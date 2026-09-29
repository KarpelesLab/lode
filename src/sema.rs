//! Semantic checking: names, types, and proof obligations.
//!
//! The output is a typed tree ([`Program`]) that the lowering pass turns into
//! LatticeFoundry IR. Every operation in it is already known to be safe: the
//! checker rejects arithmetic, division, shifts and conversions it can't prove
//! (docs/safety.md), so lowering never needs a run-time check.
//!
//! The proof checker here is the first, simplest version of the specified
//! analysis: it knows the value ranges of literals, of immutable bindings and
//! of types. It doesn't yet narrow ranges on conditions (`if i < n`), and it
//! doesn't support refinements in signatures.

use std::collections::HashMap;

use crate::ast::{self, BinOp, Convention, ExprKind, Stmt, TypeExpr, UnOp};
use crate::diag::Diagnostic;
use crate::source::Span;
use crate::types::{IntTy, Primitive, Range, Ty, primitive};

pub type LocalId = usize;
pub type FuncId = usize;

/// A checked program: every function of the package.
#[derive(Debug)]
pub struct Program {
    pub package: String,
    pub funcs: Vec<Func>,
    /// The package's `main` function, if it has one.
    pub main: Option<FuncId>,
}

#[derive(Debug)]
pub struct Func {
    pub name: String,
    /// The linker symbol: `<package>.<name>`.
    pub symbol: String,
    pub params: Vec<LocalId>,
    pub ret: Ty,
    pub locals: Vec<Local>,
    pub body: Vec<TStmt>,
    pub span: Span,
}

#[derive(Debug)]
pub struct Local {
    pub name: String,
    pub ty: Ty,
    pub mutable: bool,
    /// For an immutable integer binding, the range its value is known to be in.
    pub range: Option<Range>,
}

#[derive(Debug)]
pub enum TStmt {
    /// Initialize a local.
    Init(LocalId, TExpr),
    Assign(LocalId, TExpr),
    Expr(TExpr),
    Return(Option<TExpr>),
    If(TExpr, Vec<TStmt>, Vec<TStmt>),
    While(TExpr, Vec<TStmt>),
    Loop(Vec<TStmt>),
    Break,
    Continue,
}

#[derive(Clone, Debug)]
pub struct TExpr {
    pub kind: TExprKind,
    pub ty: Ty,
}

#[derive(Clone, Debug)]
pub enum TExprKind {
    Int(i128),
    Bool(bool),
    Local(LocalId),
    Call(FuncId, Vec<TExpr>),
    Unary(TUnOp, Box<TExpr>),
    Binary(TBinOp, Box<TExpr>, Box<TExpr>),
    /// Short-circuit `&&`.
    And(Box<TExpr>, Box<TExpr>),
    /// Short-circuit `||`.
    Or(Box<TExpr>, Box<TExpr>),
    /// An integer conversion to `ty`, proven not to lose information.
    Convert(Box<TExpr>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TUnOp {
    /// Negation, proven not to overflow.
    Neg,
    Not,
    BitNot,
}

/// How an arithmetic operator treats a result that doesn't fit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// The checker proved the result fits.
    Proven,
    Wrap,
    Saturate,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TBinOp {
    Add(Mode),
    Sub(Mode),
    Mul(Mode),
    /// Division, with the divisor proven non-zero (and no `MIN / -1`).
    Div,
    Rem,
    BitAnd,
    BitOr,
    BitXor,
    /// Shift left, with the amount proven less than the width.
    Shl,
    /// Shift left, with the amount taken modulo the width.
    ShlWrap,
    Shr,
    Cmp(CmpOp),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// Check a parsed file. `ptr_bits` is the target's address width.
pub fn check(file: &ast::File, ptr_bits: u32) -> (Program, Vec<Diagnostic>) {
    let package = file
        .package
        .as_ref()
        .map_or_else(|| "main".to_owned(), |p| p.name.clone());
    let mut ck = Checker {
        diags: Vec::new(),
        sigs: Vec::new(),
        by_name: HashMap::new(),
        imports: HashMap::new(),
        ptr_bits,
    };

    for import in &file.imports {
        if !import.path.starts_with("std/") {
            ck.error(
                import.span,
                "importing packages outside the standard library is not supported yet",
            );
            continue;
        }
        let name = import.alias.as_ref().map_or_else(
            || {
                import
                    .path
                    .rsplit('/')
                    .next()
                    .unwrap_or_default()
                    .to_owned()
            },
            |a| a.name.clone(),
        );
        ck.imports.insert(name, import.path.clone());
    }

    // Collect every signature first, so functions can call each other in any order.
    for ast::Item::Fn(f) in &file.items {
        let sig = ck.signature(f);
        if ck.by_name.contains_key(&f.name.name) {
            ck.error(
                f.name.span,
                format!("`{}` is defined more than once", f.name.name),
            );
        }
        ck.by_name.insert(f.name.name.clone(), ck.sigs.len());
        ck.sigs.push(sig);
    }

    let mut funcs = Vec::new();
    for (id, ast::Item::Fn(f)) in file.items.iter().enumerate() {
        funcs.push(ck.function(f, id, &package));
    }

    let main = ck.by_name.get("main").copied();
    if let Some(id) = main {
        let (no_params, ret) = (ck.sigs[id].params.is_empty(), ck.sigs[id].ret);
        let span = file
            .items
            .iter()
            .map(|ast::Item::Fn(f)| f)
            .nth(id)
            .map_or_else(Span::default, |f| f.name.span);
        if !no_params {
            ck.error(span, "`main` takes no parameters");
        }
        if !matches!(ret, Ty::Unit | Ty::Int(_)) {
            ck.error(span, "`main` must return nothing or an integer exit status");
        }
    }

    (
        Program {
            package,
            funcs,
            main,
        },
        ck.diags,
    )
}

#[derive(Debug)]
struct Sig {
    params: Vec<Ty>,
    ret: Ty,
}

struct Checker {
    diags: Vec<Diagnostic>,
    sigs: Vec<Sig>,
    by_name: HashMap<String, FuncId>,
    /// Imported package name to its path.
    imports: HashMap<String, String>,
    ptr_bits: u32,
}

/// Per-function state.
struct FnCx {
    locals: Vec<Local>,
    scopes: Vec<HashMap<String, LocalId>>,
    ret: Ty,
    loop_depth: u32,
}

impl FnCx {
    fn lookup(&self, name: &str) -> Option<LocalId> {
        self.scopes.iter().rev().find_map(|s| s.get(name).copied())
    }
}

/// A checked expression plus, for integers, the range its value lies in.
struct Checked {
    expr: TExpr,
    range: Option<Range>,
}

impl Checked {
    fn new(kind: TExprKind, ty: Ty, range: Option<Range>) -> Checked {
        Checked {
            expr: TExpr { kind, ty },
            range,
        }
    }

    fn ty(&self) -> Ty {
        self.expr.ty
    }

    /// The known range, or the full range of the type.
    fn int_range(&self) -> Range {
        self.range
            .unwrap_or_else(|| self.expr.ty.as_int().map_or(Range::exact(0), IntTy::range))
    }
}

/// The value of an integer or character literal, looking through parentheses
/// and negation, or `None` if `e` isn't one.
fn literal_value(e: &ast::Expr) -> Option<i128> {
    match &e.kind {
        ExprKind::Int(v) => i128::try_from(*v).ok(),
        ExprKind::Char(c) => Some(i128::from(*c)),
        ExprKind::Paren(inner) => literal_value(inner),
        ExprKind::Unary(UnOp::Neg, inner) => literal_value(inner).map(|v| -v),
        _ => None,
    }
}

fn op_name(op: BinOp) -> &'static str {
    match op {
        BinOp::Add | BinOp::AddWrap | BinOp::AddSat => "addition",
        BinOp::Sub | BinOp::SubWrap | BinOp::SubSat => "subtraction",
        BinOp::Mul | BinOp::MulWrap | BinOp::MulSat => "multiplication",
        _ => "operation",
    }
}

impl Checker {
    fn error(&mut self, span: Span, msg: impl Into<String>) {
        self.diags.push(Diagnostic::error(span, msg));
    }

    fn resolve_type(&mut self, t: &TypeExpr) -> Option<Ty> {
        match t {
            TypeExpr::Unit(_) => Some(Ty::Unit),
            TypeExpr::Named(id) => match primitive(&id.name, self.ptr_bits) {
                Some(Primitive::Ty(ty)) => Some(ty),
                Some(Primitive::Unsupported) => {
                    self.error(
                        id.span,
                        format!(
                            "the type `{}` is not supported by the compiler yet",
                            id.name
                        ),
                    );
                    None
                }
                None => {
                    self.error(id.span, format!("unknown type `{}`", id.name));
                    None
                }
            },
        }
    }

    fn signature(&mut self, f: &ast::FnDecl) -> Sig {
        let mut params = Vec::new();
        for p in &f.params {
            if p.convention != Convention::Let {
                self.error(
                    p.name.span,
                    "`inout`, `sink` and `set` parameters are not supported by the compiler yet",
                );
            }
            params.push(self.resolve_type(&p.ty).unwrap_or(Ty::Unit));
        }
        let ret = match &f.ret {
            Some(t) => self.resolve_type(t).unwrap_or(Ty::Unit),
            None => Ty::Unit,
        };
        Sig { params, ret }
    }

    fn function(&mut self, f: &ast::FnDecl, id: FuncId, package: &str) -> Func {
        let ret = self.sigs[id].ret;
        let mut cx = FnCx {
            locals: Vec::new(),
            scopes: vec![HashMap::new()],
            ret,
            loop_depth: 0,
        };
        let mut params = Vec::new();
        let param_tys = self.sigs[id].params.clone();
        for (p, &ty) in f.params.iter().zip(&param_tys) {
            if cx.scopes[0].contains_key(&p.name.name) {
                self.error(
                    p.name.span,
                    format!("parameter `{}` is declared twice", p.name.name),
                );
            }
            let local = self.declare(&mut cx, &p.name.name, ty, false, None);
            params.push(local);
        }
        let body = self.block(&mut cx, &f.body.stmts);
        if ret != Ty::Unit && !terminates(&body) {
            self.error(
                f.name.span,
                format!(
                    "`{}` can reach the end of its body without returning a value",
                    f.name.name
                ),
            );
        }
        Func {
            name: f.name.name.clone(),
            symbol: format!("{package}.{}", f.name.name),
            params,
            ret,
            locals: cx.locals,
            body,
            span: f.span,
        }
    }

    fn declare(
        &mut self,
        cx: &mut FnCx,
        name: &str,
        ty: Ty,
        mutable: bool,
        range: Option<Range>,
    ) -> LocalId {
        let id = cx.locals.len();
        cx.locals.push(Local {
            name: name.to_owned(),
            ty,
            mutable,
            range,
        });
        cx.scopes
            .last_mut()
            .expect("scope")
            .insert(name.to_owned(), id);
        id
    }

    // --- statements ---------------------------------------------------------

    fn block(&mut self, cx: &mut FnCx, stmts: &[Stmt]) -> Vec<TStmt> {
        cx.scopes.push(HashMap::new());
        let out = stmts.iter().filter_map(|s| self.stmt(cx, s)).collect();
        cx.scopes.pop();
        out
    }

    fn stmt(&mut self, cx: &mut FnCx, stmt: &Stmt) -> Option<TStmt> {
        match stmt {
            Stmt::Let {
                mutable,
                name,
                ty,
                init,
                span,
            } => {
                let annotated = match ty {
                    Some(t) => Some(self.resolve_type(t)?),
                    None => None,
                };
                let Some(init) = init else {
                    let what = if *mutable {
                        "`var` without an initial value is"
                    } else {
                        "`let` needs an initial value; it"
                    };
                    self.error(*span, format!("{what} not supported by the compiler yet"));
                    return None;
                };
                if cx.scopes.last().expect("scope").contains_key(&name.name) {
                    self.error(
                        name.span,
                        format!("`{}` is already declared in this block", name.name),
                    );
                    return None;
                }
                let value = self.expr(cx, init, annotated);
                let value = match (value, annotated) {
                    (Some(v), Some(t)) => self.coerce(v, t, init.span),
                    (v, _) => v,
                };
                let Some(value) = value else {
                    // Keep the name declared so later uses don't report it as unknown.
                    if let Some(t) = annotated {
                        self.declare(cx, &name.name, t, *mutable, None);
                    }
                    return None;
                };
                if value.ty() == Ty::Unit {
                    self.error(init.span, "this expression has no value to store");
                    return None;
                }
                let range = if *mutable { None } else { value.range };
                let local = self.declare(cx, &name.name, value.ty(), *mutable, range);
                Some(TStmt::Init(local, value.expr))
            }
            Stmt::Assign {
                target,
                op,
                value,
                span,
            } => {
                let ExprKind::Name(name) = &target.kind else {
                    self.error(target.span, "only variables can be assigned to");
                    return None;
                };
                let Some(local) = cx.lookup(name) else {
                    self.error(target.span, format!("cannot find `{name}` in this scope"));
                    return None;
                };
                if !cx.locals[local].mutable {
                    self.diags.push(
                        Diagnostic::error(
                            target.span,
                            format!("cannot assign to `{name}`, which is immutable"),
                        )
                        .with_help(format!("declare it with `var {name}` to make it mutable")),
                    );
                    return None;
                }
                let ty = cx.locals[local].ty;
                let checked = match op {
                    None => self.expr(cx, value, Some(ty))?,
                    Some(op) => {
                        let combined = ast::Expr {
                            kind: ExprKind::Binary(
                                *op,
                                Box::new(target.clone()),
                                Box::new(value.clone()),
                            ),
                            span: *span,
                        };
                        self.expr(cx, &combined, Some(ty))?
                    }
                };
                let checked = self.coerce(checked, ty, value.span)?;
                Some(TStmt::Assign(local, checked.expr))
            }
            Stmt::Expr(e) => {
                if !matches!(e.kind, ExprKind::Call(..)) {
                    self.error(e.span, "this expression has no effect");
                    return None;
                }
                Some(TStmt::Expr(self.expr(cx, e, None)?.expr))
            }
            // A `return` that fails to check still ends control flow, so it's kept
            // (as a bare `return`) to avoid a cascade of "missing return" errors.
            // Lowering never sees it: the program has errors.
            Stmt::Return { value, span } => Some(TStmt::Return(match (value, cx.ret) {
                (None, Ty::Unit) => None,
                (None, ret) => {
                    self.error(
                        *span,
                        format!("this function must return a value of type `{ret}`"),
                    );
                    None
                }
                (Some(v), Ty::Unit) => {
                    self.error(v.span, "this function doesn't return a value");
                    None
                }
                (Some(v), ret) => self
                    .expr(cx, v, Some(ret))
                    .and_then(|checked| self.coerce(checked, ret, v.span))
                    .map(|c| c.expr),
            })),
            Stmt::If(i) => self.if_stmt(cx, i),
            Stmt::While { cond, body, .. } => {
                let cond = self.condition(cx, cond);
                cx.loop_depth += 1;
                let body = self.block(cx, &body.stmts);
                cx.loop_depth -= 1;
                Some(TStmt::While(cond.unwrap_or_else(placeholder_bool), body))
            }
            Stmt::Loop { body, .. } => {
                cx.loop_depth += 1;
                let body = self.block(cx, &body.stmts);
                cx.loop_depth -= 1;
                Some(TStmt::Loop(body))
            }
            Stmt::Break(span) | Stmt::Continue(span) => {
                if cx.loop_depth == 0 {
                    self.error(
                        *span,
                        "`break` and `continue` can only be used inside a loop",
                    );
                    return None;
                }
                Some(if matches!(stmt, Stmt::Break(_)) {
                    TStmt::Break
                } else {
                    TStmt::Continue
                })
            }
        }
    }

    fn if_stmt(&mut self, cx: &mut FnCx, i: &ast::IfStmt) -> Option<TStmt> {
        let cond = self.condition(cx, &i.cond);
        let then = self.block(cx, &i.then.stmts);
        let otherwise = match &i.otherwise {
            None => Vec::new(),
            Some(ast::Else::Block(b)) => self.block(cx, &b.stmts),
            Some(ast::Else::If(inner)) => self.if_stmt(cx, inner).into_iter().collect(),
        };
        Some(TStmt::If(
            cond.unwrap_or_else(placeholder_bool),
            then,
            otherwise,
        ))
    }

    fn condition(&mut self, cx: &mut FnCx, e: &ast::Expr) -> Option<TExpr> {
        let c = self.expr(cx, e, Some(Ty::Bool))?;
        Some(self.coerce(c, Ty::Bool, e.span)?.expr)
    }

    // --- expressions --------------------------------------------------------

    /// Check that `c` can be used where `target` is expected, inserting a
    /// lossless widening conversion if needed.
    fn coerce(&mut self, c: Checked, target: Ty, span: Span) -> Option<Checked> {
        if c.ty() == target {
            return Some(c);
        }
        if let (Ty::Int(from), Ty::Int(to)) = (c.ty(), target)
            && from.range().within(to.range())
        {
            let range = c.range;
            return Some(Checked::new(
                TExprKind::Convert(Box::new(c.expr)),
                target,
                range,
            ));
        }
        self.error(span, format!("expected `{target}`, found `{}`", c.ty()));
        None
    }

    fn expr(&mut self, cx: &mut FnCx, e: &ast::Expr, expected: Option<Ty>) -> Option<Checked> {
        if let Some(v) = literal_value(e) {
            return self.literal(v, e.span, expected);
        }
        match &e.kind {
            ExprKind::Int(_) => {
                self.error(e.span, "integer literal is too large");
                None
            }
            ExprKind::Char(_) => unreachable!("handled by literal_value"),
            ExprKind::Bool(b) => Some(Checked::new(TExprKind::Bool(*b), Ty::Bool, None)),
            ExprKind::Str(_) => {
                self.error(e.span, "strings are not supported by the compiler yet");
                None
            }
            ExprKind::Name(name) => {
                if let Some(local) = cx.lookup(name) {
                    let l = &cx.locals[local];
                    return Some(Checked::new(TExprKind::Local(local), l.ty, l.range));
                }
                let msg = if self.by_name.contains_key(name) {
                    format!("`{name}` is a function; call it with `{name}(...)`")
                } else {
                    format!("cannot find `{name}` in this scope")
                };
                self.error(e.span, msg);
                None
            }
            ExprKind::Paren(inner) => self.expr(cx, inner, expected),
            ExprKind::Unary(op, operand) => self.unary(cx, *op, operand, e.span, expected),
            ExprKind::Binary(op, lhs, rhs) => self.binary(cx, *op, lhs, rhs, e.span, expected),
            ExprKind::Call(callee, args) => self.call(cx, callee, args, e.span),
            ExprKind::Field(..) => {
                self.error(
                    e.span,
                    "fields and methods are not supported by the compiler yet",
                );
                None
            }
        }
    }

    fn literal(&mut self, v: i128, span: Span, expected: Option<Ty>) -> Option<Checked> {
        match expected {
            Some(Ty::Int(t)) => {
                if t.range().contains(v) {
                    Some(Checked::new(
                        TExprKind::Int(v),
                        Ty::Int(t),
                        Some(Range::exact(v)),
                    ))
                } else {
                    self.error(span, format!("`{v}` does not fit in `{t}` ({})", t.range()));
                    None
                }
            }
            Some(other) => {
                self.error(span, format!("expected `{other}`, found an integer"));
                None
            }
            None => {
                self.diags.push(
                    Diagnostic::error(span, "cannot tell which integer type this literal has")
                        .with_help("give it a type from context, e.g. `let x: u32 = 5`"),
                );
                None
            }
        }
    }

    fn unary(
        &mut self,
        cx: &mut FnCx,
        op: UnOp,
        operand: &ast::Expr,
        span: Span,
        expected: Option<Ty>,
    ) -> Option<Checked> {
        match op {
            UnOp::Not => {
                let c = self.expr(cx, operand, Some(Ty::Bool))?;
                let c = self.coerce(c, Ty::Bool, operand.span)?;
                Some(Checked::new(
                    TExprKind::Unary(TUnOp::Not, Box::new(c.expr)),
                    Ty::Bool,
                    None,
                ))
            }
            UnOp::BitNot => {
                let c = self.expr(cx, operand, expected)?;
                let Some(_) = c.ty().as_int() else {
                    self.error(span, format!("`~` needs an integer, found `{}`", c.ty()));
                    return None;
                };
                let ty = c.ty();
                Some(Checked::new(
                    TExprKind::Unary(TUnOp::BitNot, Box::new(c.expr)),
                    ty,
                    None,
                ))
            }
            UnOp::Neg => {
                let c = self.expr(cx, operand, expected)?;
                let Some(t) = c.ty().as_int() else {
                    self.error(span, format!("`-` needs an integer, found `{}`", c.ty()));
                    return None;
                };
                if !t.signed {
                    self.error(
                        span,
                        format!("cannot negate a value of the unsigned type `{t}`"),
                    );
                    return None;
                }
                let r = c.int_range();
                if r.lo == t.min() {
                    self.diags.push(
                        Diagnostic::error(
                            span,
                            format!("cannot prove that this negation does not overflow `{t}`"),
                        )
                        .with_help(format!(
                            "the operand can be {r}, and `-({})` doesn't fit",
                            t.min()
                        )),
                    );
                    return None;
                }
                let range = Range {
                    lo: -r.hi,
                    hi: -r.lo,
                };
                Some(Checked::new(
                    TExprKind::Unary(TUnOp::Neg, Box::new(c.expr)),
                    Ty::Int(t),
                    Some(range),
                ))
            }
        }
    }

    /// Check two operands that must share a type. An untyped literal on one
    /// side takes the other side's type; otherwise a lossless widening is
    /// applied to the narrower side.
    fn operands(
        &mut self,
        cx: &mut FnCx,
        lhs: &ast::Expr,
        rhs: &ast::Expr,
        expected: Option<Ty>,
    ) -> Option<(Checked, Checked)> {
        let (l, r) = match (literal_value(lhs).is_some(), literal_value(rhs).is_some()) {
            (true, false) => {
                let r = self.expr(cx, rhs, expected)?;
                let l = self.expr(cx, lhs, Some(r.ty()))?;
                (l, r)
            }
            (false, true) => {
                let l = self.expr(cx, lhs, expected)?;
                let r = self.expr(cx, rhs, Some(l.ty()))?;
                (l, r)
            }
            _ => {
                let l = self.expr(cx, lhs, expected);
                let r = self.expr(cx, rhs, expected);
                (l?, r?)
            }
        };
        if l.ty() == r.ty() {
            return Some((l, r));
        }
        match (l.ty(), r.ty()) {
            (Ty::Int(a), Ty::Int(b)) if a.range().within(b.range()) => {
                let t = r.ty();
                Some((self.coerce(l, t, lhs.span)?, r))
            }
            (Ty::Int(a), Ty::Int(b)) if b.range().within(a.range()) => {
                let t = l.ty();
                Some((l, self.coerce(r, t, rhs.span)?))
            }
            (a, b) => {
                self.error(
                    lhs.span.to(rhs.span),
                    format!("mismatched types: `{a}` and `{b}`"),
                );
                None
            }
        }
    }

    fn binary(
        &mut self,
        cx: &mut FnCx,
        op: BinOp,
        lhs: &ast::Expr,
        rhs: &ast::Expr,
        span: Span,
        expected: Option<Ty>,
    ) -> Option<Checked> {
        match op {
            BinOp::And | BinOp::Or => {
                let l = self
                    .expr(cx, lhs, Some(Ty::Bool))
                    .and_then(|l| self.coerce(l, Ty::Bool, lhs.span));
                let r = self
                    .expr(cx, rhs, Some(Ty::Bool))
                    .and_then(|r| self.coerce(r, Ty::Bool, rhs.span));
                let (l, r) = (Box::new(l?.expr), Box::new(r?.expr));
                let kind = if op == BinOp::And {
                    TExprKind::And(l, r)
                } else {
                    TExprKind::Or(l, r)
                };
                Some(Checked::new(kind, Ty::Bool, None))
            }
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let (l, r) = self.operands(cx, lhs, rhs, None)?;
                let ordered = !matches!(op, BinOp::Eq | BinOp::Ne);
                match l.ty() {
                    Ty::Int(_) => {}
                    Ty::Bool if !ordered => {}
                    other => {
                        self.error(
                            span,
                            format!("`{}` can't compare values of type `{other}`", op.as_str()),
                        );
                        return None;
                    }
                }
                let cmp = match op {
                    BinOp::Eq => CmpOp::Eq,
                    BinOp::Ne => CmpOp::Ne,
                    BinOp::Lt => CmpOp::Lt,
                    BinOp::Le => CmpOp::Le,
                    BinOp::Gt => CmpOp::Gt,
                    _ => CmpOp::Ge,
                };
                let kind = TExprKind::Binary(TBinOp::Cmp(cmp), Box::new(l.expr), Box::new(r.expr));
                Some(Checked::new(kind, Ty::Bool, None))
            }
            BinOp::Shl | BinOp::ShlWrap | BinOp::Shr => self.shift(cx, op, lhs, rhs, expected),
            _ => self.arith(cx, op, lhs, rhs, span, expected),
        }
    }

    fn arith(
        &mut self,
        cx: &mut FnCx,
        op: BinOp,
        lhs: &ast::Expr,
        rhs: &ast::Expr,
        span: Span,
        expected: Option<Ty>,
    ) -> Option<Checked> {
        let (l, r) = self.operands(cx, lhs, rhs, expected)?;
        let Some(t) = l.ty().as_int() else {
            self.error(
                span,
                format!("`{}` needs integers, found `{}`", op.as_str(), l.ty()),
            );
            return None;
        };
        let (a, b) = (l.int_range(), r.int_range());
        let full = t.range();

        let (top, range) = match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                let result = match op {
                    BinOp::Add => a.checked_add(b),
                    BinOp::Sub => a.checked_sub(b),
                    _ => a.checked_mul(b),
                };
                match result {
                    Some(res) if res.within(full) => {
                        let top = match op {
                            BinOp::Add => TBinOp::Add(Mode::Proven),
                            BinOp::Sub => TBinOp::Sub(Mode::Proven),
                            _ => TBinOp::Mul(Mode::Proven),
                        };
                        (top, res)
                    }
                    _ => {
                        let (wrap, sat) = match op {
                            BinOp::Add => ("+%", "+|"),
                            BinOp::Sub => ("-%", "-|"),
                            _ => ("*%", "*|"),
                        };
                        self.diags.push(
                            Diagnostic::error(
                                span,
                                format!("cannot prove that this {} does not overflow `{t}`", op_name(op)),
                            )
                            .with_help(format!("the operands can be {a} and {b}"))
                            .with_help(format!(
                                "use `{wrap}` to wrap around, `{sat}` to saturate, or check the values first"
                            )),
                        );
                        return None;
                    }
                }
            }
            BinOp::AddWrap => (TBinOp::Add(Mode::Wrap), full),
            BinOp::SubWrap => (TBinOp::Sub(Mode::Wrap), full),
            BinOp::MulWrap => (TBinOp::Mul(Mode::Wrap), full),
            BinOp::AddSat => (TBinOp::Add(Mode::Saturate), full),
            BinOp::SubSat => (TBinOp::Sub(Mode::Saturate), full),
            BinOp::MulSat => {
                self.error(
                    span,
                    "saturating multiplication is not supported by the compiler yet",
                );
                return None;
            }
            BinOp::Div | BinOp::Rem => {
                if b.contains(0) {
                    self.diags.push(
                        Diagnostic::error(rhs.span, "cannot prove that this divisor is not zero")
                            .with_help(format!("the divisor can be {b}")),
                    );
                    return None;
                }
                if t.signed && a.contains(t.min()) && b.contains(-1) {
                    self.diags.push(
                        Diagnostic::error(
                            span,
                            format!("cannot prove that this is not `{}` divided by -1", t.min()),
                        )
                        .with_help(format!(
                            "the operands can be {a} and {b}; that one result doesn't fit in `{t}`"
                        )),
                    );
                    return None;
                }
                let biggest = a.lo.abs().max(a.hi.abs());
                let range = if op == BinOp::Div {
                    if t.signed {
                        Range {
                            lo: -biggest,
                            hi: biggest,
                        }
                    } else {
                        Range { lo: 0, hi: a.hi }
                    }
                } else {
                    let m = b.lo.abs().max(b.hi.abs()) - 1;
                    if t.signed {
                        Range { lo: -m, hi: m }
                    } else {
                        Range { lo: 0, hi: m }
                    }
                };
                let top = if op == BinOp::Div {
                    TBinOp::Div
                } else {
                    TBinOp::Rem
                };
                (
                    top,
                    Range {
                        lo: range.lo.max(full.lo),
                        hi: range.hi.min(full.hi),
                    },
                )
            }
            BinOp::BitAnd => {
                let range = if a.lo >= 0 && b.lo >= 0 {
                    Range {
                        lo: 0,
                        hi: a.hi.min(b.hi),
                    }
                } else {
                    full
                };
                (TBinOp::BitAnd, range)
            }
            BinOp::BitOr => (TBinOp::BitOr, full),
            BinOp::BitXor => (TBinOp::BitXor, full),
            _ => unreachable!("not an arithmetic operator"),
        };
        let kind = TExprKind::Binary(top, Box::new(l.expr), Box::new(r.expr));
        Some(Checked::new(kind, Ty::Int(t), Some(range)))
    }

    fn shift(
        &mut self,
        cx: &mut FnCx,
        op: BinOp,
        lhs: &ast::Expr,
        rhs: &ast::Expr,
        expected: Option<Ty>,
    ) -> Option<Checked> {
        let l = self.expr(cx, lhs, expected)?;
        let Some(t) = l.ty().as_int() else {
            self.error(
                lhs.span,
                format!("`{}` needs an integer, found `{}`", op.as_str(), l.ty()),
            );
            return None;
        };
        let r = self.expr(cx, rhs, Some(l.ty()))?;
        if r.ty().as_int().is_none() {
            self.error(
                rhs.span,
                format!("the shift amount must be an integer, found `{}`", r.ty()),
            );
            return None;
        }
        let amount = r.int_range();
        if op != BinOp::ShlWrap
            && !amount.within(Range {
                lo: 0,
                hi: i128::from(t.bits) - 1,
            })
        {
            self.diags.push(
                Diagnostic::error(
                    rhs.span,
                    format!(
                        "cannot prove that this shift amount is less than {}",
                        t.bits
                    ),
                )
                .with_help(format!("the amount can be {amount}"))
                .with_help("use `<<%` to take the amount modulo the width"),
            );
            return None;
        }
        let a = l.int_range();
        let (top, range) = match op {
            BinOp::Shl => (TBinOp::Shl, t.range()),
            BinOp::ShlWrap => (TBinOp::ShlWrap, t.range()),
            _ if a.lo >= 0 => (TBinOp::Shr, Range { lo: 0, hi: a.hi }),
            _ => (TBinOp::Shr, t.range()),
        };
        let kind = TExprKind::Binary(top, Box::new(l.expr), Box::new(r.expr));
        Some(Checked::new(kind, Ty::Int(t), Some(range)))
    }

    fn call(
        &mut self,
        cx: &mut FnCx,
        callee: &ast::Expr,
        args: &[ast::Expr],
        span: Span,
    ) -> Option<Checked> {
        match &callee.kind {
            ExprKind::Name(name)
                if cx.lookup(name).is_none() && primitive(name, self.ptr_bits).is_some() =>
            {
                self.conversion(cx, name, callee.span, args, span)
            }
            ExprKind::Name(name)
                if cx.lookup(name).is_none() && self.by_name.contains_key(name) =>
            {
                let id = self.by_name[name];
                let (params, ret) = (self.sigs[id].params.clone(), self.sigs[id].ret);
                if args.len() != params.len() {
                    self.error(
                        span,
                        format!(
                            "`{name}` takes {} argument(s), but {} were given",
                            params.len(),
                            args.len()
                        ),
                    );
                    return None;
                }
                let mut targs = Vec::new();
                let mut ok = true;
                for (arg, &pty) in args.iter().zip(&params) {
                    match self
                        .expr(cx, arg, Some(pty))
                        .and_then(|c| self.coerce(c, pty, arg.span))
                    {
                        Some(c) => targs.push(c.expr),
                        None => ok = false,
                    }
                }
                ok.then(|| Checked::new(TExprKind::Call(id, targs), ret, None))
            }
            ExprKind::Field(base, member) => {
                if let ExprKind::Name(pkg) = &base.kind
                    && let Some(path) = self.imports.get(pkg)
                {
                    let msg = format!(
                        "`{pkg}.{}` is not available yet: the compiler has no standard library (`{path}`)",
                        member.name
                    );
                    self.diags.push(Diagnostic::error(callee.span, msg).with_help(
                        "I/O needs the syscall intrinsic from LatticeFoundry first (docs/backend.md)",
                    ));
                } else {
                    self.error(
                        callee.span,
                        "fields and methods are not supported by the compiler yet",
                    );
                }
                None
            }
            ExprKind::Name(name) => {
                self.error(callee.span, format!("cannot find function `{name}`"));
                None
            }
            _ => {
                self.error(callee.span, "only named functions can be called");
                None
            }
        }
    }

    /// `u8(x)` and similar: an integer conversion that must be proven lossless.
    fn conversion(
        &mut self,
        cx: &mut FnCx,
        name: &str,
        name_span: Span,
        args: &[ast::Expr],
        span: Span,
    ) -> Option<Checked> {
        let Some(Primitive::Ty(Ty::Int(to))) = primitive(name, self.ptr_bits) else {
            self.error(
                name_span,
                format!("`{name}(...)` is not a supported conversion"),
            );
            return None;
        };
        let [arg] = args else {
            self.error(span, format!("`{name}(...)` converts exactly one value"));
            return None;
        };
        let c = self.expr(cx, arg, Some(Ty::Int(to)))?;
        let Some(from) = c.ty().as_int() else {
            self.error(arg.span, format!("cannot convert `{}` to `{to}`", c.ty()));
            return None;
        };
        let r = c.int_range();
        if !r.within(to.range()) {
            self.diags.push(
                Diagnostic::error(span, format!("cannot prove that this `{from}` value fits in `{to}`"))
                    .with_help(format!("the value can be {r}, and `{to}` holds {}", to.range()))
                    .with_help("check the value first; wrapping and saturating conversions are not supported by the compiler yet"),
            );
            return None;
        }
        if from == to {
            return Some(c);
        }
        Some(Checked::new(
            TExprKind::Convert(Box::new(c.expr)),
            Ty::Int(to),
            Some(r),
        ))
    }
}

/// Stands in for a condition that failed to check, so the statement around it
/// is kept for control-flow analysis. Only used when the program has errors.
fn placeholder_bool() -> TExpr {
    TExpr {
        kind: TExprKind::Bool(false),
        ty: Ty::Bool,
    }
}

/// Whether control can't fall off the end of `stmts`.
fn terminates(stmts: &[TStmt]) -> bool {
    stmts.iter().any(|s| match s {
        TStmt::Return(_) => true,
        TStmt::If(_, then, otherwise) => terminates(then) && terminates(otherwise),
        TStmt::Loop(body) => !breaks(body),
        _ => false,
    })
}

/// Whether `stmts` contain a `break` that leaves the enclosing loop.
fn breaks(stmts: &[TStmt]) -> bool {
    stmts.iter().any(|s| match s {
        TStmt::Break => true,
        TStmt::If(_, then, otherwise) => breaks(then) || breaks(otherwise),
        _ => false,
    })
}
