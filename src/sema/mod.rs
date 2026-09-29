//! Semantic checking: names, types, `unsafe`, and proof obligations.
//!
//! The checker walks every package, resolves names across packages, checks
//! types, and discharges the proof obligations of docs/safety.md using the
//! flow-sensitive facts in [`facts`]. Its output is the typed tree in [`tree`].

mod expr;
pub mod facts;
pub mod tree;

use std::collections::{HashMap, HashSet};

use crate::ast::{self, Convention, ExprKind, Stmt, TypeExpr};
use crate::diag::Diagnostic;
use crate::load::Package;
use crate::source::{FileId, Span};
use crate::types::{Primitive, Range, Ty, primitive};

use facts::Env;
pub use tree::*;

/// Check every loaded package (dependencies first, the root package last).
/// `ptr_bits` is the target's address width.
pub fn check(packages: &[Package], ptr_bits: u32) -> (Program, Vec<Diagnostic>) {
    let mut ck = Checker {
        diags: Vec::new(),
        pkgs: Vec::new(),
        sigs: Vec::new(),
        consts: Vec::new(),
        imports: HashMap::new(),
        strings: Vec::new(),
        string_ids: HashMap::new(),
        ptr_bits,
    };
    ck.collect(packages);

    // Check every constant, used or not, so its errors are reported.
    for id in 0..ck.consts.len() {
        ck.const_value(id);
    }

    let mut funcs = Vec::new();
    for (pkg, package) in packages.iter().enumerate() {
        for file in &package.files {
            for item in &file.items {
                if let ast::Item::Fn(f) = item {
                    let id = funcs.len();
                    funcs.push(ck.function(f, id, pkg, file.id));
                }
            }
        }
    }

    let root = packages.len().saturating_sub(1);
    let main = match ck.pkgs.get(root).and_then(|p| p.items.get("main")) {
        Some(Item::Func(id)) => Some(*id),
        _ => None,
    };
    if let Some(id) = main {
        let sig = &ck.sigs[id];
        let (no_params, ret, span) = (sig.params.is_empty(), sig.ret, sig.span);
        if !no_params {
            ck.error(span, "`main` takes no parameters");
        }
        if !matches!(ret, Ty::Unit | Ty::Int(_)) {
            ck.error(span, "`main` must return nothing or an integer exit status");
        }
    }

    let program = Program {
        funcs,
        strings: ck.strings,
        main,
    };
    (program, ck.diags)
}

#[derive(Clone, Copy, Debug)]
enum Item {
    Func(FuncId),
    Const(usize),
}

struct PkgInfo {
    path: String,
    items: HashMap<String, Item>,
}

struct Sig {
    is_pub: bool,
    is_unsafe: bool,
    params: Vec<Ty>,
    ret: Ty,
    /// The function name's span.
    span: Span,
}

/// The value of a checked constant.
#[derive(Clone, Copy, Debug)]
enum ConstVal {
    /// A typed integer constant.
    Typed(Ty, i128),
    /// An untyped integer constant: like a literal, it takes its type from
    /// the context where it's used.
    Untyped(i128),
}

#[derive(Clone, Copy, Debug)]
enum ConstState {
    Unchecked,
    Checking,
    Done(ConstVal),
    Failed,
}

struct ConstInfo<'a> {
    decl: &'a ast::ConstDecl,
    pkg: usize,
    file: FileId,
    state: ConstState,
}

struct Checker<'a> {
    diags: Vec<Diagnostic>,
    pkgs: Vec<PkgInfo>,
    sigs: Vec<Sig>,
    consts: Vec<ConstInfo<'a>>,
    /// For each file: import name to package index.
    imports: HashMap<FileId, HashMap<String, usize>>,
    strings: Vec<Vec<u8>>,
    string_ids: HashMap<Vec<u8>, usize>,
    ptr_bits: u32,
}

/// Per-function (or per-constant) checking state.
struct FnCx {
    pkg: usize,
    file: FileId,
    locals: Vec<Local>,
    scopes: Vec<HashMap<String, LocalId>>,
    ret: Ty,
    loop_depth: u32,
    /// Nesting of `unsafe` blocks; an `unsafe fn` body starts at 1.
    unsafe_depth: u32,
    /// The facts known at the current point.
    env: Env,
}

impl FnCx {
    fn new(pkg: usize, file: FileId, ret: Ty, is_unsafe: bool) -> FnCx {
        FnCx {
            pkg,
            file,
            locals: Vec::new(),
            scopes: vec![HashMap::new()],
            ret,
            loop_depth: 0,
            unsafe_depth: u32::from(is_unsafe),
            env: Env::default(),
        }
    }

    fn lookup(&self, name: &str) -> Option<LocalId> {
        self.scopes.iter().rev().find_map(|s| s.get(name).copied())
    }
}

/// Names assigned anywhere in `stmts` (for forgetting facts at loop heads).
fn assigned_names(stmts: &[Stmt], out: &mut HashSet<String>) {
    for s in stmts {
        match s {
            Stmt::Assign { target, .. } => {
                if let ExprKind::Name(n) = &target.kind {
                    out.insert(n.clone());
                }
            }
            Stmt::If(i) => {
                let mut cur = Some(i);
                while let Some(i) = cur {
                    assigned_names(&i.then.stmts, out);
                    cur = match &i.otherwise {
                        Some(ast::Else::If(next)) => Some(next),
                        Some(ast::Else::Block(b)) => {
                            assigned_names(&b.stmts, out);
                            None
                        }
                        None => None,
                    };
                }
            }
            Stmt::While { body, .. } | Stmt::Loop { body, .. } | Stmt::Unsafe(body) => {
                assigned_names(&body.stmts, out);
            }
            _ => {}
        }
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

impl<'a> Checker<'a> {
    fn error(&mut self, span: Span, msg: impl Into<String>) {
        self.diags.push(Diagnostic::error(span, msg));
    }

    /// Build the package and item tables and every file's imports.
    fn collect(&mut self, packages: &'a [Package]) {
        for (pkg, package) in packages.iter().enumerate() {
            self.pkgs.push(PkgInfo {
                path: package.path.clone(),
                items: HashMap::new(),
            });
            for file in &package.files {
                let mut names = HashMap::new();
                for import in &file.imports {
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
                    if let Some(target) = packages.iter().position(|p| p.path == import.path) {
                        names.insert(name, target);
                    }
                }
                self.imports.insert(file.id, names);

                for item in &file.items {
                    let (name, entry) = match item {
                        ast::Item::Fn(f) => {
                            let sig = self.signature(f);
                            self.sigs.push(sig);
                            (&f.name, Item::Func(self.sigs.len() - 1))
                        }
                        ast::Item::Const(c) => {
                            self.consts.push(ConstInfo {
                                decl: c,
                                pkg,
                                file: file.id,
                                state: ConstState::Unchecked,
                            });
                            (&c.name, Item::Const(self.consts.len() - 1))
                        }
                    };
                    if self.pkgs[pkg].items.contains_key(&name.name) {
                        self.error(
                            name.span,
                            format!("`{}` is defined more than once", name.name),
                        );
                    }
                    self.pkgs[pkg].items.insert(name.name.clone(), entry);
                }
            }
        }
    }

    fn resolve_type(&mut self, t: &TypeExpr) -> Option<Ty> {
        match t {
            TypeExpr::Unit(_) => Some(Ty::Unit),
            TypeExpr::Ptr(inner, span) => match self.resolve_type(inner)? {
                Ty::Int(it) => Some(Ty::Ptr(it)),
                other => {
                    self.error(
                        *span,
                        format!("pointers to `{other}` are not supported by the compiler yet"),
                    );
                    None
                }
            },
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
            Some(t) => match self.resolve_type(t) {
                Some(Ty::Str) => {
                    self.error(
                        t.span(),
                        "returning a `str` is not supported by the compiler yet",
                    );
                    Ty::Unit
                }
                Some(ty) => ty,
                None => Ty::Unit,
            },
            None => Ty::Unit,
        };
        Sig {
            is_pub: f.is_pub,
            is_unsafe: f.is_unsafe,
            params,
            ret,
            span: f.name.span,
        }
    }

    /// Look up `name` in package `pkg` as seen from `cx`'s package, reporting
    /// an error if it doesn't exist or is private.
    fn package_item(&mut self, cx: &FnCx, pkg: usize, name: &str, span: Span) -> Option<Item> {
        let Some(&item) = self.pkgs[pkg].items.get(name) else {
            let path = self.pkgs[pkg].path.clone();
            self.error(span, format!("package `{path}` has no `{name}`"));
            return None;
        };
        let is_pub = match item {
            Item::Func(id) => self.sigs[id].is_pub,
            Item::Const(id) => self.consts[id].decl.is_pub,
        };
        if pkg != cx.pkg && !is_pub {
            let path = self.pkgs[pkg].path.clone();
            self.error(span, format!("`{name}` is private to package `{path}`"));
            return None;
        }
        Some(item)
    }

    /// The package an import name refers to in `cx`'s file, unless a local
    /// variable of that name hides it.
    fn imported(&self, cx: &FnCx, name: &str) -> Option<usize> {
        if cx.lookup(name).is_some() {
            return None;
        }
        self.imports
            .get(&cx.file)
            .and_then(|m| m.get(name))
            .copied()
    }

    /// Evaluate a constant (once; later calls return the cached value).
    fn const_value(&mut self, id: usize) -> Option<ConstVal> {
        match self.consts[id].state {
            ConstState::Done(v) => return Some(v),
            ConstState::Failed => return None,
            ConstState::Checking => {
                let decl = self.consts[id].decl;
                self.error(
                    decl.name.span,
                    format!("the value of `{}` depends on itself", decl.name.name),
                );
                self.consts[id].state = ConstState::Failed;
                return None;
            }
            ConstState::Unchecked => {}
        }
        self.consts[id].state = ConstState::Checking;
        let ConstInfo {
            decl, pkg, file, ..
        } = self.consts[id];
        let mut cx = FnCx::new(pkg, file, Ty::Unit, false);
        let value = match &decl.ty {
            None => match self.untyped_int(&mut cx, &decl.value) {
                Some(v) => Some(ConstVal::Untyped(v)),
                None => {
                    self.diags.push(
                        Diagnostic::error(
                            decl.value.span,
                            "an untyped constant must be an integer literal or another untyped constant",
                        )
                        .with_help(format!("give it a type, e.g. `const {}: u32 = ...`", decl.name.name)),
                    );
                    None
                }
            },
            Some(t) => {
                let ty = self.resolve_type(t);
                match ty {
                    Some(ty @ Ty::Int(_)) => self
                        .expr(&mut cx, &decl.value, Some(ty))
                        .and_then(|c| self.coerce(c, ty, decl.value.span))
                        .and_then(|c| match c.range {
                            Some(r) if r.lo == r.hi => Some(ConstVal::Typed(ty, r.lo)),
                            _ => {
                                self.error(
                                    decl.value.span,
                                    "the value of a constant must be known when compiling",
                                );
                                None
                            }
                        }),
                    Some(other) => {
                        self.error(
                            t.span(),
                            format!(
                                "constants of type `{other}` are not supported by the compiler yet"
                            ),
                        );
                        None
                    }
                    None => None,
                }
            }
        };
        self.consts[id].state = value.map_or(ConstState::Failed, ConstState::Done);
        value
    }

    fn function(&mut self, f: &ast::FnDecl, id: FuncId, pkg: usize, file: FileId) -> Func {
        let (ret, is_unsafe) = (self.sigs[id].ret, self.sigs[id].is_unsafe);
        let mut cx = FnCx::new(pkg, file, ret, is_unsafe);
        let mut params = Vec::new();
        let param_tys = self.sigs[id].params.clone();
        for (p, &ty) in f.params.iter().zip(&param_tys) {
            if cx.scopes[0].contains_key(&p.name.name) {
                self.error(
                    p.name.span,
                    format!("parameter `{}` is declared twice", p.name.name),
                );
            }
            params.push(self.declare(&mut cx, &p.name.name, ty, false));
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
            symbol: format!("{}.{}", self.pkgs[pkg].path, f.name.name),
            params,
            ret,
            locals: cx.locals,
            body,
            span: f.span,
        }
    }

    fn declare(&mut self, cx: &mut FnCx, name: &str, ty: Ty, mutable: bool) -> LocalId {
        let id = cx.locals.len();
        cx.locals.push(Local {
            name: name.to_owned(),
            ty,
            mutable,
        });
        cx.scopes
            .last_mut()
            .expect("scope")
            .insert(name.to_owned(), id);
        id
    }

    fn intern_string(&mut self, bytes: &[u8]) -> usize {
        if let Some(&id) = self.string_ids.get(bytes) {
            return id;
        }
        self.strings.push(bytes.to_vec());
        self.string_ids
            .insert(bytes.to_vec(), self.strings.len() - 1);
        self.strings.len() - 1
    }

    // --- statements ---------------------------------------------------------

    fn block(&mut self, cx: &mut FnCx, stmts: &[Stmt]) -> Vec<TStmt> {
        cx.scopes.push(HashMap::new());
        let out = stmts.iter().filter_map(|s| self.stmt(cx, s)).collect();
        cx.scopes.pop();
        out
    }

    /// A local was given a new value: record what's known about it.
    fn record_value(cx: &mut FnCx, local: LocalId, value: &expr::Checked) {
        cx.env.assign(local, value.range);
        if let Some(src) = value.term
            && src != local
        {
            // A copy of another local: equal to it.
            cx.env.apply(&[
                facts::Fact::Rel {
                    a: local,
                    b: src,
                    c: 0,
                },
                facts::Fact::Rel {
                    a: src,
                    b: local,
                    c: 0,
                },
            ]);
        }
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
                        self.declare(cx, &name.name, t, *mutable);
                    }
                    return None;
                };
                if value.ty() == Ty::Unit {
                    self.error(init.span, "this expression has no value to store");
                    return None;
                }
                let local = self.declare(cx, &name.name, value.ty(), *mutable);
                Self::record_value(cx, local, &value);
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
                Self::record_value(cx, local, &checked);
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
            Stmt::If(i) => Some(self.if_stmt(cx, i)),
            Stmt::While { cond, body, .. } => {
                self.forget_assigned(cx, &body.stmts);
                let (cond, facts) = self.condition(cx, cond);
                let entry = cx.env.clone();
                cx.env.apply(&facts.when_true);
                cx.loop_depth += 1;
                let body = self.block(cx, &body.stmts);
                cx.loop_depth -= 1;
                // The loop ends when the condition is false, unless a `break`
                // leaves it earlier.
                cx.env = entry;
                if !breaks(&body) {
                    cx.env.apply(&facts.when_false);
                }
                Some(TStmt::While(cond.unwrap_or_else(placeholder_bool), body))
            }
            Stmt::Loop { body, .. } => {
                self.forget_assigned(cx, &body.stmts);
                let entry = cx.env.clone();
                cx.loop_depth += 1;
                let body = self.block(cx, &body.stmts);
                cx.loop_depth -= 1;
                cx.env = entry;
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
            Stmt::Unsafe(block) => {
                cx.unsafe_depth += 1;
                let body = self.block(cx, &block.stmts);
                cx.unsafe_depth -= 1;
                Some(TStmt::Block(body))
            }
        }
    }

    /// At the head of a loop: forget the facts about every variable the loop
    /// body assigns, since they may change on each iteration.
    fn forget_assigned(&mut self, cx: &mut FnCx, body: &[Stmt]) {
        let mut names = HashSet::new();
        assigned_names(body, &mut names);
        for name in names {
            if let Some(local) = cx.lookup(&name) {
                cx.env.forget(local);
            }
        }
    }

    fn if_stmt(&mut self, cx: &mut FnCx, i: &ast::IfStmt) -> TStmt {
        let (cond, facts) = self.condition(cx, &i.cond);
        let before = cx.env.clone();

        cx.env.apply(&facts.when_true);
        let then = self.block(cx, &i.then.stmts);
        let then_env = std::mem::replace(&mut cx.env, before);

        cx.env.apply(&facts.when_false);
        let otherwise = match &i.otherwise {
            None => Vec::new(),
            Some(ast::Else::Block(b)) => self.block(cx, &b.stmts),
            Some(ast::Else::If(inner)) => vec![self.if_stmt(cx, inner)],
        };
        let else_env = std::mem::take(&mut cx.env);

        // Facts after the `if`: a branch that always leaves the block (with
        // `return`, `break` or `continue`) contributes nothing.
        cx.env = match (diverges(&then), diverges(&otherwise)) {
            (true, false) => else_env,
            (false, true) => then_env,
            (true, true) => Env::unreachable(),
            (false, false) => Env::join(then_env, else_env),
        };
        TStmt::If(cond.unwrap_or_else(placeholder_bool), then, otherwise)
    }

    fn condition(&mut self, cx: &mut FnCx, e: &ast::Expr) -> (Option<TExpr>, facts::CondFacts) {
        match self
            .expr(cx, e, Some(Ty::Bool))
            .and_then(|c| self.coerce(c, Ty::Bool, e.span))
        {
            Some(c) => {
                let facts = c.facts.map(|f| *f).unwrap_or_default();
                (Some(c.expr), facts)
            }
            None => (None, facts::CondFacts::default()),
        }
    }
}

/// The range of values a type's integers can hold (`None` for non-integers).
fn type_range(ty: Ty) -> Option<Range> {
    ty.as_int().map(|t| t.range())
}
