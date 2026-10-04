//! Checking expressions.

use std::collections::HashMap;

use crate::ast::{self, BinOp, ExprKind, UnOp};
use crate::diag::Diagnostic;
use crate::source::Span;
use crate::types::{IntTy, Primitive, Range, Ty, primitive};

use super::facts::{self, CondFacts, Env, Linear, Side, Term};
use super::tree::*;
use super::{Checker, ConstVal, FnCx, Item, type_range};

/// A checked expression, plus what the proof checker knows about it.
pub(super) struct Checked {
    pub(super) expr: TExpr,
    /// For integers, the range its value lies in (`None`: its type's range).
    pub(super) range: Option<Range>,
    /// The term it reads, if it's (a lossless conversion of) an integer
    /// local or a view's length.
    pub(super) term: Option<Linear>,
    /// For conditions: the facts it gives when true and when false.
    pub(super) facts: Option<Box<CondFacts>>,
}

impl Checked {
    pub(super) fn new(kind: TExprKind, ty: Ty, range: Option<Range>) -> Checked {
        Checked {
            expr: TExpr { kind, ty },
            range,
            term: None,
            facts: None,
        }
    }

    pub(super) fn ty(&self) -> Ty {
        self.expr.ty
    }

    /// The known range, or the full range of the type.
    pub(super) fn int_range(&self) -> Range {
        self.range
            .or_else(|| type_range(self.expr.ty))
            .unwrap_or(Range::exact(0))
    }

    fn side(&self) -> Side {
        Side {
            term: self.term,
            range: self.int_range(),
            full: type_range(self.expr.ty).unwrap_or(Range::exact(0)),
        }
    }
}

/// Whether `e` takes its type from its context: an array literal, `none`
/// or a variant `.name`. In `xs == [1, 2, 3]` or `opt == none`, it takes
/// the other side's.
fn needs_context(e: &ast::Expr) -> bool {
    match &e.kind {
        ExprKind::ArrayLit(_) | ExprKind::ArrayRepeat(..) | ExprKind::None | ExprKind::Dot(_) => {
            true
        }
        ExprKind::Call(callee, _) => matches!(callee.kind, ExprKind::Dot(_)),
        ExprKind::Paren(inner) => needs_context(inner),
        _ => false,
    }
}

/// The name a call's callee is written with (`f`, `os.write`), for messages.
fn callee_name(callee: &ast::Expr) -> String {
    match &callee.kind {
        ExprKind::Name(n) => n.clone(),
        ExprKind::Field(base, member) => format!("{}.{}", callee_name(base), member.name),
        _ => "this function".to_owned(),
    }
}

/// The type under any optionals: `T` for `??T`. Where a `?T` is expected, a
/// literal is a `T` (made optional by [`Checker::coerce`]).
fn under_optionals(mut ty: Ty) -> Ty {
    while let Some(inner) = ty.as_optional() {
        ty = inner;
    }
    ty
}

/// Whether a value of type `from` can be used where `to` is expected (see
/// [`Checker::coerce`]).
pub(super) fn coercible(from: Ty, to: Ty) -> bool {
    if from == to {
        return true;
    }
    match (from, to) {
        (Ty::Int(a), Ty::Int(b)) => a.range().within(b.range()),
        _ if from
            .as_array()
            .is_some_and(|(e, _)| Some(e) == to.as_slice()) =>
        {
            true
        }
        _ => to.as_optional().is_some_and(|inner| coercible(from, inner)),
    }
}

/// The term for a place made of fields only, like `p.a.b`, whatever its
/// type: for a struct, the first number of its fields.
pub(super) fn place_term(place: &TExpr) -> Option<Term> {
    match &place.kind {
        TExprKind::Field(base, i) => field_term(base, *i as usize),
        _ => None,
    }
}

/// The term for field `i` of `base`, when `base` is a struct local or a
/// struct field of one, reached through fields only.
fn field_term(base: &TExpr, i: usize) -> Option<Term> {
    let (local, offset) = match &base.kind {
        TExprKind::Local(l) => (*l, 0),
        TExprKind::Field(inner, j) => match field_term(inner, *j as usize)? {
            Term::Field(l, off) => (l, off),
            _ => return None,
        },
        _ => return None,
    };
    let def = base.ty.as_struct()?;
    let before: u32 = def.fields[..i].iter().map(|f| flat_size(f.ty)).sum();
    Some(Term::Field(local, offset + before))
}

/// How many numbers [`field_term`] gives a value of type `ty`: one for
/// anything but a struct, the sum of its fields' for a struct.
pub(super) fn flat_size(ty: Ty) -> u32 {
    match ty.as_struct() {
        Some(def) => def.fields.iter().map(|f| flat_size(f.ty)).sum(),
        None => 1,
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

/// The name of the `syscall` intrinsic (docs/safety.md).
const SYSCALL: &str = "syscall";

/// The most arguments `syscall` takes after the number (the Linux ABI's six).
const SYSCALL_MAX_ARGS: usize = 6;

impl Checker<'_> {
    /// Require an `unsafe` context for `what`.
    fn require_unsafe(&mut self, cx: &FnCx, span: Span, what: &str) {
        if cx.unsafe_depth == 0 {
            self.diags.push(
                Diagnostic::error(span, format!("{what} is unsafe"))
                    .with_help("put it in an `unsafe { ... }` block, or in an `unsafe fn`"),
            );
        }
    }

    /// The value of an expression that is an untyped integer: a literal, a
    /// negated or parenthesized one, or an untyped constant. Such values take
    /// their type from the context where they're used.
    pub(super) fn untyped_int(&mut self, cx: &mut FnCx, e: &ast::Expr) -> Option<i128> {
        match &e.kind {
            ExprKind::Int(v) => i128::try_from(*v).ok(),
            ExprKind::Char(c) => Some(i128::from(*c)),
            ExprKind::Paren(inner) => self.untyped_int(cx, inner),
            ExprKind::Unary(UnOp::Neg, inner) => self.untyped_int(cx, inner).map(|v| -v),
            ExprKind::Name(name) if cx.lookup(name).is_none() => {
                match self.pkgs[cx.pkg].items.get(name) {
                    Some(&Item::Const(id)) => match self.const_value(id)? {
                        ConstVal::Untyped(v) => Some(v),
                        ConstVal::Typed(..) => None,
                    },
                    _ => None,
                }
            }
            ExprKind::Field(base, member) => {
                let ExprKind::Name(pkg_name) = &base.kind else {
                    return None;
                };
                let pkg = self.imported(cx, pkg_name)?;
                match self.pkgs[pkg].items.get(&member.name) {
                    Some(&Item::Const(id)) if pkg == cx.pkg || self.consts[id].decl.is_pub => {
                        match self.const_value(id)? {
                            ConstVal::Untyped(v) => Some(v),
                            ConstVal::Typed(..) => None,
                        }
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Check that `c` can be used where `target` is expected, inserting a
    /// lossless widening conversion if needed, or making a value of `T` an
    /// optional `?T` that holds it.
    pub(super) fn coerce(&mut self, c: Checked, target: Ty, span: Span) -> Option<Checked> {
        if c.ty() == target {
            return Some(c);
        }
        if let Some(inner) = target.as_optional()
            && coercible(c.ty(), inner)
        {
            let value = self.coerce(c, inner, span)?;
            return Some(Checked::new(
                TExprKind::Variant(1, vec![value.expr]),
                target,
                None,
            ));
        }
        if let (Ty::Int(from), Ty::Int(to)) = (c.ty(), target)
            && from.range().within(to.range())
        {
            // The value keeps its range: with none known, its own type's,
            // not the wider target's.
            let (range, term) = (Some(c.int_range()), c.term);
            let mut out = Checked::new(TExprKind::Convert(Box::new(c.expr)), target, range);
            out.term = term;
            return Some(out);
        }
        // An array where a slice of its element type is expected: a view of
        // the whole array.
        if let (Some((from, _)), Some(to)) = (c.ty().as_array(), target.as_slice())
            && from == to
        {
            return Some(Checked::new(
                TExprKind::ToSlice(Box::new(c.expr)),
                target,
                None,
            ));
        }
        self.error(span, format!("expected `{target}`, found `{}`", c.ty()));
        None
    }

    pub(super) fn expr(
        &mut self,
        cx: &mut FnCx,
        e: &ast::Expr,
        expected: Option<Ty>,
    ) -> Option<Checked> {
        if let Some(v) = self.untyped_int(cx, e) {
            return self.literal(v, e.span, expected.map(under_optionals));
        }
        match &e.kind {
            ExprKind::Int(_) => {
                self.error(e.span, "integer literal is too large");
                None
            }
            ExprKind::Char(_) => unreachable!("handled by untyped_int"),
            ExprKind::Bool(b) => Some(Checked::new(TExprKind::Bool(*b), Ty::Bool, None)),
            ExprKind::Str(bytes) => {
                if std::str::from_utf8(bytes).is_err() {
                    self.error(e.span, "a `str` literal must be valid UTF-8");
                    return None;
                }
                let id = self.intern_string(bytes);
                Some(Checked::new(TExprKind::Str(id), Ty::Str, None))
            }
            ExprKind::Name(name) => self.name(cx, name, e.span),
            ExprKind::Paren(inner) => self.expr(cx, inner, expected),
            ExprKind::Unary(op, operand) => self.unary(cx, *op, operand, e.span, expected),
            ExprKind::Binary(op, lhs, rhs) => self.binary(cx, *op, lhs, rhs, e.span, expected),
            ExprKind::Call(callee, args) => match &callee.kind {
                ExprKind::Dot(name) => self.dot_variant(name, Some(args), e.span, expected, cx),
                _ => self.call(cx, callee, args, e.span, false),
            },
            ExprKind::Dot(name) => self.dot_variant(name, None, e.span, expected, cx),
            ExprKind::Try(call) => self.try_call(cx, call, e.span),
            ExprKind::Catch {
                value,
                binding,
                handler,
            } => self.catch(cx, value, binding.as_ref(), handler, true),
            ExprKind::Throw(_) => {
                self.diags.push(
                    Diagnostic::error(e.span, "`throw` is a statement").with_help(
                        "in an expression, it can only follow `??`: `opt ?? throw .name`",
                    ),
                );
                None
            }
            ExprKind::Field(base, member) => self.field(cx, base, member, e.span),
            ExprKind::ArrayLit(elems) => {
                self.array_literal(cx, elems, e.span, expected.map(under_optionals))
            }
            ExprKind::ArrayRepeat(value, count) => {
                self.array_repeat(cx, value, count, e.span, expected.map(under_optionals))
            }
            ExprKind::Index(base, index) => self.index(cx, base, index),
            ExprKind::StructLit(ty, fields) => self.struct_literal(cx, ty, fields, e.span),
            ExprKind::None => match expected {
                Some(t @ Ty::Optional(_)) => {
                    Some(Checked::new(TExprKind::Variant(0, Vec::new()), t, None))
                }
                Some(t) => {
                    self.error(e.span, format!("expected `{t}`, found `none`"));
                    None
                }
                None => {
                    self.diags.push(
                        Diagnostic::error(
                            e.span,
                            "cannot tell which optional type this `none` has",
                        )
                        .with_help("give it a type from context, e.g. `let x: ?u32 = none`"),
                    );
                    None
                }
            },
        }
    }

    /// The enum (or struct) type an expression names, as in `Shape.circle`
    /// or `geo.Shape.circle`: `None` if it doesn't name a type, `Some(None)`
    /// if it names one it can't use (the error is reported).
    fn type_path(&mut self, cx: &FnCx, e: &ast::Expr) -> Option<Option<Ty>> {
        match &e.kind {
            ExprKind::Name(name) if cx.lookup(name).is_none() => {
                match self.pkgs[cx.pkg].items.get(name) {
                    Some(&Item::Type(ty)) => Some(Some(ty)),
                    _ => None,
                }
            }
            ExprKind::Field(base, member) => {
                let ExprKind::Name(pkg_name) = &base.kind else {
                    return None;
                };
                let pkg = self.imported(cx, pkg_name)?;
                match self.pkgs[pkg].items.get(&member.name) {
                    Some(Item::Type(_)) => {
                        match self.package_item(cx, pkg, &member.name, member.span) {
                            Some(Item::Type(ty)) => Some(Some(ty)),
                            _ => Some(None),
                        }
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// `E.name` (`args` is `None`) or `E.name(a, b)`: a value of the enum
    /// `ty`, with its payload fields given in order.
    fn enum_variant(
        &mut self,
        cx: &mut FnCx,
        ty: Ty,
        member: &ast::Ident,
        args: Option<&[ast::Expr]>,
        span: Span,
    ) -> Option<Checked> {
        let Some(def) = ty.as_enum() else {
            self.error(
                member.span,
                format!("`{ty}` is a struct; it has no variants"),
            );
            return None;
        };
        let name = &member.name;
        let Some((i, variant)) = def.variant(name) else {
            self.error(member.span, format!("`{ty}` has no variant `{name}`"));
            return None;
        };
        let fields = &variant.fields;
        let args = match (args, fields.is_empty()) {
            (None, true) => &[][..],
            (None, false) => {
                self.error(
                    span,
                    format!("`{ty}.{name}` has a payload: give it as `{ty}.{name}(...)`"),
                );
                return None;
            }
            (Some(_), true) => {
                self.error(
                    span,
                    format!("`{ty}.{name}` has no payload, so it's written without parentheses"),
                );
                return None;
            }
            (Some(args), false) => args,
        };
        if args.len() != fields.len() {
            self.error(
                span,
                format!(
                    "`{ty}.{name}` has {} payload field(s), but {} value(s) were given",
                    fields.len(),
                    args.len()
                ),
            );
            return None;
        }
        let mut values = Vec::new();
        let mut ok = true;
        for (arg, f) in args.iter().zip(fields) {
            match self
                .expr(cx, arg, Some(f.ty))
                .and_then(|c| self.coerce(c, f.ty, arg.span))
            {
                Some(c) => values.push(c.expr),
                None => ok = false,
            }
        }
        ok.then(|| Checked::new(TExprKind::Variant(i as u32, values), ty, None))
    }

    /// `.name` (`args` is `None`) or `.name(a, b)`: a variant of the enum
    /// the context expects (or of the one in the optional it expects).
    fn dot_variant(
        &mut self,
        name: &ast::Ident,
        args: Option<&[ast::Expr]>,
        span: Span,
        expected: Option<Ty>,
        cx: &mut FnCx,
    ) -> Option<Checked> {
        match expected.map(under_optionals) {
            Some(ty @ Ty::Enum(_)) => self.enum_variant(cx, ty, name, args, span),
            other => {
                let found = match other {
                    Some(t) => format!(", and `{t}` is not an enum"),
                    None => String::new(),
                };
                self.diags.push(
                    Diagnostic::error(
                        span,
                        format!(
                            "cannot tell which enum `.{}` is a variant of{found}",
                            name.name
                        ),
                    )
                    .with_help(format!("name the enum: `E.{}`", name.name)),
                );
                None
            }
        }
    }

    /// The call `e` (in parentheses or not) to a function that throws, for
    /// `what` (`try` or `catch`): its result, of a result type.
    fn throwing_call(&mut self, cx: &mut FnCx, e: &ast::Expr, what: &str) -> Option<Checked> {
        let mut inner = e;
        while let ExprKind::Paren(x) = &inner.kind {
            inner = x;
        }
        let ExprKind::Call(callee, args) = &inner.kind else {
            self.diags.push(
                Diagnostic::error(
                    e.span,
                    format!("`{what}` needs a call to a function that throws"),
                )
                .with_help("only a call can fail with an error"),
            );
            return None;
        };
        let c = self.call(cx, callee, args, inner.span, true)?;
        if c.ty().as_result().is_none() {
            self.diags.push(
                Diagnostic::error(
                    e.span,
                    format!(
                        "`{}` doesn't throw, so it needs no `{what}`",
                        callee_name(callee)
                    ),
                )
                .with_help(
                    "`try` and `catch` handle the errors of functions declared with `throws(E)`",
                ),
            );
            return None;
        }
        Some(c)
    }

    /// `try call`: the call's value, or its error passed on to the caller.
    fn try_call(&mut self, cx: &mut FnCx, call: &ast::Expr, span: Span) -> Option<Checked> {
        self.check_not_in_defer(cx, span, "`try`")?;
        let c = self.throwing_call(cx, call, "try")?;
        let (value, err) = c.ty().as_result().expect("a result");
        match cx.throws {
            None => {
                self.diags.push(
                    Diagnostic::error(span, "`try` can only be used in a function that throws")
                        .with_help(format!(
                            "handle the error here with `catch` or `match`, or declare `throws({err})`"
                        )),
                );
                return None;
            }
            Some(own) if own != err => {
                self.diags.push(
                    Diagnostic::error(
                        span,
                        format!(
                            "`try` can't pass on an error of type `{err}` from a function that throws `{own}`"
                        ),
                    )
                    .with_help(format!(
                        "convert it: `... catch e {{ throw .name(...) }}` with a variant of `{own}`"
                    )),
                );
                return None;
            }
            Some(_) => {}
        }
        Some(Checked::new(TExprKind::Try(Box::new(c.expr)), value, None))
    }

    /// `call catch e { ... }`, `call catch _ { ... }` or `call catch value`:
    /// the call's value, or else the handler's. When the value is used
    /// (`used`) and isn't `()`, a block must leave. The facts after it are
    /// those of the call joined with those at the end of a block that
    /// doesn't leave, as after an `if`.
    pub(super) fn catch(
        &mut self,
        cx: &mut FnCx,
        value: &ast::Expr,
        binding: Option<&ast::Ident>,
        handler: &ast::CatchHandler,
        used: bool,
    ) -> Option<Checked> {
        let c = self.throwing_call(cx, value, "catch")?;
        let (ty, err) = c.ty().as_result().expect("a result");
        let entry = cx.env.clone();
        let (local, handler) = match handler {
            ast::CatchHandler::Value(v) => {
                let d = self.expr(cx, v, Some(ty));
                let d = self.coerce(d?, ty, v.span)?;
                cx.env = Env::join(entry, std::mem::take(&mut cx.env));
                (None, Handler::Value(Box::new(d.expr)))
            }
            ast::CatchHandler::Block(b) => {
                cx.scopes.push(HashMap::new());
                let local = binding.map(|name| {
                    let id = self.declare(cx, &name.name, err, false);
                    cx.env.assign(id, None);
                    id
                });
                let body = self.block(cx, &b.stmts);
                cx.scopes.pop();
                let leaves = diverges(&body);
                if used && ty != Ty::Unit && !leaves {
                    self.diags.push(
                        Diagnostic::error(
                            b.span,
                            format!(
                                "this `catch` block must leave, since the call's value (a `{ty}`) is used"
                            ),
                        )
                        .with_help("end it with `return`, `throw`, `break` or `continue`")
                        .with_help("or give a value to use instead: `catch 0`"),
                    );
                    // The value is kept, so checking goes on without more
                    // errors about it.
                }
                let end = std::mem::take(&mut cx.env);
                cx.env = Checker::join_branches(vec![(entry, false), (end, leaves)]);
                (local, Handler::Block(body))
            }
        };
        Some(Checked::new(
            TExprKind::Catch {
                call: Box::new(c.expr),
                binding: local,
                handler,
            },
            ty,
            None,
        ))
    }

    /// The error `value` of `throw value`, of the function's error type.
    pub(super) fn throw(&mut self, cx: &mut FnCx, value: &ast::Expr, span: Span) -> Option<TExpr> {
        self.check_not_in_defer(cx, span, "`throw`")?;
        let Some(err) = cx.throws else {
            self.diags.push(
                Diagnostic::error(span, "`throw` can only be used in a function that throws")
                    .with_help("declare the error type: `fn name(...) throws(E)`"),
            );
            return None;
        };
        let c = self.expr(cx, value, Some(err))?;
        Some(self.coerce(c, err, value.span)?.expr)
    }

    /// `E(x)` for a C-style enum `E`: the variant whose value is the integer
    /// `x`, as a `?E` that's `none` if there's no such variant.
    fn enum_from(
        &mut self,
        cx: &mut FnCx,
        ty: Ty,
        args: &[ast::Expr],
        span: Span,
    ) -> Option<Checked> {
        let def = ty.as_enum().expect("an enum");
        if !def.explicit {
            self.diags.push(
                Diagnostic::error(
                    span,
                    format!(
                        "`{ty}(...)` converts an integer, but the variants of `{ty}` have no values"
                    ),
                )
                .with_help(format!(
                    "build a value with a variant, like `{ty}.{}`",
                    def.variants.first().map_or("name", |v| v.name.as_str())
                )),
            );
            return None;
        }
        let [arg] = args else {
            self.error(span, format!("`{ty}(...)` converts exactly one value"));
            return None;
        };
        let c = self.expr(cx, arg, Some(Ty::Int(def.tag)))?;
        if c.ty().as_int().is_none() {
            self.error(arg.span, format!("cannot convert `{}` to `{ty}`", c.ty()));
            return None;
        }
        Some(Checked::new(
            TExprKind::EnumFrom(Box::new(c.expr)),
            Ty::optional(ty),
            None,
        ))
    }

    /// `T{name: value, ...}`: every field exactly once, in any order.
    fn struct_literal(
        &mut self,
        cx: &mut FnCx,
        ty: &ast::TypeExpr,
        inits: &[ast::FieldInit],
        span: Span,
    ) -> Option<Checked> {
        let sty = self.resolve_type(cx, ty)?;
        let Some(def) = sty.as_struct() else {
            self.error(ty.span(), format!("`{sty}` is not a struct"));
            return None;
        };
        let mut given = vec![false; def.fields.len()];
        let mut out = Vec::new();
        let mut ok = true;
        for init in inits {
            let name = &init.name.name;
            let Some((i, fty)) = def.field(name) else {
                self.error(init.name.span, format!("`{sty}` has no field `{name}`"));
                ok = false;
                continue;
            };
            if given[i] {
                self.error(
                    init.name.span,
                    format!("the field `{name}` is given more than once"),
                );
                ok = false;
                continue;
            }
            given[i] = true;
            match self
                .expr(cx, &init.value, Some(fty))
                .and_then(|c| self.coerce(c, fty, init.value.span))
            {
                Some(c) => out.push((i as u32, c.expr)),
                None => ok = false,
            }
        }
        let missing: Vec<String> = def
            .fields
            .iter()
            .zip(&given)
            .filter(|&(_, &g)| !g)
            .map(|(f, _)| format!("`{}`", f.name))
            .collect();
        if !missing.is_empty() {
            let s = if missing.len() == 1 { "" } else { "s" };
            self.diags.push(
                Diagnostic::error(
                    span,
                    format!("missing field{s} {} in this `{sty}`", missing.join(", ")),
                )
                .with_help("every field must be given a value; there are no defaults"),
            );
            ok = false;
        }
        ok.then(|| Checked::new(TExprKind::StructLit(out), sty, None))
    }

    /// The element type and length (`None` for a slice) that an array literal
    /// is expected to have, from its context.
    fn expected_array(expected: Option<Ty>) -> (Option<Ty>, Option<u64>) {
        match expected {
            Some(t) => match (t.as_array(), t.as_slice()) {
                (Some((elem, n)), _) => (Some(elem), Some(n)),
                (_, Some(elem)) => (Some(elem), None),
                _ => (None, None),
            },
            None => (None, None),
        }
    }

    /// Report an array literal whose length doesn't match the expected type.
    fn check_literal_len(
        &mut self,
        found: u64,
        want: Option<u64>,
        expected: Option<Ty>,
        span: Span,
    ) -> Option<()> {
        match (want, expected) {
            (Some(n), Some(t)) if n != found => {
                self.error(
                    span,
                    format!("expected `{t}`, found an array of {found} element(s)"),
                );
                None
            }
            _ => Some(()),
        }
    }

    /// `[a, b, c]`. The element type comes from the context, or else from the
    /// first element that has a type of its own.
    fn array_literal(
        &mut self,
        cx: &mut FnCx,
        elems: &[ast::Expr],
        span: Span,
        expected: Option<Ty>,
    ) -> Option<Checked> {
        let (want_elem, want_len) = Self::expected_array(expected);
        let n = elems.len() as u64;
        let mut checked: Vec<Option<Checked>> = elems.iter().map(|_| None).collect();
        let elem = match want_elem {
            Some(t) => t,
            None => {
                let typed = elems.iter().position(|e| self.untyped_int(cx, e).is_none());
                let Some(k) = typed else {
                    self.diags.push(
                        Diagnostic::error(span, "cannot tell the element type of this array")
                            .with_help(format!(
                                "give it a type from context, e.g. `let a: [{n}]u32 = ...`"
                            )),
                    );
                    return None;
                };
                let first = self.expr(cx, &elems[k], None)?;
                let ty = first.ty();
                checked[k] = Some(first);
                ty
            }
        };
        self.check_elem(elem, "arrays", span)?;
        self.check_literal_len(n, want_len, expected, span)?;
        let mut ok = true;
        let mut out = Vec::new();
        for (e, done) in elems.iter().zip(checked) {
            let c = match done {
                Some(c) => Some(c),
                None => self.expr(cx, e, Some(elem)),
            };
            match c.and_then(|c| self.coerce(c, elem, e.span)) {
                Some(c) => out.push(c.expr),
                None => ok = false,
            }
        }
        ok.then(|| Checked::new(TExprKind::ArrayLit(out), Ty::array(elem, n), None))
    }

    /// `[value; count]`.
    fn array_repeat(
        &mut self,
        cx: &mut FnCx,
        value: &ast::Expr,
        count: &ast::Expr,
        span: Span,
        expected: Option<Ty>,
    ) -> Option<Checked> {
        let (want_elem, want_len) = Self::expected_array(expected);
        let n = self.const_count(cx, count);
        let v = self.expr(cx, value, want_elem);
        let (n, v) = (n?, v?);
        let v = match want_elem {
            Some(t) => self.coerce(v, t, value.span)?,
            None => v,
        };
        let elem = v.ty();
        self.check_elem(elem, "arrays", value.span)?;
        self.check_literal_len(n, want_len, expected, span)?;
        Some(Checked::new(
            TExprKind::ArrayRepeat(Box::new(v.expr), n),
            Ty::array(elem, n),
            None,
        ))
    }

    /// The length of a view (a slice or `str`): a term when the view is a
    /// local, so conditions like `i < xs.len` relate to it.
    pub(super) fn view_len(&self, cx: &FnCx, view: TExpr) -> Checked {
        // A length is at most the largest `isize`: no object is bigger.
        let any_len = Range {
            lo: 0,
            hi: i128::from(i64::MAX),
        };
        let term = match view.kind {
            TExprKind::Local(l) => Some(Term::Len(l)),
            _ => None,
        };
        let range = term
            .and_then(|t| cx.env.range(t))
            .and_then(|r| r.intersect(any_len))
            .unwrap_or(any_len);
        let mut c = Checked::new(
            TExprKind::ViewLen(Box::new(view)),
            self.usize_ty(),
            Some(range),
        );
        c.term = term.map(Linear::of);
        c
    }

    /// `base[index]`, which must be proven in bounds: `0 <= index < base.len`.
    fn index(&mut self, cx: &mut FnCx, base: &ast::Expr, index: &ast::Expr) -> Option<Checked> {
        let b = self.expr(cx, base, None);
        // Untyped indexes are `usize`; any integer type is accepted.
        let usize_ty = self.usize_ty();
        let i = self.expr(cx, index, Some(usize_ty));
        let (b, i) = (b?, i?);
        let elem = match b.ty() {
            Ty::Array(_) | Ty::Slice(_) => b.ty().elem().expect("array or slice"),
            Ty::Str => {
                self.error(
                    base.span,
                    "indexing a `str` is not supported by the compiler yet",
                );
                return None;
            }
            other => {
                self.error(base.span, format!("`{other}` cannot be indexed"));
                return None;
            }
        };
        if i.ty().as_int().is_none() {
            self.error(
                index.span,
                format!("an index must be an integer, found `{}`", i.ty()),
            );
            return None;
        }

        let r = i.int_range();
        let help_check = match (&index.kind, &base.kind) {
            (ExprKind::Name(i), ExprKind::Name(xs)) if !i.starts_with('$') => {
                format!("check it first (`if {i} < {xs}.len`), or loop with `for`")
            }
            _ => "check it against `.len` first, or loop with `for`".to_owned(),
        };
        if r.lo < 0 {
            self.diags.push(
                Diagnostic::error(index.span, "cannot prove that this index is not negative")
                    .with_help(format!("the index can be {r}"))
                    .with_help("check it first, or use an unsigned index"),
            );
            return None;
        }
        // `the length is 4`, `the length can be 1..=10`, ...
        let (proven, len_desc) = match b.ty().as_array() {
            Some((_, n)) => (r.hi < i128::from(n), format!("the length is {n}")),
            None => {
                let len = self.view_len(cx, b.expr.clone());
                let lr = len.int_range();
                let by_range = r.hi < lr.lo;
                let by_rel = match (i.term, len.term) {
                    (Some(it), Some(lt)) => cx.env.diff_bound(it, lt).is_some_and(|c| c <= -1),
                    _ => false,
                };
                let desc = if lr.lo == lr.hi {
                    format!("the length is {lr}")
                } else if lr.lo == 0 && lr.hi == i128::from(i64::MAX) {
                    "nothing is known about the length".to_owned()
                } else {
                    format!("the length can be {lr}")
                };
                (by_range || by_rel, desc)
            }
        };
        if !proven {
            let what = if r.lo == r.hi { "is" } else { "can be" };
            self.diags.push(
                Diagnostic::error(
                    index.span,
                    "cannot prove that this index is less than the length",
                )
                .with_help(format!("the index {what} {r}, and {len_desc}"))
                .with_help(help_check),
            );
            return None;
        }
        Some(Checked::new(
            TExprKind::Index(Box::new(b.expr), Box::new(i.expr)),
            elem,
            None,
        ))
    }

    fn name(&mut self, cx: &mut FnCx, name: &str, span: Span) -> Option<Checked> {
        if let Some(local) = cx.lookup(name) {
            let ty = cx.locals[local].ty;
            let term = Term::Local(local);
            let mut c = Checked::new(TExprKind::Local(local), ty, cx.env.range(term));
            c.term = type_range(ty).map(|_| Linear::of(term));
            return Some(c);
        }
        if let Some(&item) = self.pkgs[cx.pkg].items.get(name) {
            return self.item_value(item, name, span);
        }
        let msg = if self.imported(cx, name).is_some() {
            format!("`{name}` is a package; use one of its members, like `{name}.something`")
        } else {
            format!("cannot find `{name}` in this scope")
        };
        let mut d = Diagnostic::error(span, msg);
        if let Some(help) = self.import_help(cx, name) {
            d = d.with_help(help);
        }
        self.diags.push(d);
        None
    }

    /// For `name.member` where `name` is neither a local, a package-level
    /// item nor an imported package: report it (with the import to add, if
    /// there's a standard package of that name), and return true.
    fn unknown_receiver(&mut self, cx: &FnCx, base: &ast::Expr) -> bool {
        let ExprKind::Name(name) = &base.kind else {
            return false;
        };
        if cx.lookup(name).is_some()
            || self.pkgs[cx.pkg].items.contains_key(name)
            || self.imported(cx, name).is_some()
        {
            return false;
        }
        let mut d = Diagnostic::error(base.span, format!("unknown package or variable `{name}`"));
        if let Some(help) = self.import_help(cx, name) {
            d = d.with_help(help);
        }
        self.diags.push(d);
        true
    }

    /// The help for a name that isn't imported but is a standard package:
    /// the import to add.
    fn import_help(&self, cx: &FnCx, name: &str) -> Option<String> {
        if cx.lookup(name).is_some() || self.imported(cx, name).is_some() || name.is_empty() {
            return None;
        }
        let path = format!("std/{name}");
        let loaded = self.pkgs.iter().any(|p| p.path == path);
        let valid = name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
        (loaded || (valid && crate::std_root().join(name).is_dir()))
            .then(|| format!("add `import \"{path}\"`"))
    }

    /// A package-level item used as a value.
    fn item_value(&mut self, item: Item, name: &str, span: Span) -> Option<Checked> {
        match item {
            Item::Const(id) => match self.const_value(id)? {
                ConstVal::Typed(ty, v) => {
                    Some(Checked::new(TExprKind::Int(v), ty, Some(Range::exact(v))))
                }
                ConstVal::Untyped(_) => unreachable!("handled by untyped_int"),
            },
            Item::Func(_) => {
                self.error(
                    span,
                    format!("`{name}` is a function; call it with `{name}(...)`"),
                );
                None
            }
            Item::Type(ty) => {
                match ty.as_enum() {
                    Some(def) => self.error(
                        span,
                        format!(
                            "`{name}` is a type; use one of its variants, like `{name}.{}`",
                            def.variants.first().map_or("name", |v| v.name.as_str())
                        ),
                    ),
                    None => self.error(
                        span,
                        format!("`{name}` is a type; build a value with `{name}{{...}}`"),
                    ),
                }
                None
            }
        }
    }

    fn field(
        &mut self,
        cx: &mut FnCx,
        base: &ast::Expr,
        member: &ast::Ident,
        span: Span,
    ) -> Option<Checked> {
        if let Some(ty) = self.type_path(cx, base) {
            return self.enum_variant(cx, ty?, member, None, span);
        }
        if let ExprKind::Name(pkg_name) = &base.kind
            && let Some(pkg) = self.imported(cx, pkg_name)
        {
            let item = self.package_item(cx, pkg, &member.name, member.span)?;
            return self.item_value(item, &format!("{pkg_name}.{}", member.name), span);
        }
        if self.unknown_receiver(cx, base) {
            return None;
        }
        let b = self.expr(cx, base, None)?;
        match (b.ty(), member.name.as_str()) {
            (Ty::Str | Ty::Slice(_), "len") => Some(self.view_len(cx, b.expr)),
            (Ty::Array(_), "len") => {
                let (_, n) = b.ty().as_array().expect("an array");
                let n = i128::from(n);
                let usize_ty = self.usize_ty();
                Some(Checked::new(
                    TExprKind::ArrayLen(Box::new(b.expr)),
                    usize_ty,
                    Some(Range::exact(n)),
                ))
            }
            (Ty::Struct(_), name) => {
                let def = b.ty().as_struct().expect("a struct");
                let Some((i, fty)) = def.field(name) else {
                    self.error(member.span, format!("`{}` has no field `{name}`", b.ty()));
                    return None;
                };
                // An integer field of a local, through fields only, is a term.
                let term = match type_range(fty) {
                    Some(_) => field_term(&b.expr, i),
                    None => None,
                };
                let mut c = Checked::new(
                    TExprKind::Field(Box::new(b.expr), i as u32),
                    fty,
                    term.and_then(|t| cx.env.range(t)),
                );
                c.term = term.map(Linear::of);
                Some(c)
            }
            (Ty::Str, "ptr") => {
                self.require_unsafe(cx, span, "taking a string's raw pointer");
                Some(Checked::new(
                    TExprKind::StrPtr(Box::new(b.expr)),
                    Ty::Ptr(IntTy::new(false, 8)),
                    None,
                ))
            }
            // The first element of an array or slice of integers. An array is
            // viewed in place, as when it's passed where a slice is expected.
            (ty @ (Ty::Array(_) | Ty::Slice(_)), "ptr")
                if matches!(ty.elem(), Some(Ty::Int(_))) =>
            {
                let Some(Ty::Int(elem)) = ty.elem() else {
                    unreachable!("an integer element")
                };
                self.require_unsafe(cx, span, "taking an array's or slice's raw pointer");
                let view = match ty {
                    Ty::Array(_) => TExpr {
                        kind: TExprKind::ToSlice(Box::new(b.expr)),
                        ty: Ty::slice(Ty::Int(elem)),
                    },
                    _ => b.expr,
                };
                Some(Checked::new(
                    TExprKind::StrPtr(Box::new(view)),
                    Ty::Ptr(elem),
                    None,
                ))
            }
            (ty, name) => {
                self.error(member.span, format!("`{ty}` has no field `{name}`"));
                None
            }
        }
    }

    pub(super) fn usize_ty(&self) -> Ty {
        Ty::Int(IntTy {
            signed: false,
            bits: self.ptr_bits,
            size: true,
        })
    }

    fn isize_ty(&self) -> Ty {
        Ty::Int(IntTy {
            signed: true,
            bits: self.ptr_bits,
            size: true,
        })
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
                let facts = c.facts.map(|f| Box::new(f.negated()));
                let mut out = Checked::new(
                    TExprKind::Unary(TUnOp::Not, Box::new(c.expr)),
                    Ty::Bool,
                    None,
                );
                out.facts = facts;
                Some(out)
            }
            UnOp::BitNot => {
                let c = self.expr(cx, operand, expected)?;
                if c.ty().as_int().is_none() {
                    self.error(span, format!("`~` needs an integer, found `{}`", c.ty()));
                    return None;
                }
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

    /// Check two operands that must share a type. An untyped integer on one
    /// side takes the other side's type; otherwise a lossless widening is
    /// applied to the narrower side.
    pub(super) fn operands(
        &mut self,
        cx: &mut FnCx,
        lhs: &ast::Expr,
        rhs: &ast::Expr,
        expected: Option<Ty>,
    ) -> Option<(Checked, Checked)> {
        let l_untyped = self.untyped_int(cx, lhs).is_some();
        let r_untyped = self.untyped_int(cx, rhs).is_some();
        let (l, r) = match (l_untyped, r_untyped) {
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
            // An array literal or `none` takes its type from the other side,
            // as in `xs == [1, 2, 3]`.
            _ if needs_context(rhs) && !needs_context(lhs) => {
                let l = self.expr(cx, lhs, expected)?;
                let r = self.expr(cx, rhs, Some(l.ty()))?;
                (l, r)
            }
            _ if needs_context(lhs) && !needs_context(rhs) => {
                let r = self.expr(cx, rhs, expected)?;
                let l = self.expr(cx, lhs, Some(r.ty()))?;
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
            // A widening, or a value compared with an optional.
            (a, b) if coercible(a, b) && !b.is_view() => Some((self.coerce(l, b, lhs.span)?, r)),
            (a, b) if coercible(b, a) && !a.is_view() => Some((l, self.coerce(r, a, rhs.span)?)),
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
                // The right side is only evaluated when the left side is true
                // (`&&`) or false (`||`), so it's checked with those facts.
                let lf = l
                    .as_ref()
                    .and_then(|l| l.facts.as_deref().cloned())
                    .unwrap_or_default();
                let saved = cx.env.clone();
                cx.env.apply(if op == BinOp::And {
                    &lf.when_true
                } else {
                    &lf.when_false
                });
                let r = self
                    .expr(cx, rhs, Some(Ty::Bool))
                    .and_then(|r| self.coerce(r, Ty::Bool, rhs.span));
                cx.env = saved;
                let (l, r) = (l?, r?);
                let rf = r.facts.map(|f| *f).unwrap_or_default();
                let (le, re) = (Box::new(l.expr), Box::new(r.expr));
                let (kind, facts) = if op == BinOp::And {
                    (TExprKind::And(le, re), CondFacts::and(lf, rf))
                } else {
                    (TExprKind::Or(le, re), CondFacts::or(lf, rf))
                };
                let mut out = Checked::new(kind, Ty::Bool, None);
                out.facts = Some(Box::new(facts));
                Some(out)
            }
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let (l, r) = self.operands(cx, lhs, rhs, None)?;
                let ordered = !matches!(op, BinOp::Eq | BinOp::Ne);
                match l.ty() {
                    Ty::Int(_) => {}
                    // Arrays and structs compare element by element, field
                    // by field: every type they can hold has `==`.
                    Ty::Bool
                    | Ty::Ptr(_)
                    | Ty::Array(_)
                    | Ty::Struct(_)
                    | Ty::Enum(_)
                    | Ty::Optional(_)
                        if !ordered => {}
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
                let facts = l
                    .ty()
                    .as_int()
                    .map(|_| Box::new(facts::comparison(cmp, l.side(), r.side())));
                let kind = TExprKind::Binary(TBinOp::Cmp(cmp), Box::new(l.expr), Box::new(r.expr));
                let mut out = Checked::new(kind, Ty::Bool, None);
                out.facts = facts;
                Some(out)
            }
            BinOp::Shl | BinOp::ShlWrap | BinOp::Shr => self.shift(cx, op, lhs, rhs, expected),
            BinOp::Coalesce => self.coalesce(cx, lhs, rhs, expected),
            _ => self.arith(cx, op, lhs, rhs, span, expected),
        }
    }

    /// `opt ?? default`: the value in `opt`, or `default` if it's `none`.
    fn coalesce(
        &mut self,
        cx: &mut FnCx,
        lhs: &ast::Expr,
        rhs: &ast::Expr,
        expected: Option<Ty>,
    ) -> Option<Checked> {
        let l = self.expr(cx, lhs, expected.map(Ty::optional))?;
        let Some(inner) = l.ty().as_optional() else {
            self.error(
                lhs.span,
                format!("`??` needs an optional on its left, found `{}`", l.ty()),
            );
            return None;
        };
        // `opt ?? throw value` leaves the function when `opt` is `none`.
        let r = match &rhs.kind {
            ExprKind::Throw(value) => TExpr {
                kind: TExprKind::Throw(Box::new(self.throw(cx, value, rhs.span)?)),
                ty: inner,
            },
            _ => {
                let r = self.expr(cx, rhs, Some(inner))?;
                self.coerce(r, inner, rhs.span)?.expr
            }
        };
        Some(Checked::new(
            TExprKind::Coalesce(Box::new(l.expr), Box::new(r)),
            inner,
            None,
        ))
    }

    /// `p + n` on a raw pointer: move it forward by `n` elements.
    fn pointer_add(
        &mut self,
        cx: &mut FnCx,
        p: Checked,
        rhs: &ast::Expr,
        span: Span,
    ) -> Option<Checked> {
        self.require_unsafe(cx, span, "pointer arithmetic");
        let usize_ty = self.usize_ty();
        let n = self.expr(cx, rhs, Some(usize_ty))?;
        let n = self.coerce(n, usize_ty, rhs.span)?;
        let ty = p.ty();
        Some(Checked::new(
            TExprKind::PtrAdd(Box::new(p.expr), Box::new(n.expr)),
            ty,
            None,
        ))
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
        if self.untyped_int(cx, lhs).is_none() {
            // Pointers only take `p + n`; check for them before the usual
            // same-type operand rules.
            let probe = self.expr(cx, lhs, expected)?;
            if let Ty::Ptr(_) = probe.ty() {
                if op == BinOp::Add {
                    return self.pointer_add(cx, probe, rhs, span);
                }
                self.error(
                    span,
                    format!(
                        "`{}` doesn't apply to pointers; only `p + n` does",
                        op.as_str()
                    ),
                );
                return None;
            }
        }
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
        // A proven `x + k` or `x - k` of a term `x` and a constant `k` is
        // that term plus a constant, which the facts can relate to others.
        let exact = |r: Range| (r.lo == r.hi).then_some(r.lo);
        let linear = match op {
            BinOp::Add => match (l.term, exact(b), r.term, exact(a)) {
                (Some(x), Some(k), _, _) | (_, _, Some(x), Some(k)) => x.plus(k),
                _ => None,
            },
            BinOp::Sub => match (l.term, exact(b)) {
                (Some(x), Some(k)) => x.plus(-k),
                _ => None,
            },
            _ => None,
        };

        let (top, range) = match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                let mut result = match op {
                    BinOp::Add => a.checked_add(b),
                    BinOp::Sub => a.checked_sub(b),
                    _ => a.checked_mul(b),
                };
                // `x - y` of two terms: a known relation between them bounds
                // the difference (e.g. `y <= x` gives `x - y >= 0`).
                if op == BinOp::Sub
                    && let (Some(x), Some(y), Some(res)) = (l.term, r.term, result)
                {
                    let lo = cx.env.diff_bound(y, x).map_or(res.lo, |c| res.lo.max(-c));
                    let hi = cx.env.diff_bound(x, y).map_or(res.hi, |c| res.hi.min(c));
                    result = Some(Range { lo, hi });
                }
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
        let mut out = Checked::new(kind, Ty::Int(t), Some(range));
        out.term = linear;
        Some(out)
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

    /// A call. The result of a call to a function that throws must be
    /// `handled` (by `try`, `catch` or `match`, which then get a value of
    /// its result type); otherwise it's an error.
    pub(super) fn call(
        &mut self,
        cx: &mut FnCx,
        callee: &ast::Expr,
        args: &[ast::Expr],
        span: Span,
        handled: bool,
    ) -> Option<Checked> {
        if let ExprKind::Field(base, member) = &callee.kind
            && let Some(ty) = self.type_path(cx, base)
        {
            return self.enum_variant(cx, ty?, member, Some(args), span);
        }
        if let ExprKind::Field(base, _) = &callee.kind
            && self.unknown_receiver(cx, base)
        {
            return None;
        }
        let target = match &callee.kind {
            ExprKind::Name(name) if cx.lookup(name).is_none() => {
                if let Some(&Item::Func(id)) = self.pkgs[cx.pkg].items.get(name) {
                    (id, name.clone())
                } else if let Some(&Item::Type(ty)) = self.pkgs[cx.pkg].items.get(name) {
                    if ty.as_enum().is_some() {
                        return self.enum_from(cx, ty, args, span);
                    }
                    self.error(
                        callee.span,
                        format!("`{name}` is a struct; build one with `{name}{{...}}`"),
                    );
                    return None;
                } else if primitive(name, self.ptr_bits).is_some() {
                    return self.conversion(cx, name, callee.span, args, span);
                } else if name == SYSCALL {
                    return self.syscall(cx, args, span);
                } else {
                    self.error(callee.span, format!("cannot find function `{name}`"));
                    return None;
                }
            }
            ExprKind::Field(base, member) if matches!(&base.kind, ExprKind::Name(n) if self.imported(cx, n).is_some()) =>
            {
                let ExprKind::Name(pkg_name) = &base.kind else {
                    unreachable!()
                };
                let pkg = self.imported(cx, pkg_name).expect("checked");
                match self.package_item(cx, pkg, &member.name, member.span)? {
                    Item::Func(id) => (id, format!("{pkg_name}.{}", member.name)),
                    Item::Type(ty) if ty.as_enum().is_some() => {
                        return self.enum_from(cx, ty, args, span);
                    }
                    Item::Const(_) | Item::Type(_) => {
                        self.error(
                            callee.span,
                            format!("`{pkg_name}.{}` is not a function", member.name),
                        );
                        return None;
                    }
                }
            }
            ExprKind::Field(..) => {
                self.error(callee.span, "methods are not supported by the compiler yet");
                return None;
            }
            _ => {
                self.error(callee.span, "only named functions can be called");
                return None;
            }
        };
        let (id, name) = target;
        if self.sigs[id].is_unsafe {
            self.require_unsafe(
                cx,
                callee.span,
                &format!("calling the `unsafe fn` `{name}`"),
            );
        }
        let (params, mut ret) = (self.sigs[id].params.clone(), self.sigs[id].ret);
        if let Some(err) = self.sigs[id].throws {
            if handled {
                ret = Ty::result(ret, err);
            } else {
                // Reported, then checked as if passed on, to go on checking.
                self.diags.push(
                    Diagnostic::error(
                        span,
                        format!("`{name}` can throw, and its error must be handled"),
                    )
                    .with_help(format!(
                        "pass it on with `try {name}(...)`, handle it with `catch`, or `match` on `ok` and `err`"
                    )),
                );
            }
        }
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

    /// `syscall(nr, args...)`: the raw operating-system call (unsafe).
    fn syscall(&mut self, cx: &mut FnCx, args: &[ast::Expr], span: Span) -> Option<Checked> {
        self.require_unsafe(cx, span, "`syscall`");
        if args.is_empty() || args.len() > SYSCALL_MAX_ARGS + 1 {
            self.error(
                span,
                format!("`syscall` takes a number and up to {SYSCALL_MAX_ARGS} arguments"),
            );
            return None;
        }
        let mut targs = Vec::new();
        let mut ok = true;
        for arg in args {
            // An untyped integer is passed as a `usize`, or an `isize` if negative.
            let expected = match self.untyped_int(cx, arg) {
                Some(v) if v < 0 => Some(self.isize_ty()),
                Some(_) => Some(self.usize_ty()),
                None => None,
            };
            match self.expr(cx, arg, expected) {
                Some(c) if matches!(c.ty(), Ty::Int(_) | Ty::Ptr(_)) => targs.push(c.expr),
                Some(c) => {
                    self.error(
                        arg.span,
                        format!(
                            "`syscall` arguments must be integers or pointers, found `{}`",
                            c.ty()
                        ),
                    );
                    ok = false;
                }
                None => ok = false,
            }
        }
        let isize_ty = self.isize_ty();
        ok.then(|| Checked::new(TExprKind::Syscall(targs), isize_ty, None))
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
        let mut c = self.expr(cx, arg, Some(Ty::Int(to)))?;
        // A C-style enum converts to its value.
        if let Some(def) = c.ty().as_enum()
            && def.explicit
        {
            let lo = def.variants.iter().map(|v| v.value).min().unwrap_or(0);
            let hi = def.variants.iter().map(|v| v.value).max().unwrap_or(0);
            c = Checked::new(
                TExprKind::EnumValue(Box::new(c.expr)),
                Ty::Int(def.tag),
                Some(Range { lo, hi }),
            );
        }
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
        let term = c.term;
        let mut out = Checked::new(TExprKind::Convert(Box::new(c.expr)), Ty::Int(to), Some(r));
        out.term = term;
        Some(out)
    }
}
