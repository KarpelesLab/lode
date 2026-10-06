//! Compile-time parameters, packs, and the statements that run while a
//! function is checked (docs/generics.md, Format strings).
//!
//! A function with `comptime` parameters or a pack (`[..A: Format]` and
//! `args: ..A`) is a template: it isn't checked on its own. A call gives
//! values for its `comptime` parameters and some number of pack arguments,
//! and calls the expansion of the template for them, made the first time:
//! a function of its own, in which each `comptime` parameter is a value
//! known when compiling, and the pack is that many type parameters (each
//! with the pack's bounds) and parameters. An expansion is checked like
//! any other function, running `comptime let`, `comptime for`, `match
//! comptime` and `if comptime` as it goes. It's generic in the pack's
//! types, so `crate::mono` makes its instances as for any generic function.
//!
//! A `compile_error` reached in an expansion is reported at the call that
//! made it (the outermost one, when an expansion calls another), or at the
//! part of a string literal it's given (`compile_error_at`): a format
//! string's error points into the format string.

use std::collections::HashMap;

use super::eval::{self, StrVal, Value};
use super::expr::Checked;
use super::tree::*;
use super::{Checker, ExprKind, FnCx, FuncState, Item, expr_names};
use crate::ast;
use crate::diag::Diagnostic;
use crate::source::Span;
use crate::types::{Range, Ty};

/// How deep expansions may nest (an expansion whose body calls a template
/// makes another): beyond it, compile-time arguments likely change
/// without end.
const MAX_EXPANSION_DEPTH: usize = 64;

/// The most times a `comptime for` repeats its body.
const MAX_COMPTIME_FOR: usize = 1000;

/// The kind of a template's parameter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ParamKind {
    /// An ordinary parameter.
    Runtime,
    /// `comptime name: T`.
    Comptime,
    /// `args: ..A`: the pack, the last parameter.
    Pack,
}

/// What makes a function a template: the kind of each of its parameters.
#[derive(Clone, Debug)]
pub(super) struct Template {
    pub kinds: Vec<ParamKind>,
}

/// An expansion of a template.
pub(super) struct Expansion {
    /// The `comptime` parameters' names, types and values.
    pub values: Vec<(String, Ty, Value)>,
    /// The pack parameter's name, and its type parameters (one per
    /// argument).
    pub pack: Option<(String, Vec<Ty>)>,
    /// Where a `compile_error` in it is reported: the call that made it,
    /// or the one that made the expansion that call is in.
    pub report: Span,
}

/// A value known when compiling, as part of the key of an expansion.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum Key {
    Int(i128),
    Bool(bool),
    Str(Vec<u8>),
}

/// An expansion's template, `comptime` values and number of pack
/// arguments.
pub(super) type ExpansionKey = (FuncId, Vec<Key>, Option<usize>);

/// The pack of the expansion being checked.
#[derive(Clone, Debug)]
pub(super) struct PackCx {
    pub name: String,
    pub len: usize,
}

/// The hidden name of the pack argument `i` of the pack `name`.
pub(super) fn pack_local(name: &str, i: usize) -> String {
    format!("${name}[{i}]")
}

impl Checker<'_> {
    /// Report what a template `f` (with `comptime` parameters or a pack,
    /// `kinds`) can't have. `method`: whether it's a method or an
    /// associated function.
    pub(super) fn check_template(&mut self, f: &ast::FnDecl, method: bool, kinds: &[ParamKind]) {
        if method {
            self.diags.push(
                Diagnostic::error(
                    f.name.span,
                    "a method with `comptime` parameters or a pack is not supported by the compiler yet",
                )
                .with_help("declare it as a function"),
            );
        }
        let packs: Vec<&ast::GenericParam> = f.generics.iter().filter(|g| g.pack).collect();
        if packs.len() > 1 {
            self.error(packs[1].name.span, "a function has at most one pack");
        }
        if let Some(g) = packs.first()
            && !f.generics.last().is_some_and(|l| l.pack)
        {
            self.error(g.name.span, "a pack is the last generic parameter");
        }
        for (k, (p, &kind)) in f.params.iter().zip(kinds).enumerate() {
            if kind != ParamKind::Pack {
                continue;
            }
            let ast::TypeExpr::Pack(name, span) = &p.ty else {
                unreachable!("a pack's type")
            };
            if p.comptime || p.convention != ast::Convention::Let {
                self.error(
                    p.name.span,
                    "a pack parameter is read-only, and not `comptime`",
                );
            }
            if !packs.iter().any(|g| g.name.name == name.name) {
                self.diags.push(
                    Diagnostic::error(
                        *span,
                        format!(
                            "`..{}` is the type of a pack: `{}` must be the function's pack",
                            name.name, name.name
                        ),
                    )
                    .with_help(format!(
                        "declare it last in the brackets: `[..{}: Bound]`",
                        name.name
                    )),
                );
            }
            if k + 1 != kinds.len() {
                self.error(p.name.span, "a pack parameter is the last parameter");
            }
        }
        if let Some(g) = packs.first()
            && !kinds.contains(&ParamKind::Pack)
        {
            self.diags.push(
                Diagnostic::error(
                    g.name.span,
                    format!(
                        "the pack `{}` needs a parameter of type `..{}`",
                        g.name.name, g.name.name
                    ),
                )
                .with_help(format!(
                    "add `args: ..{}` as the last parameter",
                    g.name.name
                )),
            );
        }
    }

    /// The context for code inside `cx` that runs at compile time: the
    /// values known when compiling that `cx` sees (`comptime` parameters
    /// and locals) are locals in it too, with their values (returned).
    pub(super) fn comptime_cx(&self, cx: &FnCx) -> (FnCx, Vec<(LocalId, Value)>) {
        let mut ccx = FnCx::new(cx.pkg, cx.file, cx.ret, false);
        ccx.comptime = true;
        ccx.report = cx.report;
        ccx.self_ty = cx.self_ty;
        ccx.pack = cx.pack.as_ref().map(|p| PackCx {
            name: p.name.clone(),
            len: p.len,
        });
        let mut init = Vec::new();
        for scope in &cx.scopes {
            let mut names: Vec<(&String, &LocalId)> = scope.iter().collect();
            names.sort_by_key(|&(_, &l)| l);
            for (name, &l) in names {
                // Only the innermost declaration of a name is visible.
                if cx.lookup(name) != Some(l) {
                    continue;
                }
                let Some(v) = cx.ct_values.get(&l) else {
                    continue;
                };
                let local = Self::declare_local(&mut ccx, name, cx.locals[l].ty, false, None);
                ccx.ct_values.insert(local, v.clone());
                init.push((local, v.clone()));
            }
        }
        (ccx, init)
    }

    /// Whether `local` holds a value known when compiling.
    pub(super) fn is_comptime_local(cx: &FnCx, local: LocalId) -> bool {
        cx.ct_values.contains_key(&local)
    }

    /// The first variable `e` names that isn't known when compiling, with
    /// its span.
    fn runtime_name<'e>(cx: &FnCx, e: &'e ast::Expr) -> Option<(&'e str, Span)> {
        let mut names = Vec::new();
        expr_names(e, &mut names);
        names.into_iter().find(|(n, _)| {
            cx.lookup(n)
                .is_some_and(|l| !Self::is_comptime_local(cx, l))
        })
    }

    /// The value of `e`, which must be known when compiling: evaluated now.
    /// `what` names it in messages ("the value of `n`").
    pub(super) fn comptime_value(
        &mut self,
        cx: &FnCx,
        e: &ast::Expr,
        expected: Option<Ty>,
        what: &str,
    ) -> Option<(Ty, Value)> {
        // A value whose declaration failed (reported) fails silently.
        let mut names = Vec::new();
        expr_names(e, &mut names);
        if names
            .iter()
            .any(|(n, _)| cx.lookup(n).is_some_and(|l| cx.failed.contains(&l)))
        {
            return None;
        }
        if let Some((name, span)) = Self::runtime_name(cx, e) {
            self.diags.push(
                Diagnostic::error(
                    span,
                    format!("`{name}` is a variable, so {what} isn't known when compiling"),
                )
                .with_help("code that runs when compiling uses literals, constants, `comptime` parameters and `comptime let` values"),
            );
            return None;
        }
        let (mut ccx, init) = self.comptime_cx(cx);
        let c = self.expr(&mut ccx, e, expected)?;
        let c = match expected {
            Some(t) => self.coerce(&mut ccx, c, t, e.span)?,
            None => c,
        };
        if matches!(c.ty(), Ty::Unit | Ty::Never) {
            self.error(e.span, "this expression has no value");
            return None;
        }
        let subject = eval::Subject {
            what,
            span: e.span,
            budget_span: None,
        };
        let ty = c.ty();
        let v = self.evaluate_with(
            &c.expr,
            ccx.locals.len(),
            &init,
            eval::DEFAULT_STEPS,
            &subject,
        )?;
        Some((ty, v))
    }

    /// A value known when compiling, of type `ty`, used in code that runs
    /// when the program does: the literal that builds it.
    pub(super) fn materialize_ct(&mut self, v: &Value, ty: Ty, span: Span) -> Option<Checked> {
        Some(match v {
            Value::Str(s) => {
                let bytes = s.bytes(&self.strings).to_vec();
                let id = self.intern_string(&bytes);
                Checked::new(TExprKind::Str(id), Ty::Str, None)
            }
            Value::Int(x) => Checked::new(TExprKind::Int(*x), ty, Some(Range::exact(*x))),
            Value::Bool(b) => Checked::new(TExprKind::Bool(*b), Ty::Bool, None),
            Value::Slice(..) => {
                self.error(
                    span,
                    "a slice known when compiling can't be used when the program runs yet",
                );
                return None;
            }
            Value::Unit | Value::Uninit => {
                self.error(span, "this value isn't known when compiling");
                return None;
            }
            other => {
                let e = eval::materialize(other, ty);
                Checked::new(e.kind, e.ty, None)
            }
        })
    }

    /// The text of a `compile_error`'s message `msg`, each `{}` replaced by
    /// one of `values` (`{{` and `}}` are braces), or why it can't be made.
    pub(super) fn user_message(&self, msg: StrVal, values: &[Value]) -> Result<String, String> {
        let bytes = msg.bytes(&self.strings);
        let mut out = Vec::new();
        let mut next = values.iter();
        let mut used = 0;
        let mut i = 0;
        while i < bytes.len() {
            match (bytes[i], bytes.get(i + 1)) {
                (b'{', Some(b'{')) | (b'}', Some(b'}')) => {
                    out.push(bytes[i]);
                    i += 2;
                }
                (b'{', Some(b'}')) => {
                    used += 1;
                    let Some(v) = next.next() else {
                        return Err(format!(
                            "the message of `compile_error` has more `{{}}` than the {} value(s) given",
                            values.len()
                        ));
                    };
                    match v {
                        Value::Int(x) => out.extend(x.to_string().into_bytes()),
                        Value::Bool(b) => out.extend(b.to_string().into_bytes()),
                        Value::Str(s) => out.extend_from_slice(s.bytes(&self.strings)),
                        _ => {
                            return Err("`compile_error` shows integers, `bool` and `str` values"
                                .to_owned());
                        }
                    }
                    i += 2;
                }
                (b'{' | b'}', _) => {
                    return Err(
                        "a brace in the message of `compile_error` is written `{{` or `}}`"
                            .to_owned(),
                    );
                }
                (b, _) => {
                    out.push(b);
                    i += 1;
                }
            }
        }
        if used != values.len() {
            return Err(format!(
                "the message of `compile_error` has {used} `{{}}` for {} value(s)",
                values.len()
            ));
        }
        Ok(String::from_utf8_lossy(&out).into_owned())
    }

    /// Where the `str` value `v` is in the source, when it's part of a
    /// string literal there.
    pub(super) fn place_span(&self, v: &Value) -> Option<Span> {
        let Value::Str(s) = v else {
            return None;
        };
        let origin = s.origin?;
        let text = self.sources.get(&origin.file)?;
        let offsets = crate::lex::literal_offsets(text, origin.start as usize, origin.file);
        if offsets.len() != self.strings[s.id].len() + 1 {
            return None;
        }
        let (start, end) = (offsets[s.start] as u32, offsets[s.start + s.len] as u32);
        // A character or an escape ends where the next one starts.
        Some(Span {
            start,
            end: end.max(start + 1),
            ..origin
        })
    }

    /// `compile_error(...)` or `compile_error_at(...)` in an expression of
    /// code that runs at compile time: an error when it's reached.
    pub(super) fn compile_error_expr(
        &mut self,
        cx: &mut FnCx,
        name: &str,
        args: &[ast::Expr],
        span: Span,
    ) -> Option<Checked> {
        let at = name == super::COMPILE_ERROR_AT;
        if !cx.comptime {
            self.diags.push(
                Diagnostic::error(span, format!("`{name}` is a statement"))
                    .with_help("it's an error where it's compiled, and has no value"),
            );
            return None;
        }
        let first = usize::from(at);
        if args.len() <= first {
            let want = if at {
                "a `str` to point at and a message"
            } else {
                "a message"
            };
            self.error(
                span,
                format!("`{name}` takes {want}, then the values to show"),
            );
            return None;
        }
        let mut ok = true;
        let mut check = |ck: &mut Self, cx: &mut FnCx, e: &ast::Expr, t: Option<Ty>| {
            let c = ck.expr(cx, e, t);
            let c = match (c, t) {
                (Some(c), Some(t)) => ck.coerce(cx, c, t, e.span),
                (c, _) => c,
            };
            ok &= c.is_some();
            c.map(|c| c.expr)
        };
        let place = if at {
            check(self, cx, &args[0], Some(Ty::Str))
        } else {
            None
        };
        let message = check(self, cx, &args[first], Some(Ty::Str));
        let values: Vec<Option<TExpr>> = args[first + 1..]
            .iter()
            .map(|a| check(self, cx, a, None))
            .collect();
        if !ok {
            return None;
        }
        cx.env.dead = true;
        Some(Checked::new(
            TExprKind::CompileError {
                place: place.map(Box::new),
                message: Box::new(message.expect("checked")),
                values: values.into_iter().map(|v| v.expect("checked")).collect(),
                span: cx.report.unwrap_or(span),
            },
            Ty::Never,
            None,
        ))
    }

    /// `compile_error(...)` or `compile_error_at(...)` as a statement of a
    /// body, reached in the code compiled for the target: reported now.
    pub(super) fn compile_error_stmt(&mut self, cx: &mut FnCx, call: &ast::Expr) {
        let ExprKind::Call(callee, args) = &call.kind else {
            unreachable!("a call of `compile_error`")
        };
        let ExprKind::Name(name) = &callee.kind else {
            unreachable!("a call of `compile_error`")
        };
        // A message alone, outside of an expansion: as at package level.
        let plain = name == super::COMPILE_ERROR
            && cx.report.is_none()
            && matches!(
                &args[..],
                [ast::Expr {
                    kind: ExprKind::Str(_),
                    ..
                }]
            );
        if plain {
            self.compile_error(call);
            return;
        }
        let (mut ccx, init) = self.comptime_cx(cx);
        if let Some((var, span)) = Self::runtime_name(cx, call) {
            self.error(
                span,
                format!("`{var}` is a variable, so this message isn't known when compiling"),
            );
            return;
        }
        let Some(c) = self.compile_error_expr(&mut ccx, name, args, call.span) else {
            return;
        };
        let subject = eval::Subject {
            what: "this `compile_error`",
            span: call.span,
            budget_span: None,
        };
        self.evaluate_with(
            &c.expr,
            ccx.locals.len(),
            &init,
            eval::DEFAULT_STEPS,
            &subject,
        );
        cx.env.dead = true;
    }

    /// `comptime let name: ty = init`: a value known when compiling,
    /// computed now.
    pub(super) fn comptime_let(
        &mut self,
        cx: &mut FnCx,
        name: &ast::Ident,
        ty: Option<&ast::TypeExpr>,
        init: &ast::Expr,
    ) {
        let annotated = match ty {
            Some(t) => match self.resolve_type(cx, t) {
                Some(t) => Some(t),
                None => {
                    let l = self.declare(cx, &name.name, Ty::Unit, false);
                    cx.failed.insert(l);
                    return;
                }
            },
            None => None,
        };
        if cx.scopes.last().expect("scope").contains_key(&name.name) {
            self.error(
                name.span,
                format!("`{}` is already declared in this block", name.name),
            );
            return;
        }
        let what = format!("the value of `{}`", name.name);
        match self.comptime_value(cx, init, annotated, &what) {
            Some((t, v)) => {
                let l = self.declare(cx, &name.name, t, false);
                cx.ct_values.insert(l, v);
            }
            None => {
                let l = self.declare(cx, &name.name, annotated.unwrap_or(Ty::Unit), false);
                cx.failed.insert(l);
            }
        }
    }

    /// `comptime for var in iter { body }`: the body, checked once for each
    /// element of a list known when compiling, with `var` that element.
    pub(super) fn comptime_for(
        &mut self,
        cx: &mut FnCx,
        var: &ast::Ident,
        iter: &ast::ForIter,
        body: &ast::Block,
        span: Span,
    ) -> Option<TStmt> {
        let usize_ty = self.usize_ty();
        let (elem_ty, elems): (Ty, Vec<Value>) = match iter {
            ast::ForIter::Range(a, b) => {
                let (_, a) = self.comptime_value(cx, a, Some(usize_ty), "the range's start")?;
                let (_, b) = self.comptime_value(cx, b, Some(usize_ty), "the range's end")?;
                let (a, b) = (a.int(), b.int());
                if b - a > MAX_COMPTIME_FOR as i128 {
                    self.too_many_repeats(span, b - a);
                    return None;
                }
                (usize_ty, (a..b.max(a)).map(Value::Int).collect())
            }
            ast::ForIter::Each(xs) => {
                let (t, v) = self.comptime_value(cx, xs, None, "the list")?;
                let Some(elem) = t.elem() else {
                    self.error(
                        xs.span,
                        format!(
                            "`comptime for` goes over a range, an array or a slice, not a `{t}`"
                        ),
                    );
                    return None;
                };
                let elems = match &v {
                    Value::Array(_) | Value::Slice(..) => eval::elems(&v).to_vec(),
                    _ => unreachable!("an array or a slice"),
                };
                if elems.len() > MAX_COMPTIME_FOR {
                    self.too_many_repeats(span, elems.len() as i128);
                    return None;
                }
                (elem, elems)
            }
        };
        let floor = cx.ct_loop_floor.replace(cx.loop_depth);
        let mut out = Vec::new();
        for v in elems {
            cx.scopes.push(HashMap::new());
            let l = self.declare(cx, &var.name, elem_ty, false);
            cx.ct_values.insert(l, v);
            out.push(TStmt::Block(self.block(cx, &body.stmts)));
            cx.scopes.pop();
        }
        cx.ct_loop_floor = floor;
        Some(TStmt::Block(out))
    }

    fn too_many_repeats(&mut self, span: Span, n: i128) {
        self.diags.push(
            Diagnostic::error(
                span,
                format!(
                    "this `comptime for` would repeat its body {n} times, more than {MAX_COMPTIME_FOR}"
                ),
            )
            .with_help("use a `for` loop, which runs when the program does"),
        );
    }

    /// `match comptime value { arms }`: only the arm the value (known when
    /// compiling) picks is checked, with its bindings known too.
    pub(super) fn comptime_match(
        &mut self,
        cx: &mut FnCx,
        value: &ast::Expr,
        arms: &[ast::Arm],
    ) -> Option<TStmt> {
        let (ty, v) = self.comptime_value(cx, value, None, "the value of `match comptime`")?;
        for arm in arms {
            let Some(bindings) = self.comptime_pattern(cx, &arm.pattern, ty, &v)? else {
                continue;
            };
            cx.scopes.push(HashMap::new());
            for (name, t, val) in bindings {
                let l = self.declare(cx, &name, t, false);
                cx.ct_values.insert(l, val);
            }
            let body = self.block(cx, &arm.body.stmts);
            cx.scopes.pop();
            return Some(TStmt::Block(body));
        }
        self.error(
            value.span,
            "no arm of this `match comptime` matches its value",
        );
        None
    }

    /// Whether `pattern` matches `v`, of type `ty`, and the values it binds:
    /// `Some(None)` if it doesn't match, `None` if it's in error (reported).
    #[allow(clippy::type_complexity)]
    fn comptime_pattern(
        &mut self,
        cx: &FnCx,
        pattern: &ast::Pattern,
        ty: Ty,
        v: &Value,
    ) -> Option<Option<Vec<(String, Ty, Value)>>> {
        match pattern {
            ast::Pattern::Wildcard(_) => Some(Some(Vec::new())),
            ast::Pattern::Or(alts, _) => {
                for alt in alts {
                    if let Some(b) = self.comptime_pattern(cx, alt, ty, v)? {
                        return Some(Some(b));
                    }
                }
                Some(None)
            }
            ast::Pattern::Variant { name, bindings, .. } if ty.sum().is_some() => {
                let def = ty.sum().expect("checked");
                let Some((k, variant)) = def.variant(&name.name) else {
                    self.error(name.span, format!("`{ty}` has no variant `{}`", name.name));
                    return None;
                };
                let given = bindings.as_ref().map_or(0, Vec::len);
                if bindings.is_some() && given != variant.fields.len() {
                    self.error(
                        name.span,
                        format!(
                            "`{}` has {} field(s), but the pattern names {given}",
                            name.name,
                            variant.fields.len()
                        ),
                    );
                    return None;
                }
                let Value::Variant(j, fields) = v else {
                    unreachable!("a value of an enum")
                };
                if *j as usize != k {
                    return Some(None);
                }
                let mut out = Vec::new();
                for ((b, f), val) in bindings
                    .iter()
                    .flatten()
                    .zip(&variant.fields)
                    .zip(fields.iter())
                {
                    if b.name != "_" {
                        out.push((b.name.clone(), f.ty, val.clone()));
                    }
                }
                Some(Some(out))
            }
            ast::Pattern::Variant { name, span, .. } => {
                let e = ast::Expr {
                    kind: ExprKind::Name(name.name.clone()),
                    span: *span,
                };
                self.comptime_value_pattern(cx, &e, ty, v)
            }
            ast::Pattern::Value(e) => self.comptime_value_pattern(cx, e, ty, v),
            ast::Pattern::Range(lo, hi, _) => {
                let (_, lo) = self.comptime_value(cx, lo, Some(ty), "the pattern")?;
                let (_, hi) = self.comptime_value(cx, hi, Some(ty), "the pattern")?;
                let x = v.int();
                Some((lo.int() <= x && x <= hi.int()).then(Vec::new))
            }
        }
    }

    fn comptime_value_pattern(
        &mut self,
        cx: &FnCx,
        e: &ast::Expr,
        ty: Ty,
        v: &Value,
    ) -> Option<Option<Vec<(String, Ty, Value)>>> {
        let (_, p) = self.comptime_value(cx, e, Some(ty), "the pattern")?;
        Some(eval::equal(&p, v, &self.strings).then(Vec::new))
    }

    /// `args.len` or `args[i]` of the pack `args` (`e`'s base names it):
    /// its length, or argument `i`, `i` known when compiling.
    pub(super) fn pack_expr(&mut self, cx: &mut FnCx, e: &ast::Expr) -> Option<Option<Checked>> {
        let pack = cx.pack.clone()?;
        let named = |b: &ast::Expr| matches!(&b.kind, ExprKind::Name(n) if *n == pack.name);
        match &e.kind {
            ExprKind::Field(base, member) if named(base) && cx.lookup(&pack.name).is_none() => {
                if member.name != "len" {
                    self.error(
                        member.span,
                        format!(
                            "a pack has a length, `{}.len`, and no other field",
                            pack.name
                        ),
                    );
                    return Some(None);
                }
                let n = pack.len as i128;
                Some(Some(Checked::new(
                    TExprKind::Int(n),
                    self.usize_ty(),
                    Some(Range::exact(n)),
                )))
            }
            ExprKind::Index(base, index) if named(base) && cx.lookup(&pack.name).is_none() => {
                if cx.comptime {
                    self.error(
                        e.span,
                        format!("`{}[...]` is only known when the program runs", pack.name),
                    );
                    return Some(None);
                }
                let usize_ty = self.usize_ty();
                let Some((_, i)) =
                    self.comptime_value(cx, index, Some(usize_ty), "the index into a pack")
                else {
                    return Some(None);
                };
                let i = i.int();
                if i < 0 || i >= pack.len as i128 {
                    self.error(
                        index.span,
                        format!(
                            "`{}` has {} argument(s), so the index {i} is out of bounds",
                            pack.name, pack.len
                        ),
                    );
                    return Some(None);
                }
                Some(self.expr(
                    cx,
                    &ast::Expr {
                        kind: ExprKind::Name(pack_local(&pack.name, i as usize)),
                        span: e.span,
                    },
                    None,
                ))
            }
            _ => None,
        }
    }

    /// For a call of the template `t` (`name`) with `args`: its expansion
    /// for the values of its `comptime` arguments and the number of pack
    /// arguments, and the arguments the expansion takes.
    pub(super) fn expand_call(
        &mut self,
        cx: &mut FnCx,
        t: FuncId,
        name: &str,
        args: &[ast::Expr],
        span: Span,
    ) -> Option<(FuncId, Vec<ast::Expr>)> {
        let kinds = self.sigs[t].template.clone().expect("a template").kinds;
        let params = self.sigs[t].params.clone();
        let has_pack = kinds.last() == Some(&ParamKind::Pack);
        // `..args` passes on the caller's pack.
        let mut list: Vec<ast::Expr> = Vec::new();
        for (k, a) in args.iter().enumerate() {
            let ExprKind::Spread(inner) = &a.kind else {
                list.push(a.clone());
                continue;
            };
            let pack = match (&inner.kind, &cx.pack) {
                (ExprKind::Name(n), Some(p)) if *n == p.name && cx.lookup(n).is_none() => p.clone(),
                _ => {
                    self.diags.push(
                        Diagnostic::error(a.span, "only a pack can be passed on with `..`")
                            .with_help("in a function with a pack `args: ..A`, `..args` passes its arguments on"),
                    );
                    return None;
                }
            };
            if k + 1 != args.len() || !has_pack {
                self.error(
                    a.span,
                    format!(
                        "`..{}` is the last argument of a call of a function with a pack",
                        pack.name
                    ),
                );
                return None;
            }
            if cx.comptime {
                self.error(
                    a.span,
                    format!("`{}` is only known when the program runs", pack.name),
                );
                return None;
            }
            for i in 0..pack.len {
                list.push(ast::Expr {
                    kind: ExprKind::Name(pack_local(&pack.name, i)),
                    span: a.span,
                });
            }
        }
        let fixed = kinds.len() - usize::from(has_pack);
        if list.len() < fixed || (!has_pack && list.len() != fixed) {
            let takes = if has_pack {
                format!("at least {fixed} argument(s)")
            } else {
                format!("{fixed} argument(s)")
            };
            self.error(
                span,
                format!("`{name}` takes {takes}, but {} were given", list.len()),
            );
            return None;
        }
        let mut values = Vec::new();
        let mut runtime = Vec::new();
        let mut ok = true;
        for (k, kind) in kinds.iter().enumerate().take(fixed) {
            match kind {
                ParamKind::Comptime => {
                    let (ty, _, pname) = &params[k];
                    match self.comptime_arg(cx, &list[k], *ty, pname, name) {
                        Some(v) => values.push(v),
                        None => ok = false,
                    }
                }
                _ => runtime.push(list[k].clone()),
            }
        }
        if !ok {
            return None;
        }
        let pack_len = has_pack.then(|| list.len() - fixed);
        runtime.extend(list.drain(fixed..));
        let id = self.expansion(cx, t, values, pack_len, span)?;
        Some((id, runtime))
    }

    /// The value of the argument `arg` of the `comptime` parameter `pname`
    /// (of type `ty`) of `fname`.
    fn comptime_arg(
        &mut self,
        cx: &FnCx,
        arg: &ast::Expr,
        ty: Ty,
        pname: &str,
        fname: &str,
    ) -> Option<Value> {
        if let Some((var, _)) = Self::runtime_name(cx, arg) {
            let mut d = Diagnostic::error(
                arg.span,
                format!(
                    "`{pname}` of `{fname}` is `comptime`, so its argument must be known when compiling, and `{var}` is a variable"
                ),
            )
            .with_help("pass a literal, a constant, or a `comptime` value");
            if ty == Ty::Str {
                d = d.with_help(format!(
                    "to print a `str` known only when the program runs, format it: `{fname}(\"{{}}\", {var})`"
                ));
            }
            self.diags.push(d);
            return None;
        }
        let (_, mut v) = self.comptime_value(cx, arg, Some(ty), &format!("`{pname}`"))?;
        if let (ExprKind::Str(_), Value::Str(s)) = (&arg.kind, &mut v) {
            s.origin = Some(arg.span);
        }
        Some(v)
    }

    /// The expansion of template `t` for the `comptime` values `values` and
    /// `pack_len` pack arguments, made (and checked) if it's new, for a
    /// call at `span` in `cx`.
    fn expansion(
        &mut self,
        cx: &FnCx,
        t: FuncId,
        values: Vec<Value>,
        pack_len: Option<usize>,
        span: Span,
    ) -> Option<FuncId> {
        let keys: Vec<Key> = values
            .iter()
            .map(|v| match v {
                Value::Int(x) => Key::Int(*x),
                Value::Bool(b) => Key::Bool(*b),
                Value::Str(s) => Key::Str(s.bytes(&self.strings).to_vec()),
                other => unreachable!("a `comptime` parameter's value: {other:?}"),
            })
            .collect();
        let key = (t, keys, pack_len);
        if let Some(&id) = self.expansion_ids.get(&key) {
            match self.func_states[id] {
                // Checked during a trial of a loop's body, then rolled back.
                FuncState::Unchecked => {
                    self.check_function(id);
                    return Some(id);
                }
                FuncState::Checking | FuncState::Done(_, true) => return Some(id),
                // An expansion with errors: another, so they're reported
                // for this call too.
                FuncState::Done(_, false) => {}
            }
        }
        let name = self.sigs[t].name.clone();
        if self.expanding >= MAX_EXPANSION_DEPTH {
            self.diags.push(
                Diagnostic::error(
                    span,
                    format!("expanding `{name}` here nests more than {MAX_EXPANSION_DEPTH} expansions deep"),
                )
                .with_help("a function with `comptime` parameters that calls itself must reach the same values again"),
            );
            return None;
        }
        let (decl, pkg, file) = self.fn_decls[t];
        let count = self.expansion_counts.entry(t).or_default();
        *count += 1;
        let k = *count;
        let mut scx = FnCx::new(pkg, file, Ty::Unit, false);
        scx.expanding = Some(pack_len.unwrap_or(0));
        let mut sig = self.signature(&mut scx, decl, None);
        sig.template = None;
        let base = self.sigs[t].symbol_name.clone().unwrap_or(name);
        sig.symbol_name = Some(format!("{base}${k}"));
        let comptime: Vec<(String, Ty)> = self.sigs[t]
            .params
            .iter()
            .zip(&self.sigs[t].template.as_ref().expect("a template").kinds)
            .filter(|(_, k)| **k == ParamKind::Comptime)
            .map(|((ty, _, n), _)| (n.clone(), *ty))
            .collect();
        let pack = decl
            .params
            .iter()
            .find(|p| matches!(p.ty, ast::TypeExpr::Pack(..)))
            .map(|p| (p.name.name.clone(), scx.pack_params.clone()));
        self.view_params.extend(scx.pack_params.iter().copied());
        let id = self.sigs.len();
        self.sigs.push(sig);
        self.fn_decls.push((decl, pkg, file));
        self.func_states.push(FuncState::Unchecked);
        self.expansions.insert(
            id,
            Expansion {
                values: comptime
                    .into_iter()
                    .zip(values)
                    .map(|((n, ty), v)| (n, ty, v))
                    .collect(),
                pack,
                report: cx.report.unwrap_or(span),
            },
        );
        self.expansion_ids.insert(key, id);
        self.expanding += 1;
        self.check_function(id);
        self.expanding -= 1;
        Some(id)
    }

    /// For an expansion being checked in `cx`: its `comptime` parameters as
    /// values known when compiling, its pack, and where its
    /// `compile_error`s are reported.
    pub(super) fn declare_expansion(&mut self, cx: &mut FnCx, id: FuncId) {
        let Some(exp) = self.expansions.get(&id) else {
            return;
        };
        let values = exp.values.clone();
        let pack = exp.pack.clone();
        cx.report = Some(exp.report);
        for (name, ty, v) in values {
            let l = Self::declare_local(cx, &name, ty, false, None);
            cx.ct_values.insert(l, v);
        }
        if let Some((name, params)) = pack {
            cx.pack = Some(PackCx {
                name,
                len: params.len(),
            });
        }
    }

    /// Whether `p` is one of the pack's type parameters in expansion `id`.
    pub(super) fn is_pack_param(&self, id: FuncId, p: Ty) -> bool {
        self.expansions
            .get(&id)
            .and_then(|e| e.pack.as_ref())
            .is_some_and(|(_, ps)| ps.contains(&p))
    }

    /// Whether `name` names the item `compile_error` or `compile_error_at`
    /// in `cx` (not a local or an item of the package with that name).
    pub(super) fn names_compile_error(&self, cx: &FnCx, name: &str) -> bool {
        (name == super::COMPILE_ERROR || name == super::COMPILE_ERROR_AT)
            && cx.lookup(name).is_none()
            && !matches!(
                self.unqualified(cx, name),
                Some(Item::Func(_) | Item::Const(_) | Item::Type(_) | Item::Trait(_))
            )
    }
}
