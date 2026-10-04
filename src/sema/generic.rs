//! Generic functions over the built-in traits (docs/generics.md, M7a):
//! type parameters and their bounds, type arguments at a call (explicit,
//! or inferred from the arguments and then from the expected result type),
//! the built-in methods of `Ordered`, the proof rules for type parameters
//! with a numeric bound, and the rule that a value of a type that isn't
//! `Copy` is moved, never copied.
//!
//! A generic body is checked once, against the bounds of its parameters;
//! `crate::mono` makes the instances that are lowered.

use std::collections::{HashMap, HashSet};

use crate::ast::{self, ExprKind};
use crate::diag::Diagnostic;
use crate::source::Span;
use crate::types::{Bounds, Range, Trait, Ty, primitive};

use super::expr::{Checked, place_text};
use super::facts::{Linear, Term};
use super::tree::*;
use super::{Checker, FnCx, Item};

/// The methods `Ordered` gives (docs/generics.md, Built-in traits): `cmp`
/// and the comparisons. User traits (M7c) will declare them in `std`.
pub(super) const ORDERED_METHODS: [&str; 5] = ["cmp", "lt", "le", "gt", "ge"];

/// What the proof rules need of an integer type: a primitive, or a type
/// parameter with a numeric bound (docs/safety.md, "Facts about values of
/// a type parameter").
#[derive(Clone, Copy, Debug)]
pub(super) struct Num {
    /// The values a value of the type can have: the type's range, or for a
    /// parameter, the hull of the ranges of the types its bound admits.
    pub values: Range,
    /// The values that fit in the type: the type's range, or for a
    /// parameter, the intersection of those ranges (`0..=127` for
    /// `Integer`).
    pub fits: Range,
    /// Whether it's signed; `None` for a parameter that may be either.
    pub signed: Option<bool>,
    /// Its width in bits, or for a parameter, the narrowest it can have.
    pub bits: u32,
    /// For a type that is (or may be) signed: its smallest value, or for a
    /// parameter, the largest smallest value of the signed types it admits
    /// (-128), which every value of interest must be above.
    pub min: Option<i128>,
    /// Whether it's a type parameter.
    pub param: bool,
}

/// The [`Num`] of `ty`, if it's an integer type or a type parameter with a
/// numeric bound.
pub(super) fn num(ty: Ty) -> Option<Num> {
    if let Some(t) = ty.as_int() {
        return Some(Num {
            values: t.range(),
            fits: t.range(),
            signed: Some(t.signed),
            bits: t.bits,
            min: t.signed.then(|| t.min()),
            param: false,
        });
    }
    let def = ty.as_param()?;
    let signed = match def.bounds.numeric()? {
        Trait::Unsigned => Some(false),
        Trait::Signed => Some(true),
        _ => None,
    };
    Some(Num {
        values: def.values?,
        fits: def.fits?,
        signed,
        bits: 8,
        min: def.signed_min,
        param: true,
    })
}

/// How a range is shown in messages: as a number, or for the whole range
/// of a type parameter's values, `any T`.
pub(super) fn show_range(r: Range, ty: Ty) -> String {
    match num(ty) {
        Some(n) if n.param && r == n.values => format!("any `{ty}`"),
        _ => r.to_string(),
    }
}

/// The help that says what a type parameter with a numeric bound admits,
/// for a failed proof in a generic body.
pub(super) fn param_help(ty: Ty) -> Option<String> {
    let def = ty.as_param()?;
    let n = num(ty)?;
    let bound = def.bounds.numeric()?;
    Some(format!(
        "`{ty}` can be any `{bound}` type: a value fits in all of them when it's in {}, or when it lies between two values of type `{ty}`",
        n.fits
    ))
}

/// The type arguments of one call, as they're found: the callee's type
/// parameters, and for each, its argument and where it came from.
pub(super) struct Inference {
    params: Vec<Ty>,
    args: Vec<Option<(Ty, Span)>>,
}

impl Inference {
    pub(super) fn new(params: Vec<Ty>) -> Inference {
        let args = vec![None; params.len()];
        Inference { params, args }
    }

    fn index(&self, p: Ty) -> Option<usize> {
        self.params.iter().position(|&q| q == p)
    }

    pub(super) fn fix(&mut self, k: usize, ty: Ty, span: Span) {
        self.args[k] = Some((ty, span));
    }

    /// Whether every type parameter of the callee that `ty` mentions is
    /// known.
    pub(super) fn known(&self, ty: Ty) -> bool {
        let mut found = Vec::new();
        ty.params(&mut found);
        found
            .into_iter()
            .all(|p| self.index(p).is_none_or(|k| self.args[k].is_some()))
    }

    pub(super) fn all_known(&self) -> bool {
        self.args.iter().all(Option::is_some)
    }

    /// `ty` with the callee's known type parameters replaced by their
    /// arguments.
    pub(super) fn apply(&self, ty: Ty) -> Ty {
        ty.subst(&|p| self.index(p).and_then(|k| self.args[k].map(|(t, _)| t)))
    }

    /// Learn type arguments from a value of type `actual` where `pattern`
    /// (a type of the callee's signature) is expected: a type parameter not
    /// known yet is `actual`, or the part of it in the same position. An
    /// array matches a slice (`[4]u8` for `[]T` gives `u8`) and a value an
    /// optional (`u8` for `?T`), as where they convert. Anything else
    /// gives nothing; the argument's check reports a mismatch.
    pub(super) fn unify(&mut self, pattern: Ty, actual: Ty, span: Span) {
        if let Some(k) = self.index(pattern) {
            if self.args[k].is_none() {
                self.args[k] = Some((actual, span));
            }
            return;
        }
        if !pattern.is_generic() {
            return;
        }
        if let Some((elem, n)) = pattern.as_array() {
            if let Some((a, m)) = actual.as_array()
                && m == n
            {
                self.unify(elem, a, span);
            }
        } else if let Some(elem) = pattern.as_slice() {
            if let Some(a) = actual.elem() {
                self.unify(elem, a, span);
            }
        } else if let Some(inner) = pattern.as_optional() {
            match actual.as_optional() {
                Some(a) => self.unify(inner, a, span),
                None => self.unify(inner, actual, span),
            }
        } else if let Some((ok, err)) = pattern.as_result()
            && let Some((a, b)) = actual.as_result()
        {
            self.unify(ok, a, span);
            self.unify(err, b, span);
        }
    }

    /// The type arguments, once all are known.
    pub(super) fn types(&self) -> Vec<Ty> {
        self.args
            .iter()
            .map(|a| a.expect("every type argument is known").0)
            .collect()
    }

    /// The first type parameter not known yet.
    pub(super) fn unknown(&self) -> Option<Ty> {
        self.params
            .iter()
            .zip(&self.args)
            .find(|(_, a)| a.is_none())
            .map(|(&p, _)| p)
    }
}

/// A call from a generic function to a generic function, for the check
/// that instances can't grow without end (see
/// [`Checker::check_generic_recursion`]).
pub(super) struct GenericEdge {
    pub caller: FuncId,
    pub callee: FuncId,
    pub args: Vec<Ty>,
    pub span: Span,
}

impl Checker<'_> {
    /// The type parameters of a generic function, `[T: Ordered + Copy, U]`,
    /// declared in `cx` so its signature and body can name them, with the
    /// traits each declares.
    pub(super) fn declare_generics(
        &mut self,
        cx: &mut FnCx,
        generics: &[ast::GenericParam],
    ) -> (Vec<Ty>, Vec<Vec<Trait>>) {
        let mut out = Vec::new();
        let mut declared = Vec::new();
        for g in generics {
            let name = &g.name.name;
            if primitive(name, self.ptr_bits).is_some() {
                self.error(
                    g.name.span,
                    format!("`{name}` is the name of a built-in type"),
                );
                continue;
            }
            if out
                .iter()
                .any(|p: &Ty| p.as_param().is_some_and(|d| &d.name == name))
            {
                self.error(
                    g.name.span,
                    format!("the type parameter `{name}` is declared twice"),
                );
                continue;
            }
            let mut traits = Vec::new();
            for b in &g.bounds {
                match Trait::from_name(&b.name) {
                    Some(t) => traits.push(t),
                    None => {
                        let mut d = Diagnostic::error(
                            b.span,
                            format!("`{}` is not a built-in trait", b.name),
                        )
                        .with_help(
                            "the bounds are `Eq`, `Ordered`, `Copy`, `Integer`, `Unsigned` and `Signed`; traits declared in Lode come later (docs/generics.md, M7c)",
                        );
                        if primitive(&b.name, self.ptr_bits).is_some() {
                            d = d.with_help(
                                "a value parameter (`[N: usize]`) is not supported by the compiler yet",
                            );
                        }
                        self.diags.push(d);
                    }
                }
            }
            if traits.contains(&Trait::Unsigned) && traits.contains(&Trait::Signed) {
                self.error(
                    g.name.span,
                    format!("`{name}` can't be both `Unsigned` and `Signed`: no type is"),
                );
                traits.retain(|&t| t != Trait::Signed);
            }
            let ty = Ty::new_param(name.clone(), Bounds::new(&traits), self.ptr_bits);
            out.push(ty);
            declared.push(traits);
        }
        cx.type_params = out.clone();
        (out, declared)
    }

    /// The type parameter of `cx`'s function called `name`.
    pub(super) fn type_param(cx: &FnCx, name: &str) -> Option<Ty> {
        cx.type_params
            .iter()
            .copied()
            .find(|p| p.as_param().is_some_and(|d| d.name == name))
    }

    /// Whether `e` names a function: `f` (not hidden by a local) or
    /// `pkg.f`. Brackets after it are then type arguments.
    pub(super) fn names_function(&self, cx: &FnCx, e: &ast::Expr) -> bool {
        match &e.kind {
            ExprKind::Name(n) if cx.lookup(n).is_none() => {
                matches!(self.pkgs[cx.pkg].items.get(n), Some(Item::Func(_)))
            }
            ExprKind::Field(base, member) => match &base.kind {
                ExprKind::Name(p) => self.imported(cx, p).is_some_and(|pkg| {
                    matches!(self.pkgs[pkg].items.get(&member.name), Some(Item::Func(_)))
                }),
                _ => false,
            },
            _ => false,
        }
    }

    /// The type an item in brackets names: a type, or an expression that's
    /// a type's name (`u32`, `geo.Point`).
    pub(super) fn type_arg(&mut self, cx: &mut FnCx, item: &ast::TypeArg) -> Option<Ty> {
        let t = match item {
            ast::TypeArg::Type(t) => t.clone(),
            ast::TypeArg::Expr(e) => match &e.kind {
                ExprKind::Name(n) => ast::TypeExpr::Named(ast::Ident {
                    name: n.clone(),
                    span: e.span,
                }),
                ExprKind::Field(base, member) if matches!(base.kind, ExprKind::Name(_)) => {
                    let ExprKind::Name(p) = &base.kind else {
                        unreachable!("matched")
                    };
                    ast::TypeExpr::Qualified(
                        ast::Ident {
                            name: p.clone(),
                            span: base.span,
                        },
                        member.clone(),
                    )
                }
                _ => {
                    self.error(e.span, "expected a type argument, found an expression");
                    return None;
                }
            },
        };
        let ty = self.resolve_type(cx, &t)?;
        self.check_type_arg(ty, item.span())?;
        Some(ty)
    }

    /// Report a type that can't be a type argument: a view (a generic
    /// function may store a `T`, and views are never stored), or a type
    /// that can't be stored yet.
    pub(super) fn check_type_arg(&mut self, ty: Ty, span: Span) -> Option<()> {
        match ty {
            Ty::Int(_)
            | Ty::Bool
            | Ty::Array(_)
            | Ty::Struct(_)
            | Ty::Enum(_)
            | Ty::Optional(_)
            | Ty::Param(_) => Some(()),
            Ty::Str | Ty::Slice(_) => {
                self.diags.push(
                    Diagnostic::error(span, format!("a type argument can't be a view (`{ty}`)"))
                        .with_help("a generic function may store a value of its type parameter, and views are never stored (docs/generics.md, Views as type arguments)")
                        .with_help("take the view in the signature instead: `xs: []T`"),
                );
                None
            }
            Ty::Ptr(_) | Ty::Unit | Ty::Result(_) => {
                self.error(
                    span,
                    format!("`{ty}` as a type argument is not supported by the compiler yet"),
                );
                None
            }
        }
    }

    /// Check that each type argument of a call of `id` (`name`) satisfies
    /// the bounds of its parameter: the error is at the argument that fixed
    /// it, and names the bound.
    pub(super) fn check_bounds(&mut self, id: FuncId, name: &str, inf: &Inference) -> bool {
        let mut ok = true;
        let params = self.sigs[id].type_params.clone();
        for (k, p) in params.iter().enumerate() {
            let (arg, span) = inf.args[k].expect("every type argument is known");
            if self.check_type_arg(arg, span).is_none() {
                ok = false;
                continue;
            }
            let def = p.as_param().expect("a type parameter");
            let declared = &self.sigs[id].bounds[k];
            let missing = declared.iter().find(|&&t| !arg.satisfies(t)).copied();
            let Some(t) = missing else {
                continue;
            };
            let mut d = Diagnostic::error(
                span,
                format!(
                    "`{arg}` doesn't implement `{t}`, which `{name}` requires of `{}`",
                    def.name
                ),
            );
            if let Some(adef) = arg.as_param() {
                d = d.with_help(format!(
                    "add the bound to `{}`: `[{}: {t}]`",
                    adef.name, adef.name
                ));
            } else if t == Trait::Copy {
                d = d.with_help(format!("`{arg}` holds a value that isn't `Copy`"));
            } else if t == Trait::Ordered && matches!(arg, Ty::Struct(_) | Ty::Enum(_)) {
                d = d.with_help(format!(
                    "`impl Ordered for {arg}` is not supported by the compiler yet (docs/generics.md, M7c)"
                ));
            }
            self.diags.push(d);
            ok = false;
        }
        ok
    }

    /// `a.cmp(b)`, `a.lt(b)`, `a.le(b)`, `a.gt(b)` or `a.ge(b)` on a value
    /// of an `Ordered` type: an integer, `bool`, or a type parameter bounded
    /// by `Ordered`. `b` has `a`'s type. Both are read in place. On a
    /// numeric type, the comparisons give the facts `<` would.
    pub(super) fn ordered_method(
        &mut self,
        cx: &mut FnCx,
        recv: Checked,
        member: &ast::Ident,
        args: &[ast::Expr],
        span: Span,
    ) -> Option<Checked> {
        let ty = recv.ty();
        let method = member.name.as_str();
        if !ty.satisfies(Trait::Ordered) {
            self.diags.push(
                Diagnostic::error(member.span, format!("`{ty}` has no method `{method}`"))
                    .with_help(format!(
                        "add a bound: `[{ty}: Ordered]`, which gives `cmp`, `lt`, `le`, `gt` and `ge`"
                    )),
            );
            return None;
        }
        let [arg] = args else {
            self.error(
                span,
                format!(
                    "`{method}` takes 1 argument (a `{ty}`), but {} were given",
                    args.len()
                ),
            );
            return None;
        };
        let other = self.expr(cx, arg, Some(ty))?;
        let other = self.coerce(cx, other, ty, arg.span)?;
        let op = match method {
            "lt" => CmpOp::Lt,
            "le" => CmpOp::Le,
            "gt" => CmpOp::Gt,
            "ge" => CmpOp::Ge,
            _ => {
                return Some(Checked::new(
                    TExprKind::Compare(Box::new(recv.expr), Box::new(other.expr)),
                    Ty::ordering(),
                    None,
                ));
            }
        };
        Some(self.comparison(cx, op, recv, other))
    }

    /// The values of type parameters that terms can be: the integer locals
    /// of type `ty`.
    fn param_terms(cx: &FnCx, ty: Ty) -> Vec<Term> {
        (0..cx.locals.len())
            .filter(|&l| cx.locals[l].ty == ty && !cx.failed.contains(&l))
            .map(Term::Local)
            .collect()
    }

    /// Whether a value `lin` (a term plus a constant) is at most (`upper`)
    /// or at least a value of type `ty`, a type parameter, by a relation
    /// with one of the function's locals of that type.
    pub(super) fn bounded_by_param(cx: &FnCx, ty: Ty, lin: Linear, upper: bool) -> bool {
        Self::param_terms(cx, ty).into_iter().any(|u| {
            let u = Linear::of(u);
            let c = if upper {
                cx.env.diff_bound(lin, u)
            } else {
                cx.env.diff_bound(u, lin)
            };
            c.is_some_and(|c| c <= 0)
        })
    }

    /// Whether a value in `r` (with the term `lin`, if any) fits in the
    /// type parameter `ty`: each end is within the values every type the
    /// bound admits holds, or bounded by a value of type `ty` through a
    /// relation. `side` gives the other reasons an end holds (see
    /// [`Checker::arith`]).
    pub(super) fn fits_param(
        cx: &FnCx,
        ty: Ty,
        n: Num,
        r: Range,
        lin: Option<Linear>,
        side: (bool, bool),
    ) -> bool {
        let upper = r.hi <= n.fits.hi
            || side.1
            || lin.is_some_and(|l| Self::bounded_by_param(cx, ty, l, true));
        let lower = r.lo >= n.fits.lo
            || side.0
            || lin.is_some_and(|l| Self::bounded_by_param(cx, ty, l, false));
        upper && lower
    }

    /// `T(x)` for a type parameter `T` with a numeric bound: the integer
    /// `x`, proven to fit in every type `T` can be.
    pub(super) fn param_conversion(
        &mut self,
        cx: &mut FnCx,
        ty: Ty,
        args: &[ast::Expr],
        span: Span,
    ) -> Option<Checked> {
        let Some(n) = num(ty) else {
            self.diags.push(
                Diagnostic::error(
                    span,
                    format!(
                        "`{ty}(...)` converts an integer, but `{ty}` may not be an integer type"
                    ),
                )
                .with_help(format!("add a numeric bound: `[{ty}: Integer]`")),
            );
            return None;
        };
        let [arg] = args else {
            self.error(span, format!("`{ty}(...)` converts exactly one value"));
            return None;
        };
        let c = self.expr(cx, arg, Some(ty))?;
        if c.ty() == ty {
            return Some(c);
        }
        if num(c.ty()).is_none() {
            self.error(arg.span, format!("cannot convert `{}` to `{ty}`", c.ty()));
            return None;
        }
        let r = c.int_range();
        if !Self::fits_param(cx, ty, n, r, c.term, (false, false)) {
            let mut d = Diagnostic::error(
                span,
                format!("cannot prove that this `{}` value fits in `{ty}`", c.ty()),
            )
            .with_help(format!("the value can be {}", show_range(r, c.ty())));
            if let Some(h) = param_help(ty) {
                d = d.with_help(h);
            }
            self.diags.push(d);
            return None;
        }
        let term = c.term;
        let mut out = Checked::new(TExprKind::Convert(Box::new(c.expr)), ty, Some(r));
        out.term = term;
        Some(out)
    }

    /// A value is kept (stored in a variable, a field, an element or an
    /// optional, returned, or passed `sink`): if its type isn't `Copy` and
    /// it's read from a place, it's moved out of it. Only a `let` or `var`,
    /// or a `sink` parameter, can be moved from, whole: the variable can't
    /// be used again until it's assigned. Copying an element, a read-only
    /// parameter or an `inout` one needs `Copy` (docs/generics.md, Copy and
    /// moves). A value that isn't read from a place is a new value, whose
    /// parts were kept when it was built.
    pub(super) fn consume(&mut self, cx: &mut FnCx, e: &TExpr, span: Span) -> Option<()> {
        if e.ty.is_copy() {
            return Some(());
        }
        let Some((local, through_index)) = place_root(e) else {
            return Some(());
        };
        let mut missing = Vec::new();
        e.ty.params(&mut missing);
        let param = missing.into_iter().find(|p| !p.is_copy()).unwrap_or(e.ty);
        let text = place_text(cx, e).unwrap_or_else(|| cx.locals[local].name.clone());
        let name = cx.locals[local].name.clone();
        let add_copy = format!("add the bound `Copy` to copy it: `[{param}: Copy]`");
        if through_index {
            self.diags.push(
                Diagnostic::error(
                    span,
                    format!("this copies `{text}`, a `{}`, but `{param}` isn't `Copy`", e.ty),
                )
                .with_help(add_copy)
                .with_help("an element can't be moved out of its array; read it in place instead (compare it, call a method on it, or pass it to a parameter that isn't `sink`)"),
            );
            return None;
        }
        match cx.locals[local].convention {
            None | Some(Convention::Sink) => {
                if cx.defer_depth > 0 && local < cx.defer_floor {
                    self.diags.push(
                        Diagnostic::error(
                            span,
                            format!(
                                "a `defer` block can't move `{name}`, which is declared outside it"
                            ),
                        )
                        .with_help(add_copy),
                    );
                    return None;
                }
                cx.env.declare_uninit(local);
                cx.moved.insert(local);
                Some(())
            }
            Some(conv) => {
                let (what, help) = match conv {
                    Convention::Let => (
                        "a read-only parameter",
                        format!(
                            "or take it as `sink {name}: {}`, which moves the caller's value in",
                            cx.locals[local].ty
                        ),
                    ),
                    _ => (
                        "a parameter the caller keeps",
                        "a value can't be moved out of an `inout` or `set` parameter".to_owned(),
                    ),
                };
                self.diags.push(
                    Diagnostic::error(
                        span,
                        format!("this copies `{text}`, {what}, but `{param}` isn't `Copy`"),
                    )
                    .with_help(add_copy)
                    .with_help(help),
                );
                None
            }
        }
    }

    /// Report a use of `local`, which may have been moved (it's
    /// unassigned on some path, and a move made it so).
    pub(super) fn moved_error(&mut self, cx: &FnCx, local: LocalId, span: Span) -> bool {
        if !cx.moved.contains(&local) {
            return false;
        }
        let name = &cx.locals[local].name;
        let ty = cx.locals[local].ty;
        let mut missing = Vec::new();
        ty.params(&mut missing);
        let param = missing.into_iter().find(|p| !p.is_copy()).unwrap_or(ty);
        self.diags.push(
            Diagnostic::error(
                span,
                format!("`{name}` is used after it was moved (on some path to here)"),
            )
            .with_help(format!(
                "a `{ty}` isn't copied, since `{param}` isn't `Copy`: keeping it moves it out of `{name}`"
            ))
            .with_help(format!(
                "add the bound `[{param}: Copy]`, or use `{name}` before it's moved"
            )),
        );
        true
    }

    /// Report the calls that would make instances of generic functions
    /// without end: in a cycle of calls between generic functions, every
    /// type argument that mentions the caller's type parameters must be one
    /// of them, unchanged (`f[T]` may call `g[T]` and `g[U]` call `f[U]`,
    /// but not `f[?U]`).
    pub(super) fn check_generic_recursion(&mut self) {
        let mut graph: HashMap<FuncId, Vec<FuncId>> = HashMap::new();
        for e in &self.generic_calls {
            graph.entry(e.caller).or_default().push(e.callee);
        }
        let reaches = |from: FuncId, to: FuncId| {
            let mut seen = HashSet::new();
            let mut work = vec![from];
            while let Some(f) = work.pop() {
                if f == to {
                    return true;
                }
                if seen.insert(f) {
                    work.extend(graph.get(&f).into_iter().flatten().copied());
                }
            }
            false
        };
        let mut diags = Vec::new();
        for e in &self.generic_calls {
            let grows = e
                .args
                .iter()
                .any(|a| a.is_generic() && a.as_param().is_none());
            if grows && reaches(e.callee, e.caller) {
                let callee = &self.sigs[e.callee].name;
                let args: Vec<String> = e.args.iter().map(Ty::to_string).collect();
                diags.push(
                    Diagnostic::error(
                        e.span,
                        format!(
                            "this calls `{callee}[{}]`, which calls back here: its instances would never end",
                            args.join(", ")
                        ),
                    )
                    .with_help(
                        "generic functions that call each other in a cycle must pass their type parameters unchanged",
                    ),
                );
            }
        }
        self.diags.extend(diags);
    }
}

/// The variable a place is part of, and whether an index is on the way: a
/// local, a field, an element or a payload of one.
fn place_root(e: &TExpr) -> Option<(LocalId, bool)> {
    match &e.kind {
        TExprKind::Local(l) => Some((*l, false)),
        TExprKind::Field(base, _) | TExprKind::Payload(base, ..) => place_root(base),
        TExprKind::Index(base, _) => place_root(base).map(|(l, _)| (l, true)),
        _ => None,
    }
}
