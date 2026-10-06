//! Refinements: facts in signatures, struct fields and named types
//! (docs/safety.md, Refinements in types).
//!
//! A refinement is comparisons joined with `&&`, each between two forms of
//! the fact language: constants, and at most two values that the checker
//! can name (a parameter, its `.len` or an integer field of it, another
//! field of the same struct, a value parameter, and the refined value
//! itself: `result`, `self`, or the field). It's resolved once, where it's
//! declared, into [`Atom`]s over [`Leaf`]s. Where it's used, each leaf is
//! mapped to a [`Val`]: a term (with the facts the checker knows about
//! it), or a value known only by its range. Then the refinement is proven
//! ([`holds`]), assumed ([`Checker::assume`]), or gives facts about the
//! refined value ([`value_facts`]).

use std::rc::Rc;

use crate::ast::{self, BinOp, Convention, ExprKind, UnOp};
use crate::diag::Diagnostic;
use crate::source::Span;
use crate::types::{Len, Range, Ty};

use super::eval::Value;
use super::expr::{Checked, flat_size, place_term};
use super::facts::{Fact, Form, Linear, Term};
use super::tree::{CmpOp, LocalId, TExpr, TExprKind};
use super::{
    Checker, ConstVal, FnCx, Item, RefinedState, RefinedType, read_range, term_full_by, type_range,
};

/// A value a refinement names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Leaf {
    /// The refined value: `result` of a function, `self` of a named
    /// refinement, or the field whose refinement it is.
    Value,
    /// The value of parameter `k` (a method's `self` is 0).
    Param(usize),
    /// The length of parameter `k`, a slice or a `str`.
    Len(usize),
    /// An integer field of parameter `k`, a struct, numbered as in
    /// [`Term::Field`].
    PField(usize, u32),
    /// Field `j` (in declaration order) of the struct whose field is
    /// refined.
    Field(usize),
    /// A value parameter (`N` in `[N: usize]`).
    VParam(Ty),
}

/// A sum of leaves times constants, plus a constant.
#[derive(Clone, Debug, Default)]
pub(super) struct Lin {
    pub(super) parts: Vec<(Leaf, i128)>,
    pub(super) k: i128,
}

impl Lin {
    fn constant(k: i128) -> Lin {
        Lin {
            parts: Vec::new(),
            k,
        }
    }

    fn leaf(l: Leaf) -> Lin {
        Lin {
            parts: vec![(l, 1)],
            k: 0,
        }
    }

    fn add(mut self, other: Lin, sign: i128) -> Option<Lin> {
        self.k = self.k.checked_add(other.k.checked_mul(sign)?)?;
        for (l, m) in other.parts {
            let m = m.checked_mul(sign)?;
            match self.parts.iter_mut().find(|p| p.0 == l) {
                Some(p) => p.1 = p.1.checked_add(m)?,
                None => self.parts.push((l, m)),
            }
        }
        self.parts.retain(|p| p.1 != 0);
        Some(self)
    }

    fn scale(mut self, m: i128) -> Option<Lin> {
        self.k = self.k.checked_mul(m)?;
        for p in &mut self.parts {
            p.1 = p.1.checked_mul(m)?;
        }
        self.parts.retain(|p| p.1 != 0);
        Some(self)
    }
}

/// One comparison of a refinement.
#[derive(Clone, Debug)]
pub(super) struct Atom {
    pub(super) op: CmpOp,
    pub(super) lhs: Lin,
    pub(super) rhs: Lin,
    /// The comparison in the source, for messages.
    pub(super) span: Span,
}

impl Atom {
    /// `lhs - rhs`, which the comparison is about.
    fn diff(&self) -> Lin {
        self.lhs
            .clone()
            .add(self.rhs.clone(), -1)
            .unwrap_or_default()
    }

    /// The atom with every leaf `from` replaced by `to`.
    fn subst(&self, from: Leaf, to: Leaf) -> Atom {
        let swap = |lin: &Lin| Lin {
            parts: lin
                .parts
                .iter()
                .map(|&(l, m)| (if l == from { to } else { l }, m))
                .collect(),
            k: lin.k,
        };
        Atom {
            op: self.op,
            lhs: swap(&self.lhs),
            rhs: swap(&self.rhs),
            span: self.span,
        }
    }

    fn mentions(&self, leaf: Leaf) -> bool {
        self.lhs
            .parts
            .iter()
            .chain(&self.rhs.parts)
            .any(|p| p.0 == leaf)
    }

    /// The facts `D <= c` it states, each as a sum of leaves with the
    /// constant `c`: one for `<`, `<=`, `>`, `>=`, two for `==`, none for
    /// `!=` (see [`Atom::excluded`]).
    fn bounds(&self) -> Vec<(Lin, i128)> {
        let d = self.diff();
        let neg = d.clone().scale(-1).unwrap_or_default();
        // `d op 0` with d = lhs - rhs; a bound `X <= c` is `X - c <= 0`,
        // kept as the parts of X and c.
        let le = |x: Lin, c: i128| -> Option<(Lin, i128)> {
            let c = c.checked_sub(x.k)?;
            Some((Lin { k: 0, ..x }, c))
        };
        let out = match self.op {
            CmpOp::Lt => vec![le(d, -1)],
            CmpOp::Le => vec![le(d, 0)],
            CmpOp::Gt => vec![le(neg, -1)],
            CmpOp::Ge => vec![le(neg, 0)],
            CmpOp::Eq => vec![le(d, 0), le(neg, 0)],
            CmpOp::Ne => Vec::new(),
        };
        out.into_iter().flatten().collect()
    }

    /// For `!=`: the sum of leaves and the constant it's not.
    fn excluded(&self) -> Option<(Lin, i128)> {
        if self.op != CmpOp::Ne {
            return None;
        }
        let d = self.diff();
        Some((Lin { k: 0, ..d.clone() }, d.k.checked_neg()?))
    }
}

/// A refinement: the comparisons that must all hold.
#[derive(Clone, Debug)]
pub(super) struct Refine {
    pub(super) atoms: Vec<Atom>,
}

impl Refine {
    /// The refinement with every leaf `from` replaced by `to`.
    pub(super) fn subst(&self, from: Leaf, to: Leaf) -> Refine {
        Refine {
            atoms: self.atoms.iter().map(|a| a.subst(from, to)).collect(),
        }
    }

    pub(super) fn mentions(&self, leaf: Leaf) -> bool {
        self.atoms.iter().any(|a| a.mentions(leaf))
    }

    /// Both refinements.
    pub(super) fn and(a: Option<Rc<Refine>>, b: Option<Rc<Refine>>) -> Option<Rc<Refine>> {
        match (a, b) {
            (Some(a), Some(b)) => {
                let mut atoms = a.atoms.clone();
                atoms.extend(b.atoms.iter().cloned());
                Some(Rc::new(Refine { atoms }))
            }
            (a, b) => a.or(b),
        }
    }
}

/// What a refinement's value is known as, where it's used.
#[derive(Clone, Debug)]
pub(super) struct Val {
    /// The value as a form of terms, when it is one.
    pub(super) form: Option<Form>,
    /// Its range (for a form, the range its terms give).
    pub(super) range: Range,
    /// Bounds known for a value that isn't a form.
    pub(super) known: Vec<Known>,
}

/// `sign * v + form <= c` for a value `v`, `sign` being 1 or -1: what a
/// call's result refinement says about its value, in terms of the caller.
#[derive(Clone, Copy, Debug)]
pub(super) struct Known {
    pub(super) sign: i128,
    pub(super) form: Form,
    pub(super) c: i128,
}

impl Val {
    pub(super) fn konst(v: i128) -> Val {
        Val {
            form: Some(Form::constant(v)),
            range: Range::exact(v),
            known: Vec::new(),
        }
    }

    pub(super) fn term(cx: &FnCx, t: Term) -> Val {
        Val {
            form: Some(Form::of(Linear::of(t))),
            range: read_range(cx, t).unwrap_or_else(|| full(cx, t)),
            known: Vec::new(),
        }
    }

    /// A value known only by its range.
    pub(super) fn opaque(range: Range) -> Val {
        Val {
            form: None,
            range,
            known: Vec::new(),
        }
    }

    pub(super) fn of(c: &Checked) -> Val {
        let mut known = c.known.clone();
        if let Some(up) = c.upper {
            known.push(Known {
                sign: 1,
                form: Form::of(Linear::of(up.term))
                    .scale(-1)
                    .unwrap_or(Form::constant(0)),
                c: up.offset,
            });
        }
        Val {
            form: c.form(),
            range: c.int_range(),
            known,
        }
    }
}

/// The values a term's type allows.
fn full(cx: &FnCx, t: Term) -> Range {
    term_full_by(|l| cx.locals[l].ty, t)
}

/// The range of a term where it's read.
fn term_range(cx: &FnCx, t: Term) -> Range {
    read_range(cx, t).unwrap_or_else(|| full(cx, t))
}

fn add_term(terms: &mut Vec<(Term, i128)>, t: Term, m: i128) -> Option<()> {
    match terms.iter_mut().find(|p| p.0 == t) {
        Some(p) => p.1 = p.1.checked_add(m)?,
        None => terms.push((t, m)),
    }
    Some(())
}

/// The largest value of `sum m * t` the facts give: from the terms'
/// ranges, and for two terms, from a relation or a sum about them.
fn terms_hi(cx: &FnCx, terms: &[(Term, i128)]) -> Option<i128> {
    let mut by_ranges: i128 = 0;
    for &(t, m) in terms {
        let r = term_range(cx, t);
        let end = if m > 0 { r.hi } else { r.lo };
        by_ranges = by_ranges.checked_add(m.checked_mul(end)?)?;
    }
    if let [(a, p), (b, q)] = *terms {
        let f = Form::of(Linear::of(a))
            .scale(p)
            .zip(Form::of(Linear::of(b)).scale(q))
            .and_then(|(x, y)| x.plus(y));
        if let Some(f) = f
            && let (_, Some(hi)) = cx.env.form_bounds(f)
        {
            return Some(hi.min(by_ranges));
        }
    }
    Some(by_ranges)
}

/// The largest value of `k + sum m * v` the facts give (docs/safety.md,
/// Refinements in types): each value that's a form is its terms, bounded
/// by [`terms_hi`]; any other value by its range, or, when it's the only
/// one and its coefficient is 1 or -1, by a bound known for it.
pub(super) fn sum_hi(cx: &FnCx, parts: &[(Val, i128)], k: i128) -> Option<i128> {
    let mut terms: Vec<(Term, i128)> = Vec::new();
    let mut opaque: Vec<(&Val, i128)> = Vec::new();
    let mut k = k;
    for (v, m) in parts {
        let m = *m;
        if m == 0 {
            continue;
        }
        match v.form {
            Some(f) => {
                k = k.checked_add(f.k.checked_mul(m)?)?;
                for (t, c) in f.terms() {
                    add_term(&mut terms, t, c.checked_mul(m)?)?;
                }
            }
            None => opaque.push((v, m)),
        }
    }
    terms.retain(|p| p.1 != 0);
    let mut rest: i128 = 0;
    for &(v, m) in &opaque {
        let end = if m > 0 { v.range.hi } else { v.range.lo };
        rest = rest.checked_add(m.checked_mul(end)?)?;
    }
    let mut best = terms_hi(cx, &terms)
        .and_then(|t| t.checked_add(rest))
        .and_then(|t| t.checked_add(k));
    if let [(v, m)] = opaque[..]
        && (m == 1 || m == -1)
    {
        for known in v.known.iter().filter(|kn| kn.sign == m) {
            // m*v <= c - F, so the sum is at most k + c + hi(terms - F).
            let mut t2 = terms.clone();
            let mut ok = Some(());
            for (t, c) in known.form.terms() {
                ok = ok.and_then(|()| add_term(&mut t2, t, -c));
            }
            t2.retain(|p| p.1 != 0);
            let cand = ok
                .and_then(|()| terms_hi(cx, &t2))
                .and_then(|h| h.checked_add(known.c))
                .and_then(|h| h.checked_sub(known.form.k))
                .and_then(|h| h.checked_add(k));
            if let Some(c) = cand {
                best = Some(best.map_or(c, |b| b.min(c)));
            }
        }
    }
    best
}

/// The range of `k + sum m * v`.
pub(super) fn sum_range(cx: &FnCx, parts: &[(Val, i128)], k: i128) -> Option<Range> {
    let hi = sum_hi(cx, parts, k)?;
    let neg: Vec<(Val, i128)> = parts.iter().map(|(v, m)| (v.clone(), -m)).collect();
    let lo = sum_hi(cx, &neg, k.checked_neg()?)?.checked_neg()?;
    Some(Range { lo, hi })
}

/// The values of a sum's leaves, `None` if one can't be named here.
fn mapped(lin: &Lin, map: &dyn Fn(Leaf) -> Option<Val>) -> Option<Vec<(Val, i128)>> {
    lin.parts.iter().map(|&(l, m)| Some((map(l)?, m))).collect()
}

/// Whether the comparison holds, with each leaf mapped by `map`: for `x
/// <= y`, the largest value of `x - y` the facts give (see [`sum_hi`]) is
/// at most 0; for `x != y`, `x - y` can't be 0 by its range, or it's a
/// term (plus a constant) known not to be that value.
pub(super) fn holds(cx: &FnCx, atom: &Atom, map: &dyn Fn(Leaf) -> Option<Val>) -> bool {
    if let Some((lin, c)) = atom.excluded() {
        let Some(parts) = mapped(&lin, map) else {
            return false;
        };
        if let Some(r) = sum_range(cx, &parts, 0)
            && !r.contains(c)
        {
            return true;
        }
        // One term, times 1 or -1, plus a constant.
        let mut terms: Vec<(Term, i128)> = Vec::new();
        let mut k = 0i128;
        for (v, m) in &parts {
            let Some(f) = v.form else {
                return false;
            };
            let Some(fk) = f.k.checked_mul(*m).and_then(|x| k.checked_add(x)) else {
                return false;
            };
            k = fk;
            for (t, cf) in f.terms() {
                if cf
                    .checked_mul(*m)
                    .and_then(|x| add_term(&mut terms, t, x).map(|()| x))
                    .is_none()
                {
                    return false;
                }
            }
        }
        terms.retain(|p| p.1 != 0);
        return match terms[..] {
            [(t, m)] if m == 1 || m == -1 => {
                c.checked_sub(k).is_some_and(|v| cx.env.excludes(t, v * m))
            }
            _ => false,
        };
    }
    atom.bounds().into_iter().all(|(lin, c)| {
        mapped(&lin, map)
            .and_then(|parts| sum_hi(cx, &parts, 0))
            .is_some_and(|hi| hi <= c)
    })
}

/// The facts of `lin <= c` (or `lin != c`) about terms: the sum's values
/// that aren't forms are replaced by the end of their range that keeps it
/// true, and what's left, at most two terms, is a range, a relation or a
/// sum (as for a comparison, docs/safety.md, Sums).
fn term_facts(
    cx: &FnCx,
    lin: &Lin,
    c: i128,
    ne: bool,
    map: &dyn Fn(Leaf) -> Option<Val>,
) -> Vec<Fact> {
    let Some(parts) = mapped(lin, map) else {
        return Vec::new();
    };
    let mut form = Form::constant(0);
    let mut c = c;
    for (v, m) in &parts {
        match v.form {
            Some(f) => match f.scale(*m).and_then(|f| form.plus(f)) {
                Some(f) => form = f,
                None => return Vec::new(),
            },
            None if ne => return Vec::new(),
            None => {
                // m*v >= its smallest value.
                let lo = if *m > 0 { v.range.lo } else { v.range.hi };
                match m.checked_mul(lo).and_then(|x| c.checked_sub(x)) {
                    Some(x) => c = x,
                    None => return Vec::new(),
                }
            }
        }
    }
    let terms: Vec<(Term, i128)> = form.terms().collect();
    if ne {
        let [(t, m)] = terms[..] else {
            return Vec::new();
        };
        if m != 1 && m != -1 {
            return Vec::new();
        }
        let Some(v) = c.checked_sub(form.k).map(|v| v * m) else {
            return Vec::new();
        };
        let r = term_range(cx, t);
        let f = full(cx, t);
        return if v == r.lo && r.lo < r.hi {
            vec![Fact::Narrow {
                term: t,
                bound: Range {
                    lo: v + 1,
                    hi: r.hi,
                },
                full: f,
            }]
        } else if v == r.hi && r.lo < r.hi {
            vec![Fact::Narrow {
                term: t,
                bound: Range {
                    lo: r.lo,
                    hi: v - 1,
                },
                full: f,
            }]
        } else {
            vec![Fact::Hole { term: t, value: v }]
        };
    }
    let f = match terms[..] {
        [(t, _)] => full(cx, t),
        _ => Range::exact(0),
    };
    form.le(c, f)
}

/// The facts a refinement states about terms, its leaves mapped by `map`.
pub(super) fn facts_of(cx: &FnCx, r: &Refine, map: &dyn Fn(Leaf) -> Option<Val>) -> Vec<Fact> {
    let mut out = Vec::new();
    for atom in &r.atoms {
        for (lin, c) in atom.bounds() {
            out.extend(term_facts(cx, &lin, c, false, map));
        }
        if let Some((lin, c)) = atom.excluded() {
            out.extend(term_facts(cx, &lin, c, true, map));
        }
    }
    out
}

/// What a refinement says about its value ([`Leaf::Value`]), the other
/// leaves mapped by `map`: a range, and bounds relative to terms.
pub(super) fn value_facts(
    cx: &FnCx,
    r: &Refine,
    map: &dyn Fn(Leaf) -> Option<Val>,
) -> (Option<Range>, Vec<Known>) {
    let mut range: Option<Range> = None;
    let mut known = Vec::new();
    for atom in &r.atoms {
        for (lin, c) in atom.bounds() {
            let r: i128 = lin
                .parts
                .iter()
                .filter(|p| p.0 == Leaf::Value)
                .map(|p| p.1)
                .sum();
            if r == 0 {
                continue;
            }
            let rest = Lin {
                parts: lin
                    .parts
                    .iter()
                    .copied()
                    .filter(|p| p.0 != Leaf::Value)
                    .collect(),
                k: 0,
            };
            let Some(parts) = mapped(&rest, map) else {
                continue;
            };
            // r*v + rest <= c: r*v <= c - lo(rest).
            let neg: Vec<(Val, i128)> = parts.iter().map(|(v, m)| (v.clone(), -m)).collect();
            if let Some(lo) = sum_hi(cx, &neg, 0).and_then(i128::checked_neg)
                && let Some(b) = c.checked_sub(lo)
            {
                let bound = if r > 0 {
                    Range {
                        lo: i128::MIN,
                        hi: b.div_euclid(r),
                    }
                } else {
                    Range {
                        lo: -(b.div_euclid(-r)),
                        hi: i128::MAX,
                    }
                };
                range = Some(match range {
                    Some(x) => x.intersect(bound).unwrap_or(bound),
                    None => bound,
                });
            }
            if r == 1 || r == -1 {
                // Relative to the terms: the other values by their ranges.
                let mut form = Form::constant(0);
                let mut c = c;
                let mut ok = true;
                for (v, m) in &parts {
                    match v.form {
                        Some(f) => match f.scale(*m).and_then(|f| form.plus(f)) {
                            Some(f) => form = f,
                            None => ok = false,
                        },
                        None => {
                            let lo = if *m > 0 { v.range.lo } else { v.range.hi };
                            match m.checked_mul(lo).and_then(|x| c.checked_sub(x)) {
                                Some(x) => c = x,
                                None => ok = false,
                            }
                        }
                    }
                }
                if ok && form.term_count() > 0 {
                    known.push(Known { sign: r, form, c });
                }
            }
        }
    }
    (range, known)
}

/// The value of a generic argument for a value parameter: a number, or the
/// local holding the caller's own value parameter.
pub(super) fn value_arg(cx: &FnCx, t: Ty) -> Option<Val> {
    if let Some(v) = t.as_value() {
        return Some(Val::konst(v));
    }
    let l = cx.value_local(t)?;
    Some(Val::term(cx, Term::Local(l)))
}

/// Where a refinement is declared: what its names mean.
pub(super) struct Scope<'s> {
    /// The parameters (type, convention, name) it may name, the first
    /// `visible` of them, and the refined one, if any.
    pub(super) params: &'s [(Ty, Convention, String)],
    pub(super) visible: usize,
    pub(super) own: Option<usize>,
    /// For a result's refinement, the result's type: `result` names it.
    pub(super) result: Option<Ty>,
    /// For a field's: the struct's fields and the refined one, which the
    /// field's own name names (as [`Leaf::Value`]).
    pub(super) fields: Option<(&'s [crate::types::Field], usize)>,
    /// For a named refinement: the type `self` has.
    pub(super) self_ty: Option<Ty>,
}

/// Whether `name` names something in a refinement's scope (not a constant).
fn scope_has(cx: &FnCx, scope: &Scope, name: &str) -> bool {
    (scope.result.is_some() && name == "result")
        || (scope.self_ty.is_some() && name == "self")
        || scope
            .fields
            .is_some_and(|(fs, _)| fs.iter().any(|f| f.name == name))
        || scope.params.iter().any(|p| p.2 == name)
        || cx
            .type_params
            .iter()
            .any(|p| p.value_param().is_some() && p.to_string() == name)
}

/// A place in a refinement before it's a leaf: a parameter, the value, or a
/// field of the struct, with fields after it, and its type.
#[derive(Clone, Copy)]
enum Root {
    Param(usize),
    Value,
    Field(usize),
    VParam(Ty),
}

impl Checker<'_> {
    /// Resolve the refinement `e`, declared in `scope`: comparisons joined
    /// with `&&`, in the fact language. Errors are reported.
    pub(super) fn refinement(
        &mut self,
        cx: &mut FnCx,
        e: &ast::Expr,
        scope: &Scope,
    ) -> Option<Rc<Refine>> {
        let mut atoms = Vec::new();
        self.conjuncts(cx, e, scope, &mut atoms)?;
        Some(Rc::new(Refine { atoms }))
    }

    fn conjuncts(
        &mut self,
        cx: &mut FnCx,
        e: &ast::Expr,
        scope: &Scope,
        out: &mut Vec<Atom>,
    ) -> Option<()> {
        match &e.kind {
            ExprKind::Paren(inner) => self.conjuncts(cx, inner, scope, out),
            ExprKind::Binary(BinOp::And, a, b) => {
                let x = self.conjuncts(cx, a, scope, out);
                let y = self.conjuncts(cx, b, scope, out);
                x.and(y)
            }
            ExprKind::Binary(
                op @ (BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne),
                a,
                b,
            ) => {
                let l = self.refine_lin(cx, a, scope);
                let r = self.refine_lin(cx, b, scope);
                let (lhs, rhs) = (l?, r?);
                let op = match op {
                    BinOp::Lt => CmpOp::Lt,
                    BinOp::Le => CmpOp::Le,
                    BinOp::Gt => CmpOp::Gt,
                    BinOp::Ge => CmpOp::Ge,
                    BinOp::Eq => CmpOp::Eq,
                    _ => CmpOp::Ne,
                };
                let atom = Atom {
                    op,
                    lhs,
                    rhs,
                    span: e.span,
                };
                let d = atom.diff();
                if d.parts.len() > 2 {
                    self.diags.push(
                        Diagnostic::error(e.span, "this refinement relates more than two values")
                            .with_help("the checker's facts relate at most two values, as in `i < buf.len` or `a + b <= 100` (docs/safety.md, The fact language)"),
                    );
                    return None;
                }
                if d.parts.is_empty() {
                    // Constants only: true or false now.
                    let v = d.k;
                    let ok = match op {
                        CmpOp::Lt => v < 0,
                        CmpOp::Le => v <= 0,
                        CmpOp::Gt => v > 0,
                        CmpOp::Ge => v >= 0,
                        CmpOp::Eq => v == 0,
                        CmpOp::Ne => v != 0,
                    };
                    if !ok {
                        self.error(e.span, "this refinement is never true");
                        return None;
                    }
                    return Some(());
                }
                out.push(atom);
                Some(())
            }
            _ => {
                self.diags.push(
                    Diagnostic::error(e.span, "a refinement is comparisons joined with `&&`")
                        .with_help(
                            "as in `i < buf.len && i >= 1`: `<`, `<=`, `>`, `>=`, `==` or `!=`",
                        ),
                );
                None
            }
        }
    }

    /// An integer sum in a refinement: constants, names, `.len`, fields,
    /// `+`, `-`, and `*` by a constant.
    fn refine_lin(&mut self, cx: &mut FnCx, e: &ast::Expr, scope: &Scope) -> Option<Lin> {
        let outside = |ck: &mut Self, what: &str| {
            ck.diags.push(
                Diagnostic::error(e.span, format!("{what} can't be in a refinement"))
                    .with_help("a refinement uses integer constants, the parameters before it (and their `.len` and integer fields), `result`, `self`, value parameters, `+`, `-`, and `*` by a constant (docs/safety.md, Refinements in types)"),
            );
            None
        };
        match &e.kind {
            ExprKind::Int(v) => match i128::try_from(*v) {
                Ok(v) => Some(Lin::constant(v)),
                Err(_) => outside(self, "this number"),
            },
            ExprKind::Char(c) => Some(Lin::constant(i128::from(*c))),
            ExprKind::Paren(inner) => self.refine_lin(cx, inner, scope),
            ExprKind::Unary(UnOp::Neg, inner) => self.refine_lin(cx, inner, scope)?.scale(-1),
            ExprKind::Binary(op @ (BinOp::Add | BinOp::Sub), a, b) => {
                let x = self.refine_lin(cx, a, scope);
                let y = self.refine_lin(cx, b, scope);
                let sign = if *op == BinOp::Add { 1 } else { -1 };
                x?.add(y?, sign)
            }
            ExprKind::Binary(BinOp::Mul, a, b) => {
                let x = self.refine_lin(cx, a, scope)?;
                let y = self.refine_lin(cx, b, scope)?;
                match (x.parts.is_empty(), y.parts.is_empty()) {
                    (true, _) => y.scale(x.k),
                    (_, true) => x.scale(y.k),
                    _ => outside(self, "a product of two values"),
                }
            }
            ExprKind::Binary(op, ..) => outside(self, &format!("`{}`", op.as_str())),
            ExprKind::Name(_) | ExprKind::Field(..) => {
                // A name the refinement's scope has hides a constant.
                let mut root = e;
                while let ExprKind::Field(base, _) | ExprKind::Paren(base) = &root.kind {
                    root = base;
                }
                let named = match &root.kind {
                    ExprKind::Name(n) => scope_has(cx, scope, n),
                    _ => false,
                };
                if !named && let Some(v) = self.refine_const(cx, e) {
                    return Some(Lin::constant(v));
                }
                self.refine_name(cx, e, scope)
            }
            ExprKind::Call(..) => outside(self, "a call"),
            ExprKind::Index(..) | ExprKind::Slice(..) => outside(self, "an element"),
            _ => outside(self, "this expression"),
        }
    }

    /// The value of a constant named in a refinement (`CAP`, `pkg.MAX`),
    /// if `e` names one.
    fn refine_const(&mut self, cx: &mut FnCx, e: &ast::Expr) -> Option<i128> {
        let id = match &e.kind {
            ExprKind::Name(name) if cx.lookup(name).is_none() => {
                match self.pkgs[cx.pkg].items.get(name) {
                    Some(&Item::Const(id)) => id,
                    _ => return None,
                }
            }
            ExprKind::Field(base, member) => {
                let ExprKind::Name(pkg_name) = &base.kind else {
                    return None;
                };
                let pkg = self.imported(cx, pkg_name)?;
                match self.pkgs[pkg].items.get(&member.name) {
                    Some(&Item::Const(id)) if pkg == cx.pkg || self.consts[id].decl.is_pub => id,
                    _ => return None,
                }
            }
            _ => return None,
        };
        match self.const_value(id)? {
            ConstVal::Untyped(v) | ConstVal::Typed(_, v) => Some(v),
            _ => None,
        }
    }

    /// A name, `.len` or a field in a refinement.
    fn refine_name(&mut self, cx: &mut FnCx, e: &ast::Expr, scope: &Scope) -> Option<Lin> {
        // `x.len` of a view or an array (not a field named `len`).
        if let ExprKind::Field(base, member) = &e.kind
            && member.name == "len"
        {
            let (_, bty, _) = self.refine_path(cx, base, scope)?;
            if bty.is_view() || bty.as_array().is_some() {
                return self.refine_len(cx, e, scope);
            }
        }
        let (root, ty, flat) = self.refine_path(cx, e, scope)?;
        if type_range(ty).is_none() {
            self.diags.push(
                Diagnostic::error(
                    e.span,
                    format!("a refinement compares integers, but this is a `{ty}`"),
                )
                .with_help("name an integer, or a slice's `.len`"),
            );
            return None;
        }
        let leaf = match (root, flat) {
            (Root::Param(k), None) => Leaf::Param(k),
            (Root::Param(k), Some(f)) => Leaf::PField(k, f),
            (Root::Value, None) => Leaf::Value,
            (Root::Field(j), None) => Leaf::Field(j),
            (Root::VParam(p), _) => Leaf::VParam(p),
            (Root::Value | Root::Field(_), Some(_)) => {
                self.error(e.span, "a refinement can't name a field of this value");
                return None;
            }
        };
        Some(Lin::leaf(leaf))
    }

    /// `x.len` in a refinement, for a parameter that's a view or an array
    /// (of any field of it).
    fn refine_len(&mut self, cx: &mut FnCx, e: &ast::Expr, scope: &Scope) -> Option<Lin> {
        let ExprKind::Field(base, _) = &e.kind else {
            return None;
        };
        let (root, ty, flat) = self.refine_path(cx, base, scope)?;
        if let Some((_, len)) = ty.as_array() {
            return Some(match len {
                Len::Known(n) => Lin::constant(i128::from(n)),
                Len::Param(p) => Lin::leaf(Leaf::VParam(p)),
            });
        }
        match (root, flat, ty.is_view()) {
            (Root::Param(k), None, true) => Some(Lin::leaf(Leaf::Len(k))),
            _ => {
                self.error(
                    e.span,
                    "`.len` in a refinement is of a parameter that's a slice, a `str` or an array",
                );
                None
            }
        }
    }

    /// The place a refinement names, with its type and, for a field of a
    /// struct parameter, the field's number (as in [`Term::Field`]).
    fn refine_path(
        &mut self,
        cx: &mut FnCx,
        e: &ast::Expr,
        scope: &Scope,
    ) -> Option<(Root, Ty, Option<u32>)> {
        match &e.kind {
            ExprKind::Paren(inner) => self.refine_path(cx, inner, scope),
            ExprKind::Name(name) => {
                if let Some(t) = scope.result
                    && name == "result"
                {
                    return Some((Root::Value, t, None));
                }
                if let Some(t) = scope.self_ty
                    && name == "self"
                {
                    return Some((Root::Value, t, None));
                }
                if let Some((fields, own)) = scope.fields
                    && let Some(j) = fields.iter().position(|f| f.name == *name)
                {
                    let root = if j == own {
                        Root::Value
                    } else {
                        Root::Field(j)
                    };
                    return Some((root, fields[j].ty, None));
                }
                if let Some(k) = scope.params.iter().position(|p| p.2 == *name) {
                    if k >= scope.visible {
                        let own = scope.own.map(|o| &scope.params[o].2);
                        let msg = match own {
                            Some(o) => format!(
                                "`{name}` comes after `{o}`: a refinement can only name the parameters before it"
                            ),
                            None => format!("`{name}` can't be named here"),
                        };
                        self.diags
                            .push(Diagnostic::error(e.span, msg).with_help(format!(
                                "move the refinement to `{name}`, or `{name}` before this parameter"
                            )));
                        return None;
                    }
                    return Some((Root::Param(k), scope.params[k].0, None));
                }
                if let Some(&p) = cx.type_params.iter().find(|p| p.to_string() == *name)
                    && let Some(it) = p.value_param()
                {
                    return Some((Root::VParam(p), Ty::Int(it), None));
                }
                self.error(e.span, format!("cannot find `{name}` for this refinement"));
                None
            }
            ExprKind::Field(base, member) => {
                let (root, ty, flat) = self.refine_path(cx, base, scope)?;
                if member.name == "len" && (ty.is_view() || ty.as_array().is_some()) {
                    // `.len`: handled by the caller.
                    return Some((root, ty, flat));
                }
                let Some(def) = ty.as_struct() else {
                    self.error(
                        member.span,
                        format!("`{ty}` has no field `{}`", member.name),
                    );
                    return None;
                };
                let Some((i, fty)) = def.field(&member.name) else {
                    self.error(
                        member.span,
                        format!("`{ty}` has no field `{}`", member.name),
                    );
                    return None;
                };
                if def.pkg != cx.pkg && !def.fields[i].is_pub {
                    self.error(
                        member.span,
                        format!(
                            "`{}` is a private field of `{}`, which a refinement here can't name",
                            member.name, def.name
                        ),
                    );
                    return None;
                }
                let before: u32 = def.fields[..i].iter().map(|f| flat_size(f.ty)).sum();
                let flat = flat.unwrap_or(0) + before;
                Some((root, fty, Some(flat)))
            }
            _ => {
                self.error(e.span, "this can't be in a refinement");
                None
            }
        }
    }
}

/// What a call's argument is known as, for the refinements of the callee.
#[derive(Clone, Debug, Default)]
pub(super) struct ArgVal {
    /// Its value, for an integer.
    pub(super) value: Option<Val>,
    /// Its length, for a view or an array.
    pub(super) len: Option<Val>,
    /// For a struct that's a place made of fields only: the local and the
    /// number of its first field (as in [`Term::Field`]).
    pub(super) place: Option<(LocalId, u32)>,
    /// Its type.
    pub(super) ty: Option<Ty>,
}

/// The local and first field number of a struct place made of fields only
/// (`p`, `p.inner`).
pub(super) fn struct_place(e: &TExpr) -> Option<(LocalId, u32)> {
    e.ty.as_struct()?;
    match &e.kind {
        TExprKind::Local(l) => Some((*l, 0)),
        TExprKind::Field(..) => match place_term(e)? {
            Term::Field(l, off) => Some((l, off)),
            _ => None,
        },
        _ => None,
    }
}

/// The number of the first field of field `j` of the struct `def`, among
/// its fields flattened (as in [`Term::Field`]).
fn field_offset(def: &crate::types::StructDef, j: usize) -> u32 {
    def.fields[..j].iter().map(|f| flat_size(f.ty)).sum()
}

/// The value of field `j` of a struct `base` of type `sty`: a term when
/// it's a place made of fields only, otherwise its type's range.
fn field_val(cx: &FnCx, base: Option<(LocalId, u32)>, sty: Ty, j: usize) -> Option<Val> {
    let def = sty.as_struct()?;
    let fty = def.fields.get(j)?.ty;
    let range = type_range(fty)?;
    Some(match base {
        Some((l, b)) => Val::term(cx, Term::Field(l, b + field_offset(&def, j))),
        None => Val::opaque(range),
    })
}

/// The value of a value parameter of a struct `sty`, from its arguments.
fn struct_vparam(cx: &FnCx, sty: Ty, p: Ty) -> Option<Val> {
    let k = sty.decl().decl_params().iter().position(|&q| q == p)?;
    let arg = *sty.type_args().get(k)?;
    value_arg(cx, arg)
}

impl Checker<'_> {
    /// The source text of `span`, for messages.
    pub(super) fn span_text(&self, span: Span) -> String {
        self.sources
            .get(&span.file)
            .and_then(|s| s.get(span.start as usize..span.end as usize))
            .unwrap_or("the refinement")
            .to_owned()
    }

    /// The error for a refinement `atom` that isn't proven where `span` is,
    /// `what` saying for what.
    pub(super) fn refine_error(&mut self, span: Span, atom: &Atom, what: &str, val: Option<&Val>) {
        let text = self.span_text(atom.span);
        let mut d = Diagnostic::error(span, format!("cannot prove `{text}` {what}"))
            .with_note(atom.span, "the refinement");
        if let Some(v) = val
            && v.form.is_none_or(|f| f.term_count() > 0)
            && v.range.lo > i128::from(i64::MIN)
            && v.range.hi < i128::from(i64::MAX)
        {
            d = d.with_help(format!("the value can be {}", v.range));
        }
        d = d.with_help(
            "the checker proves it from the facts it knows here: check the value first, or give it a refinement that proves it",
        );
        self.diags.push(d);
    }

    /// The type `t` names, and when it's a named refinement (`Digit`), its
    /// refinement, about [`Leaf::Value`]. A named refinement elsewhere in a
    /// type (`[4]Digit`) is an error in [`Checker::resolve_type`].
    pub(super) fn resolve_refined(
        &mut self,
        cx: &mut FnCx,
        t: &ast::TypeExpr,
    ) -> Option<(Ty, Option<Rc<Refine>>)> {
        let item = match t {
            ast::TypeExpr::Named(id) => match self.pkgs[cx.pkg].items.get(&id.name) {
                Some(&Item::Refined(k)) => Some(k),
                _ => None,
            },
            ast::TypeExpr::Qualified(pkg, name) => {
                let found = self
                    .imports
                    .get(&cx.file)
                    .and_then(|m| m.get(&pkg.name))
                    .copied();
                match found {
                    Some(p)
                        if matches!(self.pkgs[p].items.get(&name.name), Some(Item::Refined(_))) =>
                    {
                        match self.package_item(cx, p, &name.name, name.span)? {
                            Item::Refined(k) => Some(k),
                            _ => None,
                        }
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        match item {
            Some(k) => {
                let (ty, r) = self.refined_type(k)?;
                Some((ty, Some(r)))
            }
            None => Some((self.resolve_type(cx, t)?, None)),
        }
    }

    /// The type and refinement of the named refinement `k`, resolved the
    /// first time.
    pub(super) fn refined_type(&mut self, k: usize) -> Option<(Ty, Rc<Refine>)> {
        match &self.refined_types[k].state {
            RefinedState::Done(v) => return v.clone(),
            RefinedState::Resolving => {
                let decl = self.refined_types[k].decl;
                self.error(
                    decl.name.span,
                    format!("`{}` is defined in terms of itself", decl.name.name),
                );
                self.refined_types[k].state = RefinedState::Done(None);
                return None;
            }
            RefinedState::Unresolved => {}
        }
        self.refined_types[k].state = RefinedState::Resolving;
        let RefinedType {
            decl, pkg, file, ..
        } = self.refined_types[k];
        let mut cx = FnCx::new(pkg, file, Ty::Unit, false);
        let out = self.resolve_refined_decl(&mut cx, decl);
        self.refined_types[k].state = RefinedState::Done(out.clone());
        out
    }

    fn resolve_refined_decl(
        &mut self,
        cx: &mut FnCx,
        decl: &ast::TypeDecl,
    ) -> Option<(Ty, Rc<Refine>)> {
        let ty = self.resolve_type(cx, &decl.ty)?;
        if ty.as_int().is_none() {
            self.diags.push(
                Diagnostic::error(
                    decl.ty.span(),
                    format!("a named refinement refines an integer type, not `{ty}`"),
                )
                .with_help("as in `type Digit = u8 where self <= 9`"),
            );
            return None;
        }
        let Some(e) = &decl.refine else {
            self.diags.push(
                Diagnostic::error(
                    decl.span,
                    "a `type` declaration needs a refinement: `type Digit = u8 where self <= 9`",
                )
                .with_help(
                    "other type declarations (distinct types, aliases) are not supported by the compiler yet",
                ),
            );
            return None;
        };
        let scope = Scope {
            params: &[],
            visible: 0,
            own: None,
            result: None,
            fields: None,
            self_ty: Some(ty),
        };
        let r = self.refinement(cx, e, &scope)?;
        Some((ty, r))
    }

    /// The refinements of a function's parameters and result, from their
    /// `where` clauses and named refinements (`named`, about
    /// [`Leaf::Value`]). Errors are reported.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn sig_refines(
        &mut self,
        cx: &mut FnCx,
        f: &ast::FnDecl,
        params: &[(Ty, Convention, String)],
        named: &[Option<Rc<Refine>>],
        ret: Ty,
        ret_named: Option<Rc<Refine>>,
        is_member: bool,
    ) -> (Vec<Option<Rc<Refine>>>, Option<Rc<Refine>>) {
        let mut out: Vec<Option<Rc<Refine>>> = vec![None; params.len()];
        let assignable = |k: usize| {
            let (ty, conv, _) = &params[k];
            !ty.is_view() && matches!(conv, Convention::Inout | Convention::Sink | Convention::Set)
        };
        let names_param = |r: &Refine, j: usize| {
            r.mentions(Leaf::Param(j))
                || r.atoms.iter().any(|a| {
                    a.lhs
                        .parts
                        .iter()
                        .chain(&a.rhs.parts)
                        .any(|p| matches!(p.0, Leaf::PField(x, _) if x == j))
                })
        };
        let any = f.params.iter().any(|p| p.refine.is_some())
            || named.iter().any(Option::is_some)
            || f.ret_refine.is_some()
            || ret_named.is_some();
        if any && is_member {
            let span = f
                .params
                .iter()
                .find_map(|p| p.refine.as_ref().map(|e| e.span))
                .or(f.ret_refine.as_ref().map(|e| e.span))
                .unwrap_or(f.name.span);
            self.error(
                span,
                "refinements on the methods of traits and impls are not supported by the compiler yet",
            );
            return (out, None);
        }
        if params.len() != f.params.len() {
            return (out, None);
        }
        for (k, p) in f.params.iter().enumerate() {
            let own = named
                .get(k)
                .cloned()
                .flatten()
                .map(|r| Rc::new(r.subst(Leaf::Value, Leaf::Param(k))));
            let written = match &p.refine {
                Some(e) => {
                    let scope = Scope {
                        params,
                        visible: k + 1,
                        own: Some(k),
                        result: None,
                        fields: None,
                        self_ty: None,
                    };
                    self.refinement(cx, e, &scope)
                }
                None => None,
            };
            if let (Some(r), Some(e)) = (&written, &p.refine) {
                let own_field = r.atoms.iter().any(|a| {
                    a.lhs
                        .parts
                        .iter()
                        .chain(&a.rhs.parts)
                        .any(|p| matches!(p.0, Leaf::PField(x, _) if x == k))
                });
                if assignable(k) && own_field {
                    self.error(
                        e.span,
                        format!(
                            "`{}` can change, so its refinement can only be about its value, not its fields",
                            params[k].2
                        ),
                    );
                }
                for j in (0..params.len()).filter(|&j| j != k) {
                    if !names_param(r, j) {
                        continue;
                    }
                    if params[j].1 == Convention::Set && !params[j].0.is_view() {
                        self.error(
                            e.span,
                            format!(
                                "a refinement can't name `{}`, which is passed `set`: it has no value when the call starts",
                                params[j].2
                            ),
                        );
                    } else if assignable(k) && assignable(j) {
                        self.error(
                            e.span,
                            format!(
                                "`{}` can change, so its refinement can't name `{}`, which can change too",
                                params[k].2, params[j].2
                            ),
                        );
                    }
                }
            }
            out[k] = Refine::and(own, written);
        }
        let ret_written = match &f.ret_refine {
            Some(e) => {
                let scope = Scope {
                    params,
                    visible: params.len(),
                    own: None,
                    result: Some(ret.as_optional().unwrap_or(ret)),
                    fields: None,
                    self_ty: None,
                };
                let r = self.refinement(cx, e, &scope);
                if let Some(r) = &r {
                    for (j, (ty, conv, name)) in params.iter().enumerate() {
                        if names_param(r, j) && *conv == Convention::Sink && !ty.is_view() {
                            self.error(
                                e.span,
                                format!(
                                    "a result's refinement can't name `{name}`, which is passed `sink`: the caller doesn't have its value after the call"
                                ),
                            );
                        }
                    }
                }
                match r {
                    Some(r) if !r.mentions(Leaf::Value) => {
                        self.diags.push(
                            Diagnostic::error(
                                e.span,
                                "this refinement of the result doesn't name `result`",
                            )
                            .with_help("as in `-> usize where result <= buf.len`"),
                        );
                        None
                    }
                    r => r,
                }
            }
            None => None,
        };
        (out, Refine::and(ret_named, ret_written))
    }

    /// What a leaf is in the body of the function being checked: its
    /// parameters are terms, and `value` is [`Leaf::Value`].
    pub(super) fn body_leaf(cx: &FnCx, leaf: Leaf, value: Option<&Val>) -> Option<Val> {
        match leaf {
            Leaf::Value => value.cloned(),
            Leaf::Param(k) => Some(Val::term(cx, Term::Local(k))),
            Leaf::Len(k) if cx.locals[k].ty.is_view() => Some(Val::term(cx, Term::Len(k))),
            Leaf::Len(_) => None,
            Leaf::PField(k, f) => Some(Val::term(cx, Term::Field(k, f))),
            Leaf::VParam(p) => value_arg(cx, p),
            Leaf::Field(_) => None,
        }
    }

    /// At the start of a body: the parameters' refinements are facts, and
    /// those of parameters it can assign hold at each assignment.
    pub(super) fn assume_params(&self, cx: &mut FnCx, id: usize) {
        let refines = self.sigs[id].refines.clone();
        let params = self.sigs[id].params.clone();
        // The refinements of the fields of struct parameters, which a
        // parameter's refinement may name.
        for (k, (ty, conv, _)) in params.iter().enumerate() {
            if *conv != Convention::Set && k < cx.locals.len() {
                self.assume_struct(cx, k, 0, *ty);
            }
        }
        for (k, r) in refines.iter().enumerate() {
            let Some(r) = r else {
                continue;
            };
            let (ty, conv, _) = &params[k];
            if !ty.is_view()
                && matches!(conv, Convention::Inout | Convention::Sink | Convention::Set)
            {
                cx.place_refines.insert(k, (r.clone(), Leaf::Param(k)));
            }
            if *conv != Convention::Set {
                let facts = facts_of(cx, r, &|l| Self::body_leaf(cx, l, None));
                cx.env.apply(&facts);
            }
        }
        cx.ret_refine = self.sigs[id].ret_refine.clone();
    }

    /// `return value`: the result's refinement must hold. For a `?T`
    /// result, it's about the value in it: `none` needs nothing, and a `?T`
    /// value needs what's known about the value in it.
    pub(super) fn check_return_refine(&mut self, cx: &FnCx, value: &Checked, span: Span) {
        let Some(r) = cx.ret_refine.clone() else {
            return;
        };
        let inner = cx.ret.as_optional();
        let v = match inner {
            Some(t) if value.ty() == cx.ret => {
                let full = type_range(t).unwrap_or(Range::exact(0));
                match (&value.expr.kind, &value.payload) {
                    (TExprKind::Variant(0, _), _) => return,
                    (_, Some(p)) => Val {
                        form: None,
                        range: p.0.unwrap_or(full),
                        known: p.1.clone(),
                    },
                    _ => Val::opaque(full),
                }
            }
            _ => Val::of(value),
        };
        for atom in &r.atoms {
            if !holds(cx, atom, &|l| Self::body_leaf(cx, l, Some(&v))) {
                self.refine_error(span, atom, "for the result", Some(&v));
                return;
            }
        }
    }

    /// The local `local`, which may have a refinement, is given `value`:
    /// it must hold.
    pub(super) fn check_local_refine(
        &mut self,
        cx: &FnCx,
        local: LocalId,
        value: &Checked,
        span: Span,
    ) {
        let Some((r, subject)) = cx.place_refines.get(&local).cloned() else {
            return;
        };
        let v = Val::of(value);
        let name = cx.locals[local].name.clone();
        for atom in &r.atoms {
            let ok = holds(cx, atom, &|l| {
                if l == subject {
                    Some(v.clone())
                } else {
                    Self::body_leaf(cx, l, None)
                }
            });
            if !ok {
                self.refine_error(span, atom, &format!("for the value of `{name}`"), Some(&v));
                return;
            }
        }
    }

    /// A local that may have a refinement was given a value (known to
    /// satisfy it): its facts.
    pub(super) fn assume_local_refine(&self, cx: &mut FnCx, local: LocalId) {
        let Some((r, subject)) = cx.place_refines.get(&local).cloned() else {
            return;
        };
        let me = Val::term(cx, Term::Local(local));
        let facts = facts_of(cx, &r, &|l| {
            if l == subject {
                Some(me.clone())
            } else {
                Self::body_leaf(cx, l, None)
            }
        });
        cx.env.apply(&facts);
    }

    /// The refinements of the fields of `sty` (its declaration's), by
    /// field.
    pub(super) fn struct_refines(&self, sty: Ty) -> Vec<(usize, Rc<Refine>)> {
        if sty.as_struct().is_none() {
            return Vec::new();
        }
        self.field_refines
            .get(&sty.decl())
            .cloned()
            .unwrap_or_default()
    }

    /// Every value of a struct keeps its fields' refinements: for the
    /// struct place `(local, base)` of type `sty`, they're facts.
    pub(super) fn assume_struct(&self, cx: &mut FnCx, local: LocalId, base: u32, sty: Ty) {
        let refines = self.struct_refines(sty);
        if refines.is_empty() {
            return;
        }
        let place = Some((local, base));
        let mut facts = Vec::new();
        for (j, r) in &refines {
            facts.extend(facts_of(cx, r, &|l| match l {
                Leaf::Value => field_val(cx, place, sty, *j),
                Leaf::Field(m) => field_val(cx, place, sty, m),
                Leaf::VParam(p) => struct_vparam(cx, sty, p),
                _ => None,
            }));
        }
        cx.env.apply(&facts);
    }

    /// Field `i` of a struct of type `sty` was read, into `c`, from the
    /// place `at` when it's made of fields only: what the struct's
    /// refinements say about it. For such a place, they're facts about its
    /// fields; otherwise they bound the value read.
    pub(super) fn field_read(
        &self,
        cx: &mut FnCx,
        sty: Ty,
        at: Option<(LocalId, u32)>,
        i: usize,
        c: &mut Checked,
    ) {
        if let Some((l, b)) = at {
            self.assume_struct(cx, l, b, sty);
            if let Some(Linear { term, .. }) = c.term {
                c.range = read_range(cx, term);
            }
            return;
        }
        let Some((_, r)) = self.struct_refines(sty).into_iter().find(|(j, _)| *j == i) else {
            return;
        };
        let (range, known) = value_facts(cx, &r, &|l| match l {
            Leaf::Field(m) => field_val(cx, None, sty, m),
            Leaf::VParam(p) => struct_vparam(cx, sty, p),
            _ => None,
        });
        if let Some(range) = range {
            let r0 = c.int_range();
            c.range = Some(r0.intersect(range).unwrap_or(r0));
        }
        c.known.extend(known);
    }

    /// `place = value` for a field `place`: every refinement of the struct
    /// that names the field must hold with the new value.
    pub(super) fn check_field_assign(
        &mut self,
        cx: &mut FnCx,
        place: &TExpr,
        value: &Checked,
        span: Span,
    ) {
        let TExprKind::Field(base, i) = &place.kind else {
            return;
        };
        let i = *i as usize;
        let sty = base.ty;
        let refines = self.struct_refines(sty);
        if refines.is_empty() {
            return;
        }
        let at = struct_place(base);
        if let Some((l, b)) = at {
            self.assume_struct(cx, l, b, sty);
        }
        let new = Val::of(value);
        let name = sty
            .as_struct()
            .and_then(|d| d.fields.get(i).map(|f| f.name.clone()))
            .unwrap_or_default();
        // The field's own refinement first, then the others that name it.
        let mut order: Vec<&(usize, Rc<Refine>)> =
            refines.iter().filter(|(j, _)| *j == i).collect();
        order.extend(
            refines
                .iter()
                .filter(|(j, r)| *j != i && r.mentions(Leaf::Field(i))),
        );
        for (j, r) in order {
            for atom in &r.atoms {
                let ok = holds(cx, atom, &|l| match l {
                    Leaf::Value if *j == i => Some(new.clone()),
                    Leaf::Value => field_val(cx, at, sty, *j),
                    Leaf::Field(m) if m == i => Some(new.clone()),
                    Leaf::Field(m) => field_val(cx, at, sty, m),
                    Leaf::VParam(p) => struct_vparam(cx, sty, p),
                    _ => None,
                });
                if !ok {
                    self.refine_error(
                        span,
                        atom,
                        &format!("for the field `{name}` of `{sty}`"),
                        Some(&new),
                    );
                    return;
                }
            }
        }
    }

    /// A struct literal of type `sty`, with the fields' values `vals` (by
    /// field, with their spans): every refinement of its fields must hold.
    /// In code that only runs at compile time, `false` when one isn't
    /// proven (the evaluator checks it); otherwise it's an error.
    pub(super) fn check_struct_lit(
        &mut self,
        cx: &FnCx,
        sty: Ty,
        vals: &[(usize, Val, Span)],
        span: Span,
    ) -> bool {
        let refines = self.struct_refines(sty);
        let get = |m: usize| vals.iter().find(|v| v.0 == m).map(|v| v.1.clone());
        for (j, r) in &refines {
            for atom in &r.atoms {
                let ok = holds(cx, atom, &|l| match l {
                    Leaf::Value => get(*j),
                    Leaf::Field(m) => get(m),
                    Leaf::VParam(p) => struct_vparam(cx, sty, p),
                    _ => None,
                });
                if ok {
                    continue;
                }
                if cx.comptime {
                    return false;
                }
                let (at, v) = match vals.iter().find(|v| v.0 == *j) {
                    Some((_, v, s)) => (*s, Some(v)),
                    None => (span, None),
                };
                let name = sty
                    .as_struct()
                    .and_then(|d| d.fields.get(*j).map(|f| f.name.clone()))
                    .unwrap_or_default();
                self.refine_error(at, atom, &format!("for the field `{name}` of `{sty}`"), v);
                return true;
            }
        }
        true
    }

    /// What a checked argument is known as.
    pub(super) fn arg_of_checked(&self, cx: &FnCx, c: &Checked) -> ArgVal {
        let ty = c.ty();
        let len = if let TExprKind::ToSlice(a) = &c.expr.kind {
            // An array passed as a slice: its length.
            match a.ty.as_array() {
                Some((_, Len::Known(n))) => Some(Val::konst(i128::from(n))),
                Some((_, Len::Param(p))) => value_arg(cx, p),
                None => None,
            }
        } else if ty.is_view() {
            Some(Val::of(&self.view_len_of(cx, c)))
        } else {
            match ty.as_array() {
                Some((_, Len::Known(n))) => Some(Val::konst(i128::from(n))),
                Some((_, Len::Param(p))) => value_arg(cx, p),
                None => None,
            }
        };
        ArgVal {
            value: type_range(ty).is_some().then(|| Val::of(c)),
            len,
            place: struct_place(&c.expr),
            ty: Some(ty),
        }
    }

    /// What a place passed `&` is known as (before the call).
    pub(super) fn arg_of_place(&self, cx: &FnCx, place: &TExpr) -> ArgVal {
        let ty = place.ty;
        let value = type_range(ty).map(|full| match &place.kind {
            TExprKind::Local(l) => Val::term(cx, Term::Local(*l)),
            _ => match place_term(place) {
                Some(t) => Val::term(cx, t),
                None => Val::opaque(full),
            },
        });
        let len = match (&place.kind, ty.as_array()) {
            (_, Some((_, Len::Known(n)))) => Some(Val::konst(i128::from(n))),
            (_, Some((_, Len::Param(p)))) => value_arg(cx, p),
            (TExprKind::Local(l), None) if ty.is_view() => Some(Val::term(cx, Term::Len(*l))),
            (TExprKind::ToSlice(a), None) => match a.ty.as_array() {
                Some((_, Len::Known(n))) => Some(Val::konst(i128::from(n))),
                Some((_, Len::Param(p))) => value_arg(cx, p),
                None => match &a.kind {
                    TExprKind::Local(l) if a.ty.is_view() => Some(Val::term(cx, Term::Len(*l))),
                    _ => None,
                },
            },
            _ => None,
        };
        ArgVal {
            value,
            len,
            place: struct_place(place),
            ty: Some(ty),
        }
    }
}

/// What a leaf of the callee's refinements is at a call, from the
/// arguments `args` (the receiver first) and the generic arguments
/// `vparam` gives; [`Leaf::Value`] is `value`.
pub(super) fn call_leaf(
    cx: &FnCx,
    leaf: Leaf,
    args: &[ArgVal],
    vparam: &dyn Fn(Ty) -> Ty,
    value: Option<&Val>,
) -> Option<Val> {
    match leaf {
        Leaf::Value => value.cloned(),
        Leaf::Param(k) => args.get(k)?.value.clone(),
        Leaf::Len(k) => args.get(k)?.len.clone(),
        Leaf::PField(k, f) => {
            let a = args.get(k)?;
            match a.place {
                Some((l, b)) => Some(Val::term(cx, Term::Field(l, b + f))),
                None => {
                    let fty = super::flat_field(a.ty?, f)?;
                    Some(Val::opaque(type_range(fty)?))
                }
            }
        }
        Leaf::VParam(p) => value_arg(cx, vparam(p)),
        Leaf::Field(_) => None,
    }
}

/// The facts known bounds give about `local`, which holds the value.
pub(super) fn known_facts(cx: &FnCx, local: LocalId, known: &[Known]) -> Vec<Fact> {
    let me = Form::of(Linear::of(Term::Local(local)));
    let f = full(cx, Term::Local(local));
    let mut out = Vec::new();
    for k in known {
        if k.form.terms().any(|(t, _)| t.local() == local) {
            continue;
        }
        if let Some(form) = me.scale(k.sign).and_then(|m| m.plus(k.form)) {
            out.extend(form.le(k.c, f));
        }
    }
    out
}

/// A known upper bound that's a term plus a constant (`v <= t + c`), as
/// [`Checked::upper`] keeps it.
pub(super) fn known_upper(known: &[Known]) -> Option<Linear> {
    known.iter().find_map(|k| {
        let terms: Vec<(Term, i128)> = k.form.terms().collect();
        let [(t, -1)] = terms[..] else {
            return None;
        };
        if k.sign != 1 {
            return None;
        }
        Some(Linear {
            term: t,
            offset: k.c.checked_sub(k.form.k)?,
        })
    })
}

impl Checker<'_> {
    /// `Digit(x)` for a named refinement `Digit` (number `k`): `x`
    /// converted to its type, which must meet the refinement.
    pub(super) fn refined_conversion(
        &mut self,
        cx: &mut FnCx,
        k: usize,
        name: &str,
        name_span: Span,
        args: &[ast::Expr],
        span: Span,
    ) -> Option<Checked> {
        let (ty, r) = self.refined_type(k)?;
        let c = self.conversion(cx, &ty.to_string(), name_span, args, span)?;
        let v = Val::of(&c);
        for atom in &r.atoms {
            if holds(cx, atom, &|l| (l == Leaf::Value).then(|| v.clone())) {
                continue;
            }
            if cx.comptime {
                // Checked when it runs.
                let c = Checked::new(TExprKind::Refined(Box::new(c.expr), k), ty, None);
                return Some(c.unproven(span));
            }
            self.refine_error(span, atom, &format!("for a `{name}`"), Some(&v));
            return None;
        }
        Some(c)
    }
}

impl Checker<'_> {
    /// After a call, for a place passed `&` to parameter `k`, whose
    /// refinement is `callee`: whether the place's own refinement (a
    /// local's, or one of its struct's that names the field) still holds.
    /// The callee may have changed the place to any value its parameter's
    /// refinement allows, so that refinement must prove it.
    pub(super) fn ref_keeps_refine(
        &self,
        cx: &mut FnCx,
        place: &TExpr,
        k: usize,
        callee: Option<&Refine>,
        args: &[ArgVal],
        vparam: &dyn Fn(Ty) -> Ty,
    ) -> bool {
        let assume = |cx: &mut FnCx, me: &Val| {
            if let Some(cr) = callee {
                let facts = facts_of(cx, cr, &|leaf| {
                    if leaf == Leaf::Param(k) {
                        Some(me.clone())
                    } else {
                        call_leaf(cx, leaf, args, vparam, None)
                    }
                });
                cx.env.apply(&facts);
            }
        };
        match &place.kind {
            TExprKind::Local(l) => {
                let Some((r, subject)) = cx.place_refines.get(l).cloned() else {
                    return true;
                };
                let me = Val::term(cx, Term::Local(*l));
                assume(cx, &me);
                r.atoms.iter().all(|a| {
                    holds(cx, a, &|leaf| {
                        if leaf == subject {
                            Some(me.clone())
                        } else {
                            Self::body_leaf(cx, leaf, None)
                        }
                    })
                })
            }
            TExprKind::Field(base, i) => {
                let i = *i as usize;
                let sty = base.ty;
                let touching: Vec<(usize, Rc<Refine>)> = self
                    .struct_refines(sty)
                    .into_iter()
                    .filter(|(j, r)| *j == i || r.mentions(Leaf::Field(i)))
                    .collect();
                if touching.is_empty() {
                    return true;
                }
                let at = struct_place(base);
                let Some(me) = at.and_then(|_| field_val(cx, at, sty, i)) else {
                    return false;
                };
                assume(cx, &me);
                touching.iter().all(|(j, r)| {
                    r.atoms.iter().all(|a| {
                        holds(cx, a, &|leaf| match leaf {
                            Leaf::Value => field_val(cx, at, sty, *j),
                            Leaf::Field(m) => field_val(cx, at, sty, m),
                            Leaf::VParam(p) => struct_vparam(cx, sty, p),
                            _ => None,
                        })
                    })
                })
            }
            _ => true,
        }
    }
}

/// Whether a comparison holds for the values `leaf` gives (exactly, over
/// all integers). A leaf with no value (a result's) doesn't fail it.
fn eval_holds(atom: &Atom, leaf: &dyn Fn(Leaf) -> Option<i128>) -> bool {
    let sum = |lin: &Lin| -> Option<i128> {
        let mut v = lin.k;
        for &(l, m) in &lin.parts {
            v = v.checked_add(leaf(l)?.checked_mul(m)?)?;
        }
        Some(v)
    };
    let (Some(l), Some(r)) = (sum(&atom.lhs), sum(&atom.rhs)) else {
        return true;
    };
    match atom.op {
        CmpOp::Lt => l < r,
        CmpOp::Le => l <= r,
        CmpOp::Gt => l > r,
        CmpOp::Ge => l >= r,
        CmpOp::Eq => l == r,
        CmpOp::Ne => l != r,
    }
}

/// The integer of a value at compile time, if it's one.
fn value_int(v: &Value) -> Option<i128> {
    match v {
        Value::Int(x) => Some(*x),
        _ => None,
    }
}

/// The length of a view or an array at compile time.
fn value_len(v: &Value) -> Option<i128> {
    match v {
        Value::Array(xs) => i128::try_from(xs.len()).ok(),
        Value::Slice(_, _, len) => i128::try_from(*len).ok(),
        Value::Str(s) => i128::try_from(s.len).ok(),
        _ => None,
    }
}

/// Field number `f` (as in [`Term::Field`]) of a value of type `ty`.
fn value_field(v: &Value, ty: Ty, f: u32) -> Option<i128> {
    let Some(def) = ty.as_struct() else {
        return if f == 0 { value_int(v) } else { None };
    };
    let Value::Struct(fields) = v else {
        return None;
    };
    let mut f = f;
    for (fd, fv) in def.fields.iter().zip(fields.iter()) {
        let n = flat_size(fd.ty);
        if f < n {
            return value_field(fv, fd.ty, f);
        }
        f -= n;
    }
    None
}

impl Checker<'_> {
    /// At compile time, a call of `f` with the parameters `params` (its
    /// locals) holding `locals`: the message for a refinement of a
    /// parameter that the arguments don't meet. `ty` gives the type
    /// arguments.
    pub(super) fn params_fail(
        &self,
        f: usize,
        params: &[LocalId],
        locals: &[Value],
        ty: &dyn Fn(Ty) -> Ty,
    ) -> Option<String> {
        let sig = &self.sigs[f];
        for (k, r) in sig.refines.iter().enumerate() {
            let Some(r) = r else {
                continue;
            };
            if sig.params[k].1 == Convention::Set {
                continue;
            }
            let val = |j: usize| params.get(j).and_then(|&l| locals.get(l));
            let leaf = |l: Leaf| -> Option<i128> {
                match l {
                    Leaf::Param(j) => value_int(val(j)?),
                    Leaf::Len(j) => value_len(val(j)?),
                    Leaf::PField(j, fl) => value_field(val(j)?, ty(sig.params[j].0), fl),
                    Leaf::VParam(p) => ty(p).as_value(),
                    Leaf::Value | Leaf::Field(_) => None,
                }
            };
            for atom in &r.atoms {
                if !eval_holds(atom, &leaf) {
                    return Some(format!(
                        "`{}` of `{}` doesn't meet its refinement `{}`",
                        sig.params[k].2,
                        sig.name,
                        self.span_text(atom.span)
                    ));
                }
            }
        }
        None
    }

    /// At compile time, a struct of type `sty` with the fields `vs`: the
    /// message for a field's refinement it doesn't meet.
    pub(super) fn fields_fail(&self, sty: Ty, vs: &[Value]) -> Option<String> {
        for (j, r) in self.struct_refines(sty) {
            let leaf = |l: Leaf| -> Option<i128> {
                match l {
                    Leaf::Value => value_int(vs.get(j)?),
                    Leaf::Field(m) => value_int(vs.get(m)?),
                    Leaf::VParam(p) => {
                        let k = sty.decl().decl_params().iter().position(|&q| q == p)?;
                        sty.type_args().get(k)?.as_value()
                    }
                    _ => None,
                }
            };
            for atom in &r.atoms {
                if !eval_holds(atom, &leaf) {
                    let name = sty
                        .as_struct()
                        .and_then(|d| d.fields.get(j).map(|f| f.name.clone()))
                        .unwrap_or_default();
                    return Some(format!(
                        "the field `{name}` of `{sty}` doesn't meet its refinement `{}`",
                        self.span_text(atom.span)
                    ));
                }
            }
        }
        None
    }

    /// At compile time, a value `v` converted to the named refinement `k`:
    /// the message if it doesn't meet it.
    pub(super) fn refined_fails(&self, k: usize, v: &Value) -> Option<String> {
        let RefinedState::Done(Some((_, r))) = &self.refined_types[k].state else {
            return None;
        };
        let x = value_int(v)?;
        let leaf = |l: Leaf| (l == Leaf::Value).then_some(x);
        let name = &self.refined_types[k].decl.name.name;
        r.atoms.iter().find(|a| !eval_holds(a, &leaf)).map(|a| {
            format!(
                "{x} isn't a `{name}`: it doesn't meet `{}`",
                self.span_text(a.span)
            )
        })
    }
}

impl Checker<'_> {
    /// Report the refinements of generic parameters declared where they
    /// aren't supported: on a struct, an enum, an `impl` or the type's
    /// parameters of a method.
    pub(super) fn no_generic_refine(&mut self, generics: &[ast::GenericParam]) {
        for g in generics {
            if let Some(e) = &g.refine {
                self.error(
                    e.span,
                    "only a function's own value parameters can have a refinement for now",
                );
            }
        }
    }

    /// The refinements of a function's own value parameters (`[N: usize
    /// where N > 0]`), declared in `cx.type_params`, together.
    pub(super) fn vparam_refine(
        &mut self,
        cx: &mut FnCx,
        generics: &[ast::GenericParam],
    ) -> Option<Rc<Refine>> {
        let mut out = None;
        for g in generics {
            let Some(e) = &g.refine else {
                continue;
            };
            let declared = cx
                .type_params
                .iter()
                .find(|p| p.to_string() == g.name.name)
                .copied();
            if declared.is_none_or(|p| p.value_param().is_none()) {
                self.error(
                    e.span,
                    format!(
                        "`{}` is a type parameter: only a value parameter (`[N: usize where N > 0]`) has a refinement",
                        g.name.name
                    ),
                );
                continue;
            }
            let scope = Scope {
                params: &[],
                visible: 0,
                own: None,
                result: None,
                fields: None,
                self_ty: None,
            };
            if let Some(r) = self.refinement(cx, e, &scope) {
                out = Refine::and(out, Some(r));
            }
        }
        out
    }

    /// At the start of a body: its value parameters' refinements are facts.
    pub(super) fn assume_vparams(&self, cx: &mut FnCx, id: usize) {
        if let Some(r) = self.sigs[id].vparam_refine.clone() {
            let facts = facts_of(cx, &r, &|l| Self::body_leaf(cx, l, None));
            cx.env.apply(&facts);
        }
    }

    /// At compile time, a call of `f` with the type arguments `ty` gives:
    /// the message for a refinement of its value parameters they don't
    /// meet.
    pub(super) fn vparams_fail(&self, f: usize, ty: &dyn Fn(Ty) -> Ty) -> Option<String> {
        let r = self.sigs[f].vparam_refine.as_ref()?;
        let leaf = |l: Leaf| match l {
            Leaf::VParam(p) => ty(p).as_value(),
            _ => None,
        };
        r.atoms.iter().find(|a| !eval_holds(a, &leaf)).map(|a| {
            format!(
                "the generic arguments of `{}` don't meet its refinement `{}`",
                self.sigs[f].name,
                self.span_text(a.span)
            )
        })
    }
}
