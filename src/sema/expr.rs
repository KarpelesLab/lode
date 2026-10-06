//! Checking expressions.

use std::collections::HashMap;

use crate::ast::{self, BinOp, ExprKind, UnOp};
use crate::diag::Diagnostic;
use crate::source::Span;
use crate::types::{Field, IntTy, Len, Primitive, Range, StructDef, Trait, Ty, primitive};

use super::facts::{self, CondFacts, Env, Form, Linear, Side, Term};
use super::generic::{
    GenericEdge, Inference, ORDERED_METHODS, expr_type, num, param_help, show_range,
};
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
    /// For integers, a term plus a constant it's known to be at most (`x / 2`
    /// is at most `x`), when it isn't exactly a term.
    pub(super) upper: Option<Linear>,
    /// For a slice `base[start..end]`, what's known about its length.
    pub(super) len: Option<SliceLen>,
    /// For integers, the value as a form of at most two terms, like
    /// `9 - d` or `10 * v + d`, when it isn't exactly a term plus a
    /// constant (see [`Checked::form`]).
    pub(super) form: Option<Form>,
    /// For integers, the value as `F / m` (rounded down) of a form `F` that
    /// can't be negative and a constant `m >= 1`, like `(MAX - d) / 10`.
    pub(super) quot: Option<(Form, i128)>,
}

/// What the checker knows about the length of a slice `base[start..end]`,
/// which is `end - start`.
#[derive(Clone, Copy, Debug)]
pub(super) struct SliceLen {
    /// The length's range.
    pub(super) range: Range,
    /// `end`, as a term plus a constant (the base's length, for `base[i..]`).
    pub(super) end: Option<Linear>,
    /// The range of `start`: the length is between `end - start.hi` and
    /// `end - start.lo`.
    pub(super) start: Range,
}

impl Checked {
    pub(super) fn new(kind: TExprKind, ty: Ty, range: Option<Range>) -> Checked {
        Checked {
            expr: TExpr { kind, ty },
            range,
            term: None,
            facts: None,
            upper: None,
            len: None,
            form: None,
            quot: None,
        }
    }

    /// The value as a form: its term plus a constant, a constant if its
    /// range is a single value, or the form it was computed as.
    pub(super) fn form(&self) -> Option<Form> {
        if let Some(t) = self.term {
            return Some(Form::of(t));
        }
        match self.range {
            Some(r) if r.lo == r.hi => Some(Form::constant(r.lo)),
            _ => self.form,
        }
    }

    /// The same value converted to `ty`, in `range`: it's still the term,
    /// form or quotient this one is, and below the same `upper` bound.
    pub(super) fn converted(self, ty: Ty, range: Option<Range>) -> Checked {
        let mut out = Checked::new(TExprKind::Convert(Box::new(self.expr)), ty, range);
        out.term = self.term;
        out.upper = self.upper;
        out.form = self.form;
        out.quot = self.quot;
        out
    }

    pub(super) fn ty(&self) -> Ty {
        self.expr.ty
    }

    /// This operation, whose proof obligation isn't proven, in code that
    /// only runs at compile time (see [`FnCx::comptime`]): checked as it
    /// runs, with a failure reported at `span`. Its value is anything of
    /// its type.
    pub(super) fn unproven(self, span: Span) -> Checked {
        let ty = self.ty();
        let range = type_range(ty);
        Checked::new(TExprKind::Unproven(span, Box::new(self.expr)), ty, range)
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
            form: self.form(),
            quot: self.quot,
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

/// The name of a struct or an enum, without arguments (`Pair`).
pub(super) fn nominal_name(ty: Ty) -> String {
    match ty.as_struct() {
        Some(def) => def.name.clone(),
        None => ty
            .as_enum()
            .map_or_else(|| ty.to_string(), |d| d.name.clone()),
    }
}

/// The name a call's callee is written with (`f`, `os.write`), for messages.
fn callee_name(callee: &ast::Expr) -> String {
    match &callee.kind {
        ExprKind::Name(n) => n.clone(),
        ExprKind::Field(base, member) => format!("{}.{}", callee_name(base), member.name),
        ExprKind::Call(callee, _) => format!("{}()", callee_name(callee)),
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
    if from == to || from == Ty::Never {
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

/// What changes a place, for messages: a `&` argument passed `inout` or
/// `set`, or the receiver of a method that takes `inout self` (its name).
#[derive(Clone, Copy)]
pub(super) enum Changer<'a> {
    Ref,
    Receiver(&'a str),
}

/// One step from a variable to a part of it.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Step {
    Field(u32),
    /// An element, at a constant index if known.
    Index(Option<i128>),
    /// A payload field (of a hidden local).
    Payload,
    /// Some of the elements: a slice `a[i..j]`.
    Slice,
}

/// A use of (part of) a variable in an expression: whether it changes it
/// (passed `inout` or `set`), and the place, for messages.
struct Access<'e> {
    local: LocalId,
    path: Vec<Step>,
    write: bool,
    place: &'e TExpr,
}

/// The variable and the steps a place like `a[i].x` is made of, if `e` is
/// a place.
fn place_path(e: &TExpr) -> Option<(LocalId, Vec<Step>)> {
    let (base, step) = match &e.kind {
        TExprKind::Local(l) => return Some((*l, Vec::new())),
        TExprKind::Field(base, i) => (base, Step::Field(*i)),
        TExprKind::Index(base, index) => {
            let mut k = &**index;
            while let TExprKind::Convert(inner) = &k.kind {
                k = inner;
            }
            let at = match k.kind {
                TExprKind::Int(v) => Some(v),
                _ => None,
            };
            (base, Step::Index(at))
        }
        TExprKind::Payload(base, ..) => (base, Step::Payload),
        // A slice is some of the elements, at indexes not known here.
        TExprKind::Slice(base, ..) => (base, Step::Slice),
        TExprKind::ToSlice(inner) => return place_path(inner),
        _ => return None,
    };
    let (local, mut path) = place_path(base)?;
    path.push(step);
    Some((local, path))
}

/// Whether two accesses may reach the same memory: the same variable, and
/// neither goes to a different field or a different constant index than the
/// other at some step.
fn overlap(a: &Access<'_>, b: &Access<'_>) -> bool {
    a.local == b.local
        && a.path.iter().zip(&b.path).all(|pair| match pair {
            (Step::Field(x), Step::Field(y)) => x == y,
            (Step::Index(Some(x)), Step::Index(Some(y))) => x == y,
            _ => true,
        })
}

/// The accesses to variables in `e`, in evaluation order. `a.len` doesn't
/// access `a`'s contents: an array's length is constant, and a slice's
/// doesn't change through `&` (only its elements can).
fn accesses<'e>(e: &'e TExpr, out: &mut Vec<Access<'e>>) {
    match &e.kind {
        TExprKind::Ref(inner) => {
            let place = match &inner.kind {
                TExprKind::ToSlice(array) => &**array,
                _ => &**inner,
            };
            index_accesses(place, out);
            if let Some((local, path)) = place_path(place) {
                out.push(Access {
                    local,
                    path,
                    write: true,
                    place,
                });
            }
        }
        TExprKind::ArrayLen(inner) | TExprKind::ViewLen(inner) if place_path(inner).is_some() => {
            index_accesses(inner, out);
        }
        _ => match place_path(e) {
            Some((local, path)) => {
                index_accesses(e, out);
                out.push(Access {
                    local,
                    path,
                    write: false,
                    place: e,
                });
            }
            None => {
                for sub in subexprs(e) {
                    accesses(sub, out);
                }
            }
        },
    }
}

/// The accesses in the indexes of the place `e`.
fn index_accesses<'e>(e: &'e TExpr, out: &mut Vec<Access<'e>>) {
    match &e.kind {
        TExprKind::Index(base, index) => {
            index_accesses(base, out);
            accesses(index, out);
        }
        TExprKind::Slice(base, start, end) => {
            index_accesses(base, out);
            for bound in start.iter().chain(end) {
                accesses(bound, out);
            }
        }
        TExprKind::Field(base, _) | TExprKind::Payload(base, ..) | TExprKind::ToSlice(base) => {
            index_accesses(base, out)
        }
        _ => {}
    }
}

/// How an index or a slice bound is written in messages: a constant, a
/// variable's name, or `...`.
fn index_text(cx: &FnCx, index: &TExpr) -> String {
    let mut k = index;
    while let TExprKind::Convert(inner) = &k.kind {
        k = inner;
    }
    match &k.kind {
        TExprKind::Int(v) => v.to_string(),
        TExprKind::Local(l) if !cx.locals[*l].name.starts_with('$') => cx.locals[*l].name.clone(),
        _ => "...".to_owned(),
    }
}

/// How a place is written in messages: `p.x`, `a[i]`, `a[2]`, `a[...]`,
/// `a[i..]`.
pub(super) fn place_text(cx: &FnCx, e: &TExpr) -> Option<String> {
    Some(match &e.kind {
        TExprKind::Local(l) => cx.locals[*l].name.clone(),
        TExprKind::Field(base, i) => {
            let def = base.ty.as_struct()?;
            format!("{}.{}", place_text(cx, base)?, def.fields[*i as usize].name)
        }
        TExprKind::Index(base, index) => {
            format!("{}[{}]", place_text(cx, base)?, index_text(cx, index))
        }
        TExprKind::Slice(base, start, end) => {
            let bound =
                |b: &Option<Box<TExpr>>| b.as_deref().map_or(String::new(), |b| index_text(cx, b));
            format!(
                "{}[{}..{}]",
                place_text(cx, base)?,
                bound(start),
                bound(end)
            )
        }
        TExprKind::ToSlice(inner) => return place_text(cx, inner),
        _ => return None,
    })
}

/// Forget the facts about a place a call may have changed. Array and
/// slice elements have no facts, and a slice's length doesn't change.
pub(super) fn forget_place(cx: &mut FnCx, place: &TExpr) {
    match &place.kind {
        TExprKind::Local(l) if !cx.locals[*l].ty.is_view() => cx.env.forget(*l),
        TExprKind::Field(..) => {
            if let Some(Term::Field(l, off)) = place_term(place) {
                cx.env.forget_fields(l, off..off + flat_size(place.ty));
            }
        }
        _ => {}
    }
}

/// Forget the facts about every place `e` passes `inout` or `set`.
pub(super) fn forget_changed(cx: &mut FnCx, e: &TExpr) {
    let mut found = Vec::new();
    accesses(e, &mut found);
    for a in found.iter().filter(|a| a.write) {
        forget_place(cx, a.place);
    }
}

/// The parts of a divisor's range without 0: the negative values, then the
/// positive ones.
fn nonzero_parts(b: Range) -> impl Iterator<Item = Range> {
    let neg = (b.lo <= -1).then(|| Range {
        lo: b.lo,
        hi: b.hi.min(-1),
    });
    let pos = (b.hi >= 1).then(|| Range {
        lo: b.lo.max(1),
        hi: b.hi,
    });
    neg.into_iter().chain(pos)
}

/// The range of `a / b` (rounded toward zero) for a divisor `b` that isn't
/// 0. On each side of 0, the quotient only moves one way as either operand
/// grows, so its extremes are at the corners.
fn quotient_range(a: Range, b: Range) -> Range {
    nonzero_parts(b)
        .map(|b| {
            let vals = [a.lo / b.lo, a.lo / b.hi, a.hi / b.lo, a.hi / b.hi];
            Range {
                lo: *vals.iter().min().expect("four values"),
                hi: *vals.iter().max().expect("four values"),
            }
        })
        .reduce(Range::hull)
        .unwrap_or(a)
}

/// The range of `a % b` for a divisor `b` that isn't 0: smaller than `b` in
/// size, with the sign of `a`. (Not also "no further from 0 than `a`": the
/// range only depends on the divisor, so `a = (a + x) % m` in a loop has the
/// same range at every iteration, and the loop's head can keep it.)
fn remainder_range(a: Range, b: Range) -> Range {
    let m =
        b.lo.unsigned_abs()
            .max(b.hi.unsigned_abs())
            .saturating_sub(1);
    let m = i128::try_from(m).unwrap_or(i128::MAX);
    Range {
        lo: if a.lo >= 0 { 0 } else { -m },
        hi: if a.hi <= 0 { 0 } else { m },
    }
}

/// The smallest `2^k - 1` that is at least `x` (for `x >= 0`): no value
/// without a bit above those of `x` is larger.
fn all_ones(x: i128) -> i128 {
    let bits = 128 - x.leading_zeros();
    if bits >= 127 {
        i128::MAX
    } else {
        (1i128 << bits) - 1
    }
}

/// The upper bound of `a / b` or `a >> n` of a term `a` (plus a constant)
/// in `a_range`: when `a >= 0` and the operation can't grow it (`b >= 1`,
/// `n >= 0`), it's at most `a`; when also `a >= 1` and it shrinks it (`b >=
/// 2`, `n >= 1`), at most `a - 1`.
fn shrunk(a: Option<Linear>, a_range: Range, keeps: bool, shrinks: bool) -> Option<Linear> {
    let a = a?;
    if a_range.lo >= 1 && shrinks {
        a.plus(-1)
    } else if a_range.lo >= 0 && keeps {
        Some(a)
    } else {
        None
    }
}

/// Whether `x - y <= c` is known from the relations, for the value `x` (its
/// term, or the term plus a constant it's at most) and a term `y`.
fn at_most(cx: &FnCx, x: &Checked, y: Option<Linear>, c: i128) -> bool {
    let Some(y) = y else {
        return false;
    };
    [x.term, x.upper]
        .into_iter()
        .flatten()
        .any(|t| cx.env.diff_bound(t, y).is_some_and(|d| d <= c))
}

/// Whether `x <= y` is known, from their ranges or a relation.
fn proven_le(cx: &FnCx, x: &Checked, y: &Checked) -> bool {
    x.int_range().hi <= y.int_range().lo || at_most(cx, x, y.term, 0)
}

fn op_name(op: BinOp) -> &'static str {
    match op {
        BinOp::Add | BinOp::AddWrap | BinOp::AddSat => "addition",
        BinOp::Sub | BinOp::SubWrap | BinOp::SubSat => "subtraction",
        BinOp::Mul | BinOp::MulWrap | BinOp::MulSat => "multiplication",
        _ => "operation",
    }
}

/// The most elements of an array constant [`Checker::table_elem_range`]
/// looks at one by one; past it, the range of all its elements is used.
const TABLE_SCAN_LIMIT: usize = 4096;

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
                        ConstVal::Typed(..) | ConstVal::Table(..) | ConstVal::Expr(_) => None,
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
                            ConstVal::Typed(..) | ConstVal::Table(..) | ConstVal::Expr(_) => None,
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
    /// optional `?T` that holds it (which keeps the value: see
    /// [`Checker::consume`]).
    pub(super) fn coerce(
        &mut self,
        cx: &mut FnCx,
        c: Checked,
        target: Ty,
        span: Span,
    ) -> Option<Checked> {
        if c.ty() == target {
            return Some(c);
        }
        // A call that doesn't return stands for a value of any type.
        if c.ty() == Ty::Never && target != Ty::Unit {
            return Some(Checked::new(
                TExprKind::Never(Box::new(c.expr)),
                target,
                None,
            ));
        }
        if let Some(inner) = target.as_optional()
            && coercible(c.ty(), inner)
        {
            let value = self.coerce(cx, c, inner, span)?;
            self.consume(cx, &value.expr, span)?;
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
            let range = Some(c.int_range());
            return Some(c.converted(target, range));
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
        self.whole(cx, e.span, |ck, cx| ck.expr_inner(cx, e, expected))
    }

    /// Check an expression with `check`. If it's a whole expression (not
    /// part of one being checked), check it for exclusivity once it's done.
    pub(super) fn whole(
        &mut self,
        cx: &mut FnCx,
        span: Span,
        check: impl FnOnce(&mut Self, &mut FnCx) -> Option<Checked>,
    ) -> Option<Checked> {
        cx.expr_depth += 1;
        let out = check(self, cx);
        cx.expr_depth -= 1;
        if cx.expr_depth == 0
            && let Some(c) = &out
        {
            self.check_exclusive(cx, &c.expr, span);
        }
        out
    }

    /// Exclusivity (docs/memory.md): a place passed `inout` or `set` in an
    /// expression (with `&`, or as the receiver of a method that takes
    /// `inout self`) can't overlap anything else the expression uses.
    fn check_exclusive(&mut self, cx: &FnCx, e: &TExpr, span: Span) {
        let mut found = Vec::new();
        accesses(e, &mut found);
        let text = |a: &Access<'_>| {
            place_text(cx, a.place).unwrap_or_else(|| cx.locals[a.local].name.clone())
        };
        for (i, w) in found.iter().enumerate() {
            if !w.write {
                continue;
            }
            let Some(other) = found
                .iter()
                .enumerate()
                .find(|&(j, o)| j != i && !(o.write && j < i) && overlap(w, o))
                .map(|(_, o)| o)
            else {
                continue;
            };
            let (wt, ot) = (text(w), text(other));
            let msg = if other.write {
                format!(
                    "`{wt}` and `{ot}` are both passed `inout` or `set` in this expression, and may overlap"
                )
            } else {
                format!(
                    "`{wt}` is passed `inout` or `set`, so `{ot}` can't be used in the same expression"
                )
            };
            let mut d = Diagnostic::error(span, msg).with_help(
                "a place passed `inout` or `set` (with `&`, or to a method that takes `inout self`) needs exclusive access: nothing else in the expression may use it",
            );
            let pairs = || w.path.iter().zip(&other.path);
            let unknown_index = pairs().any(|pair| {
                matches!(pair, (Step::Index(a), Step::Index(b)) if a.is_none() || b.is_none())
            });
            if pairs().any(|(a, b)| *a == Step::Slice || *b == Step::Slice) {
                d = d.with_help(
                    "a slice of an array overlaps every element and every other slice of it",
                );
            } else if unknown_index {
                d = d.with_help(
                    "two elements of one array count as overlapping unless their indexes are different constants",
                );
            }
            self.diags.push(d);
            return;
        }
    }

    fn expr_inner(
        &mut self,
        cx: &mut FnCx,
        e: &ast::Expr,
        expected: Option<Ty>,
    ) -> Option<Checked> {
        if let Some(v) = self.untyped_int(cx, e) {
            return self.literal(v, e.span, expected.map(under_optionals));
        }
        // `args.len` and `args[i]` of a pack.
        if let Some(c) = self.pack_expr(cx, e) {
            return c;
        }
        match &e.kind {
            ExprKind::Spread(_) => {
                self.diags.push(
                    Diagnostic::error(e.span, "`..` passes a pack on, as a call's last argument")
                        .with_help("as in `print(fmt, ..args)`, for a function with a pack"),
                );
                None
            }
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
                _ => self.call(cx, callee, args, e.span, false, expected),
            },
            ExprKind::Dot(name) => self.dot_variant(name, None, e.span, expected, cx),
            ExprKind::Try(call) => self.try_call(cx, call, e.span, expected),
            ExprKind::Catch {
                value,
                binding,
                handler,
            } => self.catch(cx, value, binding.as_ref(), handler, true, expected),
            ExprKind::Ref(_) => {
                self.diags.push(
                    Diagnostic::error(
                        e.span,
                        "`&` marks a call's argument passed `inout` or `set`, and is only used there",
                    )
                    .with_help("to copy a value, use it without `&`"),
                );
                None
            }
            ExprKind::Throw(_) => {
                self.diags.push(
                    Diagnostic::error(e.span, "`throw` is a statement").with_help(
                        "in an expression, it can only follow `??`: `opt ?? throw .name`",
                    ),
                );
                None
            }
            ExprKind::Field(base, member) => self.field(cx, base, member, e.span, expected),
            ExprKind::ArrayLit(elems) => {
                self.array_literal(cx, elems, e.span, expected.map(under_optionals))
            }
            ExprKind::ArrayRepeat(value, count) => {
                self.array_repeat(cx, value, count, e.span, expected.map(under_optionals))
            }
            ExprKind::Index(base, _) | ExprKind::TypeArgs(base, _)
                if self.names_function(cx, base) =>
            {
                let name = callee_name(base);
                self.diags.push(
                    Diagnostic::error(e.span, format!("`{name}` is a function; call it"))
                        .with_help(format!("as in `{name}[u32](...)`")),
                );
                None
            }
            ExprKind::Index(base, index) => self.index(cx, base, index),
            ExprKind::Slice(base, start, end) => {
                self.slice(cx, base, start.as_deref(), end.as_deref(), e.span)
            }
            ExprKind::TypeArgs(base, _) => {
                self.diags.push(
                    Diagnostic::error(
                        e.span,
                        format!(
                            "`{}` is not a generic function, so these brackets would be an index, which is one integer",
                            callee_name(base)
                        ),
                    )
                    .with_help("several items, or a type, in brackets are the type arguments of a generic function: `max[u32](a, b)`"),
                );
                None
            }
            ExprKind::StructLit(ty, fields) => {
                self.struct_literal(cx, ty, fields, e.span, expected.map(under_optionals))
            }
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
    fn type_path(&mut self, cx: &mut FnCx, e: &ast::Expr) -> Option<Option<Ty>> {
        match &e.kind {
            // `Pair[u8, bool]`: a generic type with its arguments.
            ExprKind::Index(base, _) | ExprKind::TypeArgs(base, _) => {
                if self.type_path(cx, base)?.is_none() {
                    return Some(None);
                }
                let t = expr_type(e)?;
                Some(self.resolve_type(cx, &t))
            }
            ExprKind::Name(name) if cx.lookup(name).is_none() => {
                // `Self` and type parameters: for their associated
                // functions and constants.
                if name == super::SELF {
                    return cx.self_ty.map(Some);
                }
                if let Some(p) = Self::type_param(cx, name)
                    && p.value_param().is_none()
                {
                    return Some(Some(p));
                }
                match self.pkgs[cx.pkg].items.get(name) {
                    Some(&Item::Type(ty)) => Some(Some(ty)),
                    None if name == "Ordering" => Some(Some(Ty::ordering())),
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
    /// `ty`, with its payload fields given in order. For a generic enum
    /// named without its arguments (`Either.left(x)`), they're inferred from
    /// the payload and the expected type.
    fn enum_variant(
        &mut self,
        cx: &mut FnCx,
        ty: Ty,
        member: &ast::Ident,
        args: Option<&[ast::Expr]>,
        span: Span,
        expected: Option<Ty>,
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
        let shown = if ty.is_decl_form() {
            def.name.clone()
        } else {
            ty.to_string()
        };
        let fields = &variant.fields;
        let args = match (args, fields.is_empty()) {
            (None, true) => &[][..],
            (None, false) => {
                self.error(
                    span,
                    format!("`{shown}.{name}` has a payload: give it as `{shown}.{name}(...)`"),
                );
                return None;
            }
            (Some(_), true) => {
                self.error(
                    span,
                    format!("`{shown}.{name}` has no payload, so it's written without parentheses"),
                );
                return None;
            }
            (Some(args), false) => args,
        };
        if args.len() != fields.len() {
            self.error(
                span,
                format!(
                    "`{shown}.{name}` has {} payload field(s), but {} value(s) were given",
                    fields.len(),
                    args.len()
                ),
            );
            return None;
        }
        let (ty, mut pre) = if ty.is_decl_form() {
            let values: Vec<(Ty, &ast::Expr)> = fields.iter().map(|f| f.ty).zip(args).collect();
            let what = format!("`{shown}.{name}`");
            self.infer_instance(cx, ty, &values, expected, span, &what)?
        } else {
            (ty, args.iter().map(|_| None).collect())
        };
        let def = ty.as_enum().expect("an enum");
        let fields = &def.variants[i].fields;
        let mut values = Vec::new();
        let mut ok = true;
        for (k, (arg, f)) in args.iter().zip(fields).enumerate() {
            let c = match pre[k].take() {
                Some(c) => Some(c),
                None => self.expr(cx, arg, Some(f.ty)),
            };
            match c
                .and_then(|c| self.coerce(cx, c, f.ty, arg.span))
                .filter(|c| self.consume(cx, &c.expr, arg.span).is_some())
            {
                Some(c) => values.push(c.expr),
                None => ok = false,
            }
        }
        ok.then(|| Checked::new(TExprKind::Variant(i as u32, values), ty, None))
    }

    /// Whether `e` builds a value of a generic struct or enum named
    /// without its arguments (`Pair{...}`, `Either.left(x)`): it may infer
    /// them itself, or take them from the context.
    pub(super) fn generic_literal(&self, cx: &FnCx, e: &ast::Expr) -> bool {
        let names_generic = |t: &ast::Expr| {
            let item = match &t.kind {
                ExprKind::Name(n) if cx.lookup(n).is_none() => self.pkgs[cx.pkg].items.get(n),
                ExprKind::Field(base, member) => match &base.kind {
                    ExprKind::Name(p) => self
                        .imported(cx, p)
                        .and_then(|pkg| self.pkgs[pkg].items.get(&member.name)),
                    _ => None,
                },
                _ => None,
            };
            matches!(item, Some(Item::Type(ty)) if ty.is_decl_form())
        };
        match &e.kind {
            ExprKind::Paren(inner) => self.generic_literal(cx, inner),
            ExprKind::StructLit(ty, _) => {
                let as_expr = |id: &ast::Ident| ast::Expr {
                    kind: ExprKind::Name(id.name.clone()),
                    span: id.span,
                };
                match ty {
                    ast::TypeExpr::Named(id) => names_generic(&as_expr(id)),
                    ast::TypeExpr::Qualified(p, id) => names_generic(&ast::Expr {
                        kind: ExprKind::Field(Box::new(as_expr(p)), id.clone()),
                        span: id.span,
                    }),
                    _ => false,
                }
            }
            ExprKind::Call(callee, _) => {
                matches!(&callee.kind, ExprKind::Field(base, _) if names_generic(base))
            }
            ExprKind::Field(base, _) => names_generic(base),
            _ => false,
        }
    }

    /// The instance a literal (or a variant) of `decl`, a generic struct or
    /// enum named without its arguments, builds: its arguments are inferred
    /// like a call's (docs/generics.md), from `values` (each with its
    /// field's type in the declaration), in order, then from the type
    /// `expected`. A value that takes its type from the context (a literal,
    /// `none`, `.name`, an array literal) doesn't fix an argument; a literal
    /// of a generic type without its arguments waits for the expected type
    /// too, and fixes them if that doesn't. Returns the values checked on
    /// the way (by position), to be converted to their fields' types.
    /// `what` names the literal in messages.
    pub(super) fn infer_instance(
        &mut self,
        cx: &mut FnCx,
        decl: Ty,
        values: &[(Ty, &ast::Expr)],
        expected: Option<Ty>,
        span: Span,
        what: &str,
    ) -> Option<(Ty, Vec<Option<Checked>>)> {
        let mut inf = Inference::new(decl.decl_params());
        let mut checked: Vec<Option<Checked>> = values.iter().map(|_| None).collect();
        let mut ok = true;
        let mut later = Vec::new();
        for (k, &(fty, e)) in values.iter().enumerate() {
            if inf.known(fty) || self.untyped_int(cx, e).is_some() || needs_context(e) {
                continue;
            }
            if self.generic_literal(cx, e) {
                later.push(k);
                continue;
            }
            match self.expr(cx, e, None) {
                Some(c) => {
                    inf.unify(fty, c.ty(), e.span);
                    checked[k] = Some(c);
                }
                None => ok = false,
            }
        }
        if !inf.all_known()
            && let Some(t) = expected
        {
            inf.unify(decl, under_optionals(t), span);
        }
        for k in later {
            let (fty, e) = values[k];
            if inf.known(fty) {
                continue;
            }
            match self.expr(cx, e, None) {
                Some(c) => {
                    inf.unify(fty, c.ty(), e.span);
                    checked[k] = Some(c);
                }
                None => ok = false,
            }
        }
        if !ok {
            return None;
        }
        if let Some(p) = inf.unknown() {
            let params: Vec<String> = decl.decl_params().iter().map(Ty::to_string).collect();
            self.diags.push(
                Diagnostic::error(span, format!("cannot tell what `{p}` is in {what}"))
                    .with_help(format!(
                        "write the arguments, as in `{}[{}]`, or give the value a type from context",
                        nominal_name(decl),
                        params.join(", ")
                    ))
                    .with_help("an integer literal doesn't fix a generic argument"),
            );
            return None;
        }
        let inst = decl.instantiate(&inf.types());
        if !self.check_type_bounds(inst, span) {
            return None;
        }
        Some((inst, checked))
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
            Some(ty @ Ty::Enum(_)) => self.enum_variant(cx, ty, name, args, span, None),
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
    fn throwing_call(
        &mut self,
        cx: &mut FnCx,
        e: &ast::Expr,
        what: &str,
        expected: Option<Ty>,
    ) -> Option<Checked> {
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
        let c = self.call(cx, callee, args, inner.span, true, expected)?;
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
    fn try_call(
        &mut self,
        cx: &mut FnCx,
        call: &ast::Expr,
        span: Span,
        expected: Option<Ty>,
    ) -> Option<Checked> {
        self.check_not_in_defer(cx, span, "`try`")?;
        let c = self.throwing_call(cx, call, "try", expected)?;
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
        expected: Option<Ty>,
    ) -> Option<Checked> {
        let c = self.throwing_call(cx, value, "catch", expected)?;
        let (ty, err) = c.ty().as_result().expect("a result");
        let entry = cx.env.clone();
        // When the call fails, the variables it was to assign (`set`) aren't.
        for l in std::mem::take(&mut cx.call_sets) {
            cx.env.declare_uninit(l);
        }
        let (local, handler) = match handler {
            ast::CatchHandler::Value(v) => {
                let d = self.expr(cx, v, Some(ty));
                let d = self.coerce(cx, d?, ty, v.span)?;
                self.consume(cx, &d.expr, v.span)?;
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
                // The block's statements are expressions of their own.
                let depth = std::mem::replace(&mut cx.expr_depth, 0);
                let body = self.block(cx, &b.stmts);
                cx.expr_depth = depth;
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
                        .with_help("end it with `return`, `throw`, `break`, `continue`, or a call to a `never` function like `os.exit`")
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
        Some(self.coerce(cx, c, err, value.span)?.expr)
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

    /// `T{name: value, ...}`: every field exactly once, in any order. For
    /// a generic struct named without its arguments (`Pair{...}`), they're
    /// inferred from the fields' values and the expected type.
    fn struct_literal(
        &mut self,
        cx: &mut FnCx,
        ty: &ast::TypeExpr,
        inits: &[ast::FieldInit],
        span: Span,
        expected: Option<Ty>,
    ) -> Option<Checked> {
        let sty = self.resolve_type_or_decl(cx, ty)?;
        let Some(def) = sty.as_struct() else {
            self.error(ty.span(), format!("`{sty}` is not a struct"));
            return None;
        };
        if def.pkg != cx.pkg && def.fields.iter().any(|f| !f.is_pub) {
            self.private_literal(&def, sty, span);
            return None;
        }
        let mut pre: Vec<Option<Checked>> = inits.iter().map(|_| None).collect();
        let (sty, def) = if sty.is_decl_form() {
            // The fields given once, with known names, fix the arguments.
            let mut seen = Vec::new();
            let mut idx = Vec::new();
            let mut values = Vec::new();
            for (k, init) in inits.iter().enumerate() {
                if let Some((i, fty)) = def.field(&init.name.name)
                    && !seen.contains(&i)
                {
                    seen.push(i);
                    idx.push(k);
                    values.push((fty, &init.value));
                }
            }
            let what = format!("this `{}` literal", def.name);
            let (inst, checked) = self.infer_instance(cx, sty, &values, expected, span, &what)?;
            for (k, c) in idx.into_iter().zip(checked) {
                pre[k] = c;
            }
            (inst, inst.as_struct().expect("a struct"))
        } else {
            (sty, def)
        };
        let mut given = vec![false; def.fields.len()];
        let mut out = Vec::new();
        let mut ok = true;
        for (k, init) in inits.iter().enumerate() {
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
            let c = match pre[k].take() {
                Some(c) => Some(c),
                None => self.expr(cx, &init.value, Some(fty)),
            };
            match c
                .and_then(|c| self.coerce(cx, c, fty, init.value.span))
                .filter(|c| self.consume(cx, &c.expr, init.value.span).is_some())
            {
                Some(c) => out.push((i as u32, c.expr)),
                None => ok = false,
            }
        }
        // `unsafe` code may leave an `@uninit` field unwritten.
        let in_unsafe = cx.unsafe_depth > 0;
        let missing: Vec<&Field> = def
            .fields
            .iter()
            .zip(&given)
            .filter(|&(f, &g)| !g && !(f.uninit && in_unsafe))
            .map(|(f, _)| f)
            .collect();
        if !missing.is_empty() {
            let s = if missing.len() == 1 { "" } else { "s" };
            let names: Vec<String> = missing.iter().map(|f| format!("`{}`", f.name)).collect();
            let help = match missing.iter().find(|f| f.uninit) {
                Some(f) => format!(
                    "`{}` is `@uninit`: only `unsafe` code may leave it out",
                    f.name
                ),
                None => "every field must be given a value; there are no defaults".to_owned(),
            };
            self.diags.push(
                Diagnostic::error(
                    span,
                    format!("missing field{s} {} in this `{sty}`", names.join(", ")),
                )
                .with_help(help),
            );
            ok = false;
        }
        ok.then(|| Checked::new(TExprKind::StructLit(out), sty, None))
    }

    /// Report a literal of a struct with private fields outside its
    /// package, pointing to a public function of that package that makes
    /// one without `self` (`new` if there's one).
    fn private_literal(&mut self, def: &StructDef, sty: Ty, span: Span) {
        let decl = sty.decl();
        let mut makers: Vec<(bool, usize, &str)> = self
            .sigs
            .iter()
            .filter(|sig| {
                sig.pkg == def.pkg && sig.is_pub && !sig.has_self && sig.ret.decl() == decl
            })
            .map(|sig| {
                let last = sig.name.rsplit('.').next().unwrap_or_default();
                (last != "new", sig.params.len(), sig.name.as_str())
            })
            .collect();
        makers.sort();
        let mut d = Diagnostic::error(
            span,
            format!(
                "`{}` has private fields, so it can only be built in package `{}`",
                def.name, self.pkgs[def.pkg].path
            ),
        );
        if let Some(&(_, params, name)) = makers.first() {
            let pkg = def.name.rsplit_once('.').map_or("", |(p, _)| p);
            let args = if params == 0 { "" } else { "..." };
            d = d.with_help(format!("use `{pkg}.{name}({args})`"));
        }
        self.diags.push(d);
    }

    /// The element type and length (`None` for a slice) that an array literal
    /// is expected to have, from its context.
    fn expected_array(expected: Option<Ty>) -> (Option<Ty>, Option<Len>) {
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
        found: Len,
        want: Option<Len>,
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
        self.check_literal_len(Len::Known(n), want_len, expected, span)?;
        let mut ok = true;
        let mut out = Vec::new();
        for (e, done) in elems.iter().zip(checked) {
            let c = match done {
                Some(c) => Some(c),
                None => self.expr(cx, e, Some(elem)),
            };
            match c
                .and_then(|c| self.coerce(cx, c, elem, e.span))
                .filter(|c| self.consume(cx, &c.expr, e.span).is_some())
            {
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
        let n = self.array_len_arg(cx, count);
        let v = self.expr(cx, value, want_elem);
        let (n, v) = (n?, v?);
        let v = match want_elem {
            Some(t) => self.coerce(cx, v, t, value.span)?,
            None => v,
        };
        let elem = v.ty();
        self.check_elem(elem, "arrays", value.span)?;
        self.check_literal_len(n, want_len, expected, span)?;
        if !elem.is_copy() {
            let mut params = Vec::new();
            elem.params(&mut params);
            let param = params.into_iter().find(|p| !p.is_copy()).unwrap_or(elem);
            self.diags.push(
                Diagnostic::error(
                    value.span,
                    format!("`[value; {n}]` copies its value, but `{param}` isn't `Copy`"),
                )
                .with_help(format!("add the bound `[{param}: Copy]`")),
            );
            return None;
        }
        Some(Checked::new(
            TExprKind::ArrayRepeat(Box::new(v.expr)),
            Ty::array_of(elem, n),
            None,
        ))
    }

    /// The value parameter `p` (of type `usize`), as an array's length: its
    /// local, a term.
    pub(super) fn param_len(&self, cx: &FnCx, p: Ty) -> Checked {
        let local = cx
            .value_local(p)
            .expect("a value parameter of the function being checked");
        let term = Term::Local(local);
        let mut c = Checked::new(
            TExprKind::Local(local),
            self.usize_ty(),
            super::read_range(cx, term),
        );
        c.term = Some(Linear::of(term));
        c
    }

    /// The value of an associated constant, `p` (see
    /// [`Checker::assoc_const`]), of type `it`: a number, or for a type
    /// parameter's (`E.MAX_LEN`), the local an instance assigns it, a term.
    pub(super) fn assoc_const_expr(
        &mut self,
        cx: &FnCx,
        p: Ty,
        it: IntTy,
        span: Span,
    ) -> Option<Checked> {
        if let Some(v) = p.as_value() {
            return Some(Checked::new(
                TExprKind::Int(v),
                Ty::Int(it),
                Some(Range::exact(v)),
            ));
        }
        let Some(local) = cx.value_local(p) else {
            self.error(
                span,
                format!("`{p}` isn't known here: it's known in a function's body"),
            );
            return None;
        };
        let term = Term::Local(local);
        let mut c = Checked::new(
            TExprKind::Local(local),
            Ty::Int(it),
            super::read_range(cx, term),
        );
        c.term = Some(Linear::of(term));
        Some(c)
    }

    /// `a.len` of an array: the constant length of its type, or the value
    /// parameter that's its length (`[N]T`).
    fn array_len(&self, cx: &FnCx, array: TExpr) -> Checked {
        let usize_ty = self.usize_ty();
        let (_, len) = array.ty.as_array().expect("an array");
        let kind = TExprKind::ArrayLen(Box::new(array));
        match len {
            Len::Known(n) => {
                let n = i128::from(n);
                Checked::new(kind, usize_ty, Some(Range::exact(n)))
            }
            Len::Param(p) => {
                let n = self.param_len(cx, p);
                let mut c = Checked::new(kind, usize_ty, n.range);
                c.term = n.term;
                c
            }
        }
    }

    /// The length of a view (a slice or `str`): a term when the view is a
    /// local, so conditions like `i < xs.len` relate to it.
    pub(super) fn view_len(&self, cx: &FnCx, view: TExpr) -> Checked {
        // A length is at most the largest `isize`: no object is bigger.
        let any_len = Range {
            lo: 0,
            hi: self.len_max(),
        };
        let term = match view.kind {
            TExprKind::Local(l) => Some(Term::Len(l)),
            // `s.bytes()` has the length of `s`.
            TExprKind::Bytes(ref s) => match s.kind {
                TExprKind::Local(l) => Some(Term::Len(l)),
                _ => None,
            },
            _ => None,
        };
        let range = term
            .and_then(|t| super::read_range(cx, t))
            .and_then(|r| r.intersect(any_len))
            .unwrap_or(any_len);
        // A string literal's length is known.
        let literal = match &view.kind {
            TExprKind::Str(id) => Some(self.strings[*id].len() as i128),
            TExprKind::Bytes(s) => match s.kind {
                TExprKind::Str(id) => Some(self.strings[id].len() as i128),
                _ => None,
            },
            _ => None,
        };
        let range = literal.map_or(range, Range::exact);
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
                self.diags.push(
                    Diagnostic::error(
                        base.span,
                        "a `str` can't be indexed: a byte is not a character",
                    )
                    .with_help("index its bytes: `s.bytes()[i]`"),
                );
                return None;
            }
            other => {
                self.error(base.span, format!("`{other}` cannot be indexed"));
                return None;
            }
        };
        if num(i.ty()).is_none() {
            self.error(
                index.span,
                format!("an index must be an integer, found `{}`", i.ty()),
            );
            return None;
        }

        let r = i.int_range();
        if cx.comptime {
            let in_bounds = match b.ty().as_array().and_then(|(_, n)| n.known()) {
                Some(n) => r.lo >= 0 && r.hi < i128::from(n),
                None => false,
            };
            let range = match elem {
                Ty::Int(_) => self.table_elem_range(&b.expr, r),
                _ => None,
            };
            let c = Checked::new(
                TExprKind::Index(Box::new(b.expr), Box::new(i.expr)),
                elem,
                range,
            );
            return Some(if in_bounds { c } else { c.unproven(index.span) });
        }
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
            Some((_, Len::Known(n))) => (r.hi < i128::from(n), format!("the length is {n}")),
            arr => {
                let len = match arr {
                    Some((_, Len::Param(p))) => self.param_len(cx, p),
                    _ => self.view_len_of(cx, &b),
                };
                let lr = len.int_range();
                let by_range = r.hi < lr.lo;
                let by_rel = at_most(cx, &i, len.term, -1);
                let desc = if let Some((_, Len::Param(p))) = arr {
                    format!("the length is `{p}`, which can be {lr}")
                } else if lr.lo == lr.hi {
                    format!("the length is {lr}")
                } else if lr.lo == 0 && lr.hi == self.len_max() {
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
        let range = match elem {
            Ty::Int(_) => self.table_elem_range(&b.expr, r),
            _ => None,
        };
        Some(Checked::new(
            TExprKind::Index(Box::new(b.expr), Box::new(i.expr)),
            elem,
            range,
        ))
    }

    /// The length of the view `v`, with what's known about it when `v` is
    /// a slice `base[start..end]`: its range, and with a constant start,
    /// `end` minus it as a term (`xs[..n].len` is `n`).
    pub(super) fn view_len_of(&self, cx: &FnCx, v: &Checked) -> Checked {
        let mut len = self.view_len(cx, v.expr.clone());
        if let Some(sl) = v.len {
            let r = len.int_range();
            len.range = Some(r.intersect(sl.range).unwrap_or(sl.range));
            if len.term.is_none() && sl.start.lo == sl.start.hi {
                len.term = sl.end.and_then(|e| e.plus(-sl.start.lo));
            }
        }
        len
    }

    /// `base[start..end]` (either bound may be missing), a view of part of
    /// an array or slice. It must be proven that `0 <= start <= end <=
    /// base.len`.
    fn slice(
        &mut self,
        cx: &mut FnCx,
        base: &ast::Expr,
        start: Option<&ast::Expr>,
        end: Option<&ast::Expr>,
        span: Span,
    ) -> Option<Checked> {
        let b = self.expr(cx, base, None);
        // Untyped bounds are `usize`; any integer type is accepted.
        let usize_ty = self.usize_ty();
        let s = start.map(|e| self.expr(cx, e, Some(usize_ty)));
        let e = end.map(|e| self.expr(cx, e, Some(usize_ty)));
        let b = b?;
        let s = s.map_or(Some(None), |c| c.map(Some))?;
        let e = e.map_or(Some(None), |c| c.map(Some))?;
        // The base as a view, and its length.
        let (view, len) = match b.ty() {
            Ty::Array(_) => {
                let (elem, n) = b.ty().as_array().expect("an array");
                let len = match n {
                    Len::Known(n) => {
                        let n = i128::from(n);
                        Checked::new(TExprKind::Int(n), usize_ty, Some(Range::exact(n)))
                    }
                    Len::Param(p) => self.param_len(cx, p),
                };
                let view =
                    Checked::new(TExprKind::ToSlice(Box::new(b.expr)), Ty::slice(elem), None);
                (view, len)
            }
            Ty::Slice(_) => {
                let len = self.view_len_of(cx, &b);
                (b, len)
            }
            // In code that runs when compiling, the evaluator checks the
            // bounds, and that they don't split a character.
            Ty::Str if cx.comptime => {
                for (c, ast) in [(&s, start), (&e, end)] {
                    if let (Some(c), Some(ast)) = (c, ast)
                        && num(c.ty()).is_none()
                    {
                        self.error(
                            ast.span,
                            format!("a slice's bounds must be integers, found `{}`", c.ty()),
                        );
                        return None;
                    }
                }
                let slice = TExprKind::Slice(
                    Box::new(b.expr),
                    s.map(|c| Box::new(c.expr)),
                    e.map(|c| Box::new(c.expr)),
                );
                return Some(Checked::new(slice, Ty::Str, None).unproven(span));
            }
            Ty::Str => {
                self.diags.push(
                    Diagnostic::error(
                        base.span,
                        "a `str` can't be sliced: a slice could split a character",
                    )
                    .with_help("slice its bytes instead: `s.bytes()[i..j]` is a `[]u8`"),
                );
                return None;
            }
            other => {
                self.error(base.span, format!("`{other}` cannot be sliced"));
                return None;
            }
        };
        for (c, ast) in [(&s, start), (&e, end)] {
            if let (Some(c), Some(ast)) = (c, ast)
                && num(c.ty()).is_none()
            {
                self.error(
                    ast.span,
                    format!("a slice's bounds must be integers, found `{}`", c.ty()),
                );
                return None;
            }
        }
        if cx.comptime {
            let ty = view.ty();
            let kind = TExprKind::Slice(
                Box::new(view.expr),
                s.map(|c| Box::new(c.expr)),
                e.map(|c| Box::new(c.expr)),
            );
            return Some(Checked::new(kind, ty, None).unproven(span));
        }

        // How the code names a bound and the base, for help.
        let name = |e: Option<&ast::Expr>| match e.map(|e| &e.kind) {
            Some(ExprKind::Name(n)) if !n.starts_with('$') => Some(n.clone()),
            _ => None,
        };
        let len_text = match name(Some(base)) {
            Some(xs) => format!("`{xs}.len`"),
            None => "the length".to_owned(),
        };
        let can = |r: Range| if r.lo == r.hi { "is" } else { "can be" };
        let len_r = len.int_range();
        let len_desc = if len_r.lo == len_r.hi {
            format!("the length is {len_r}")
        } else if len_r.lo == 0 && len_r.hi == self.len_max() {
            "nothing is known about the length".to_owned()
        } else {
            format!("the length can be {len_r}")
        };
        let mut errors = Vec::new();
        let zero = Checked::new(TExprKind::Int(0), usize_ty, Some(Range::exact(0)));
        let first = s.as_ref().unwrap_or(&zero);
        let last = e.as_ref().unwrap_or(&len);
        // `0 <= start`, or `0 <= end` without a start.
        let low = match (&s, &e) {
            (Some(c), _) => start.map(|a| (c, a, "start")),
            (None, Some(c)) => end.map(|a| (c, a, "end")),
            (None, None) => None,
        };
        if let Some((c, ast, which)) = low
            && c.int_range().lo < 0
        {
            let r = c.int_range();
            errors.push(
                Diagnostic::error(
                    ast.span,
                    format!("cannot prove that this slice's {which} is not negative"),
                )
                .with_help(format!("the {which} {} {r}", can(r)))
                .with_help("check it first, or use an unsigned type"),
            );
            self.diags.extend(errors);
            return None;
        }
        // `start <= end` (the length, without an end).
        if let Some(sc) = &s
            && !proven_le(cx, sc, last)
        {
            let r = sc.int_range();
            let d = match &e {
                Some(ec) => {
                    let er = ec.int_range();
                    let check = match (name(start), name(end)) {
                        (Some(i), Some(j)) => format!("check it first (`if {i} <= {j}`)"),
                        _ => "check them first, as in `if i <= j`".to_owned(),
                    };
                    Diagnostic::error(
                        span,
                        "cannot prove that this slice's start is at most its end",
                    )
                    .with_help(format!(
                        "the start {} {r}, and the end {} {er}",
                        can(r),
                        can(er)
                    ))
                    .with_help(check)
                }
                None => {
                    let check = match name(start) {
                        Some(i) => format!(
                            "check it first (`if {i} <= {}`)",
                            len_text.trim_matches('`')
                        ),
                        None => format!("check it against {len_text} first"),
                    };
                    Diagnostic::error(
                        start.map_or(span, |a| a.span),
                        "cannot prove that this slice's start is at most the length",
                    )
                    .with_help(format!("the start {} {r}, and {len_desc}", can(r)))
                    .with_help(check)
                }
            };
            errors.push(d);
        }
        // `end <= base.len`.
        if let (Some(ec), Some(end_ast)) = (&e, end)
            && !proven_le(cx, ec, &len)
        {
            let r = ec.int_range();
            let check = match name(end) {
                Some(j) => format!(
                    "check it first (`if {j} <= {}`)",
                    len_text.trim_matches('`')
                ),
                None => format!("check it against {len_text} first"),
            };
            errors.push(
                Diagnostic::error(
                    end_ast.span,
                    "cannot prove that this slice's end is at most the length",
                )
                .with_help(format!("the end {} {r}, and {len_desc}", can(r)))
                .with_help(check),
            );
        }
        if !errors.is_empty() {
            self.diags.extend(errors);
            return None;
        }

        // The length, `end - start`: from the ranges, and from relations
        // between the bounds.
        let (fr, lr) = (first.int_range(), last.int_range());
        let diff = |x: &Checked, y: &Checked| match (x.term, y.term) {
            (Some(x), Some(y)) => cx.env.diff_bound(x, y),
            _ => None,
        };
        let mut lo = lr.lo.saturating_sub(fr.hi).max(0);
        if let Some(c) = diff(first, last) {
            lo = lo.max(c.saturating_neg());
        }
        let mut hi = lr.hi.saturating_sub(fr.lo).min(self.len_max());
        if let Some(c) = diff(last, first) {
            hi = hi.min(c);
        }
        let info = SliceLen {
            range: Range { lo: lo.min(hi), hi },
            end: last.term,
            start: fr,
        };
        let ty = view.ty();
        let kind = TExprKind::Slice(
            Box::new(view.expr),
            s.map(|c| Box::new(c.expr)),
            e.map(|c| Box::new(c.expr)),
        );
        let mut out = Checked::new(kind, ty, None);
        out.len = Some(info);
        Some(out)
    }

    /// The range of an integer element `base[i]`, with `i` in `index`, when
    /// `base` is an array constant or a row of one: the smallest and the
    /// largest of the elements `i` can pick (of all the constant's elements
    /// if there are too many to look at).
    fn table_elem_range(&self, base: &TExpr, index: Range) -> Option<Range> {
        // The indexes from the constant down, as ranges.
        let mut ranges = vec![index];
        let mut e = base;
        let id = loop {
            match &e.kind {
                TExprKind::Table(id) => break *id,
                TExprKind::Index(inner, k) => {
                    let mut k = &**k;
                    while let TExprKind::Convert(x) = &k.kind {
                        k = x;
                    }
                    let r = match k.kind {
                        TExprKind::Int(v) => Range::exact(v),
                        _ => Range {
                            lo: 0,
                            hi: i128::MAX,
                        },
                    };
                    ranges.push(r);
                    e = inner;
                }
                _ => return None,
            }
        };
        ranges.reverse();
        let table = &self.tables[id];
        let mut dims = Vec::new();
        let mut ty = table.ty;
        while let Some((elem, n)) = ty.as_known_array() {
            dims.push(n as usize);
            ty = elem;
        }
        // The positions the indexes can pick: a box, one range per dimension.
        let mut boxed: Vec<(usize, usize)> = Vec::new();
        let mut count: usize = 1;
        for (k, &n) in dims.iter().enumerate() {
            if n == 0 {
                return None;
            }
            let (lo, hi) = match ranges.get(k) {
                Some(r) => (
                    r.lo.clamp(0, n as i128 - 1) as usize,
                    r.hi.clamp(0, n as i128 - 1) as usize,
                ),
                None => (0, n - 1),
            };
            count = count.saturating_mul(hi - lo + 1);
            boxed.push((lo, hi));
        }
        let picked: Box<dyn Iterator<Item = i128>> = if count <= TABLE_SCAN_LIMIT {
            let mut flat = vec![0usize];
            for (&(lo, hi), &n) in boxed.iter().zip(&dims) {
                flat = flat
                    .iter()
                    .flat_map(|&f| (lo..=hi).map(move |i| f * n + i))
                    .collect();
            }
            Box::new(flat.into_iter().map(|f| table.values[f]))
        } else {
            Box::new(table.values.iter().copied())
        };
        picked.fold(None, |acc: Option<Range>, v| {
            Some(acc.map_or(Range::exact(v), |r| r.hull(Range::exact(v))))
        })
    }

    fn name(&mut self, cx: &mut FnCx, name: &str, span: Span) -> Option<Checked> {
        if let Some(local) = cx.lookup(name) {
            if cx.failed.contains(&local) {
                return None;
            }
            // A value known when compiling is its literal, except a `str` in
            // code that runs when compiling, which keeps where it comes from
            // (the evaluator has its value).
            if let Some(v) = cx.ct_values.get(&local).cloned()
                && !(cx.comptime && matches!(v, super::eval::Value::Str(_)))
            {
                return self.materialize_ct(&v, cx.locals[local].ty, span);
            }
            if cx.env.is_uninit(local) {
                if self.moved_error(cx, local, span) {
                    return None;
                }
                let help = if cx.set_params.contains(&local) {
                    "a `set` parameter starts unassigned: the function assigns it"
                } else {
                    "assign it on every path that leads here"
                };
                self.diags.push(
                    Diagnostic::error(span, format!("`{name}` is used before it's assigned"))
                        .with_help(help),
                );
                return None;
            }
            let ty = cx.locals[local].ty;
            let term = Term::Local(local);
            let mut c = Checked::new(TExprKind::Local(local), ty, super::read_range(cx, term));
            c.term = type_range(ty).map(|_| Linear::of(term));
            return Some(c);
        }
        if let Some(&item) = self.pkgs[cx.pkg].items.get(name) {
            return self.item_value(item, name, span);
        }
        if name == super::TARGET && self.imported(cx, name).is_none() {
            let e = self.target_value();
            return Some(Checked::new(e.kind, e.ty, None));
        }
        if let Some(p) = &cx.pack
            && p.name == name
        {
            self.diags.push(
                Diagnostic::error(span, format!("`{name}` is a pack, not a value"))
                    .with_help(format!(
                        "use `{name}[i]`, with `i` known when compiling, `{name}.len`, or pass it on with `..{name}`"
                    )),
            );
            return None;
        }
        // In a trait or an `impl`, `MAX_LEN` is `Self.MAX_LEN`.
        if let Some(s) = cx.self_ty
            && let Some((p, it)) = self.assoc_const(s, name)
        {
            return self.assoc_const_expr(cx, p, it, span);
        }
        let msg = if self.imported(cx, name).is_some() {
            format!("`{name}` is a package; use one of its members, like `{name}.something`")
        } else if Self::type_param(cx, name).is_some() || primitive(name, self.ptr_bits).is_some() {
            format!("`{name}` is a type, not a value")
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
    /// there's a standard package of that name), and return true. Also true
    /// for a failed local (see [`FnCx::failed`]), without an error.
    fn unknown_receiver(&mut self, cx: &FnCx, base: &ast::Expr) -> bool {
        let ExprKind::Name(name) = &base.kind else {
            return false;
        };
        if let Some(local) = cx.lookup(name) {
            // A failed local: its error is reported.
            return cx.failed.contains(&local);
        }
        if self.pkgs[cx.pkg].items.contains_key(name) || self.imported(cx, name).is_some() {
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
                ConstVal::Table(ty, id) => Some(Checked::new(TExprKind::Table(id), ty, None)),
                ConstVal::Expr(k) => {
                    let e = self.const_exprs[k].clone();
                    let ty = e.ty;
                    Some(Checked::new(e.kind, ty, None))
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
            Item::Trait(_) => {
                self.error(
                    span,
                    format!(
                        "`{name}` is a trait; call one of its methods, like `{name}.method(x)`"
                    ),
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
        expected: Option<Ty>,
    ) -> Option<Checked> {
        if let Some(ty) = self.type_path(cx, base) {
            let ty = ty?;
            // `E.MAX_LEN`: an associated constant.
            let variant = ty
                .as_enum()
                .is_some_and(|d| d.variant(&member.name).is_some());
            if !variant && let Some((p, it)) = self.assoc_const(ty, &member.name) {
                return self.assoc_const_expr(cx, p, it, span);
            }
            if ty.as_param().is_some() {
                let found = self.assoc_trait(ty, &member.name).err().unwrap_or_default();
                self.assoc_error(ty, member, &found);
                return None;
            }
            if self.methods.contains_key(&(ty.decl(), member.name.clone()))
                || self
                    .impl_methods
                    .contains_key(&(ty.decl(), member.name.clone()))
            {
                self.error(
                    span,
                    format!(
                        "`{ty}.{}` is a function; call it with `{ty}.{}(...)`",
                        member.name, member.name
                    ),
                );
                return None;
            }
            return self.enum_variant(cx, ty, member, None, span, expected);
        }
        if let ExprKind::Name(pkg_name) = &base.kind
            && let Some(pkg) = self.imported(cx, pkg_name)
        {
            let item = self.package_item(cx, pkg, &member.name, member.span)?;
            return self.item_value(item, &format!("{pkg_name}.{}", member.name), span);
        }
        // `target.os` and the like: known when compiling.
        if let ExprKind::Name(n) = &base.kind
            && n == super::TARGET
            && cx.lookup(n).is_none()
            && !self.pkgs[cx.pkg].items.contains_key(n)
        {
            let (ty, v) = self.target_field(member)?;
            let range = matches!(ty, Ty::Int(_)).then(|| Range::exact(v));
            return Some(Checked::new(super::scalar_expr(ty, v).kind, ty, range));
        }
        if self.unknown_receiver(cx, base) {
            return None;
        }
        let b = self.expr(cx, base, None)?;
        match (b.ty(), member.name.as_str()) {
            (Ty::Str | Ty::Slice(_), "len") => Some(self.view_len_of(cx, &b)),
            (Ty::Array(_), "len") => Some(self.array_len(cx, b.expr)),
            (ty, name)
                if self.methods.contains_key(&(ty.decl(), name.to_owned()))
                    || (self
                        .impl_methods
                        .contains_key(&(ty.decl(), name.to_owned()))
                        && ty.as_struct().is_none_or(|d| d.field(name).is_none())) =>
            {
                self.error(
                    span,
                    format!("`{name}` is a method of `{ty}`; call it with `.{name}(...)`"),
                );
                None
            }
            (Ty::Struct(_), name) => {
                let def = b.ty().as_struct().expect("a struct");
                let Some((i, fty)) = def.field(name) else {
                    self.error(member.span, format!("`{}` has no field `{name}`", b.ty()));
                    return None;
                };
                if def.pkg != cx.pkg && !def.fields[i].is_pub {
                    self.diags.push(
                        Diagnostic::error(
                            member.span,
                            format!("`{name}` is a private field of `{}`", def.name),
                        )
                        .with_help(format!(
                            "only code in package `{}` can use it",
                            self.pkgs[def.pkg].path
                        )),
                    );
                    return None;
                }
                // An integer field of a local, through fields only, is a term.
                let term = match type_range(fty) {
                    Some(_) => field_term(&b.expr, i),
                    None => None,
                };
                // A field of a literal (a struct constant's value) is known.
                let literal = match &b.expr.kind {
                    TExprKind::StructLit(fields) => fields.iter().find_map(|(k, v)| match v.kind {
                        TExprKind::Int(v) if *k as usize == i => Some(Range::exact(v)),
                        _ => None,
                    }),
                    _ => None,
                };
                let mut c = Checked::new(
                    TExprKind::Field(Box::new(b.expr), i as u32),
                    fty,
                    literal.or_else(|| term.and_then(|t| super::read_range(cx, t))),
                );
                c.term = term.map(Linear::of);
                Some(c)
            }
            (Ty::Str, "bytes") => {
                self.error(
                    span,
                    "`bytes` is a method of `str`; call it with `.bytes()`",
                );
                None
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

    /// The longest a view can be: the largest `isize` of the target, since
    /// no object is bigger.
    pub(super) fn len_max(&self) -> i128 {
        (1i128 << (self.ptr_bits - 1)) - 1
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
            Some(ty @ Ty::Param(_)) => {
                let Some(n) = num(ty) else {
                    self.diags.push(
                        Diagnostic::error(span, format!("expected `{ty}`, found an integer"))
                            .with_help(format!(
                                "only a type parameter with a numeric bound takes integer literals: `[{ty}: Integer]`"
                            )),
                    );
                    return None;
                };
                if !n.fits.contains(v) {
                    let mut d = Diagnostic::error(
                        span,
                        format!("`{v}` does not fit in every type `{ty}` can be"),
                    );
                    if let Some(h) = param_help(ty) {
                        d = d.with_help(h);
                    }
                    self.diags.push(d);
                    return None;
                }
                Some(Checked::new(TExprKind::Int(v), ty, Some(Range::exact(v))))
            }
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
                let c = self.coerce(cx, c, Ty::Bool, operand.span)?;
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
                if num(c.ty()).is_none() {
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
                let t = c.ty();
                let Some(n) = num(t) else {
                    self.error(span, format!("`-` needs an integer, found `{t}`"));
                    return None;
                };
                match n.signed {
                    Some(true) => {}
                    Some(false) => {
                        self.error(
                            span,
                            format!("cannot negate a value of the unsigned type `{t}`"),
                        );
                        return None;
                    }
                    None => {
                        self.diags.push(
                            Diagnostic::error(
                                span,
                                format!("cannot negate a value of `{t}`, which may be unsigned"),
                            )
                            .with_help(format!(
                                "add the bound `[{t}: Signed]`, or subtract from 0: `0 -| x`"
                            )),
                        );
                        return None;
                    }
                }
                let r = c.int_range();
                let min = n.min.expect("a signed type");
                // For a type parameter, above every signed type's smallest
                // value.
                let overflows = (n.param && r.lo <= min) || r.lo == min;
                if overflows && cx.comptime {
                    let neg = TExprKind::Unary(TUnOp::Neg, Box::new(c.expr));
                    return Some(Checked::new(neg, t, None).unproven(span));
                }
                if overflows {
                    let mut d = Diagnostic::error(
                        span,
                        format!("cannot prove that this negation does not overflow `{t}`"),
                    )
                    .with_help(format!(
                        "the operand can be {}, and `-({min})` doesn't fit",
                        show_range(r, t)
                    ));
                    if n.param {
                        d = d.with_help(format!(
                            "`{t}` can be `i8`: the operand must be above {min}"
                        ));
                    }
                    self.diags.push(d);
                    return None;
                }
                let range = Range {
                    lo: -r.hi,
                    hi: -r.lo,
                };
                Some(Checked::new(
                    TExprKind::Unary(TUnOp::Neg, Box::new(c.expr)),
                    t,
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
            _ if (needs_context(rhs) || self.generic_literal(cx, rhs))
                && !needs_context(lhs)
                && !self.generic_literal(cx, lhs) =>
            {
                let l = self.expr(cx, lhs, expected)?;
                let r = self.expr(cx, rhs, Some(l.ty()))?;
                (l, r)
            }
            _ if (needs_context(lhs) || self.generic_literal(cx, lhs))
                && !needs_context(rhs)
                && !self.generic_literal(cx, rhs) =>
            {
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
            (a, b) if coercible(a, b) && !b.is_view() => {
                Some((self.coerce(cx, l, b, lhs.span)?, r))
            }
            (a, b) if coercible(b, a) && !a.is_view() => {
                Some((l, self.coerce(cx, r, a, rhs.span)?))
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
                    .and_then(|l| self.coerce(cx, l, Ty::Bool, lhs.span));
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
                    .and_then(|r| self.coerce(cx, r, Ty::Bool, rhs.span));
                let after = std::mem::replace(&mut cx.env, saved);
                // A value the right side may have moved out of a variable
                // is gone whether it ran or not.
                for l in after.uninit_locals() {
                    if cx.moved.contains(&l) && !cx.env.is_uninit(l) {
                        cx.env.declare_uninit(l);
                    }
                }
                // What the right side changes, it may have changed.
                if let Some(r) = &r {
                    forget_changed(cx, &r.expr);
                }
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
                let ty = l.ty();
                // Integers are ordered; arrays and structs compare element
                // by element, field by field.
                let ok = if ordered {
                    num(ty).is_some()
                } else {
                    ty.satisfies(Trait::Eq)
                };
                if !ok {
                    let mut d = Diagnostic::error(
                        span,
                        format!("`{}` can't compare values of type `{ty}`", op.as_str()),
                    );
                    if let Some(field) = ty.uninit_field().filter(|_| !ordered) {
                        d = d.with_help(format!(
                            "its field `{field}` is `@uninit`, so `==` could read bytes never written: compare with a method of `{ty}`"
                        ));
                    } else if ty.as_param().is_some() {
                        d = if !ordered {
                            d.with_help(format!("add the bound `[{ty}: Eq]`"))
                        } else if ty.satisfies(Trait::Ordered) {
                            d.with_help(format!(
                                "`{ty}: Ordered` gives methods, not operators: `a.lt(b)`, `a.le(b)`, `a.gt(b)`, `a.ge(b)`, `a.cmp(b)`"
                            ))
                        } else {
                            d.with_help(format!(
                                "add the bound `[{ty}: Ordered]` and compare with `a.lt(b)`, or a numeric bound (`Integer`) for `<`"
                            ))
                        };
                    }
                    self.diags.push(d);
                    return None;
                }
                let cmp = match op {
                    BinOp::Eq => CmpOp::Eq,
                    BinOp::Ne => CmpOp::Ne,
                    BinOp::Lt => CmpOp::Lt,
                    BinOp::Le => CmpOp::Le,
                    BinOp::Gt => CmpOp::Gt,
                    _ => CmpOp::Ge,
                };
                Some(self.comparison(cx, cmp, l, r))
            }
            BinOp::Shl | BinOp::ShlWrap | BinOp::Shr => self.shift(cx, op, lhs, rhs, expected),
            BinOp::Coalesce => self.coalesce(cx, lhs, rhs, expected),
            _ => self.arith(cx, op, lhs, rhs, span, expected),
        }
    }

    /// The comparison `l op r` of two values of the same type, with the
    /// facts it gives if they're integers.
    pub(super) fn comparison(
        &mut self,
        cx: &mut FnCx,
        cmp: CmpOp,
        l: Checked,
        r: Checked,
    ) -> Checked {
        let numeric = type_range(l.ty()).is_some();
        if numeric {
            super::note_thresholds(cx, l.side(), r.side());
        }
        let facts = numeric.then(|| Box::new(facts::comparison(cmp, l.side(), r.side())));
        let kind = TExprKind::Binary(TBinOp::Cmp(cmp), Box::new(l.expr), Box::new(r.expr));
        let mut out = Checked::new(kind, Ty::Bool, None);
        out.facts = facts;
        out
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
        // The value is taken out of the optional.
        self.consume(cx, &l.expr, lhs.span)?;
        // `opt ?? throw value` leaves the function when `opt` is `none`.
        // The right side runs only then: after it, what's known is what
        // holds whether it ran or not.
        let before = cx.env.clone();
        let r = match &rhs.kind {
            ExprKind::Throw(value) => TExpr {
                kind: TExprKind::Throw(Box::new(self.throw(cx, value, rhs.span)?)),
                ty: inner,
            },
            _ => {
                let r = self.expr(cx, rhs, Some(inner))?;
                let r = self.coerce(cx, r, inner, rhs.span)?;
                self.consume(cx, &r.expr, rhs.span)?;
                r.expr
            }
        };
        cx.env = Env::join(before, std::mem::take(&mut cx.env));
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
        let n = self.coerce(cx, n, usize_ty, rhs.span)?;
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
        let t = l.ty();
        let Some(n) = num(t) else {
            let mut d = Diagnostic::error(
                span,
                format!("`{}` needs integers, found `{t}`", op.as_str()),
            );
            if t.as_param().is_some() {
                d = d.with_help(format!(
                    "only a numeric bound gives `{t}` operators: `[{t}: Integer]` (or `Unsigned`, `Signed`)"
                ));
            }
            self.diags.push(d);
            return None;
        };
        let (a, b) = (l.int_range(), r.int_range());
        // The values a result can have, whatever the type is.
        let full = n.values;
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
        // The result as a form of at most two terms (`a + b`, `10 * v + d`,
        // `9 - d`), for `+`, `-` and `*` by a constant that are proven.
        let form = match (op, l.form(), r.form()) {
            (BinOp::Add, Some(x), Some(y)) => x.plus(y),
            (BinOp::Sub, Some(x), Some(y)) => x.minus(y),
            (BinOp::Mul, Some(x), _) if exact(b).is_some() => exact(b).and_then(|k| x.scale(k)),
            (BinOp::Mul, _, Some(y)) if exact(a).is_some() => exact(a).and_then(|k| y.scale(k)),
            _ => None,
        };

        let (top, range) = match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                let mut result = match op {
                    BinOp::Add => a.checked_add(b),
                    BinOp::Sub => a.checked_sub(b),
                    _ => a.checked_mul(b),
                };
                // A form of two terms: a relation or a sum between them
                // bounds it (`y <= x` gives `x - y >= 0`, `a + b <= c`
                // gives `a + b <= c`).
                if let (Some(f), Some(res)) = (form, result) {
                    let (lo, hi) = cx.env.form_bounds(f);
                    let lo = lo.map_or(res.lo, |lo| res.lo.max(lo));
                    let hi = hi.map_or(res.hi, |hi| res.hi.min(hi));
                    if lo <= hi {
                        result = Some(Range { lo, hi });
                    }
                }
                // For a type parameter, each end of the result also fits
                // when it's past an operand, which is a value of the type:
                // `x + y` is at least `x` when `y >= 0`, at most `x` when
                // `y <= 0`; `x - y` is at most `x` when `y >= 0`.
                let side = match op {
                    BinOp::Add => (a.lo >= 0 || b.lo >= 0, a.hi <= 0 || b.hi <= 0),
                    BinOp::Sub => (b.hi <= 0, b.lo >= 0),
                    _ => (false, false),
                };
                let fits = |res: Range| {
                    res.within(n.fits) || (n.param && Self::fits_param(cx, t, n, res, linear, side))
                };
                match result {
                    Some(res) if fits(res) => {
                        let top = match op {
                            BinOp::Add => TBinOp::Add(Mode::Proven),
                            BinOp::Sub => TBinOp::Sub(Mode::Proven),
                            _ => TBinOp::Mul(Mode::Proven),
                        };
                        // A value of the type: within the values it can have.
                        (top, res.intersect(full).unwrap_or(res))
                    }
                    _ if cx.comptime => {
                        let top = match op {
                            BinOp::Add => TBinOp::Add(Mode::Proven),
                            BinOp::Sub => TBinOp::Sub(Mode::Proven),
                            _ => TBinOp::Mul(Mode::Proven),
                        };
                        let kind = TExprKind::Binary(top, Box::new(l.expr), Box::new(r.expr));
                        return Some(Checked::new(kind, t, None).unproven(span));
                    }
                    _ => {
                        let (wrap, sat) = match op {
                            BinOp::Add => ("+%", "+|"),
                            BinOp::Sub => ("-%", "-|"),
                            _ => ("*%", "*|"),
                        };
                        let mut d = Diagnostic::error(
                            span,
                            format!(
                                "cannot prove that this {} does not overflow `{t}`",
                                op_name(op)
                            ),
                        )
                        .with_help(format!(
                            "the operands can be {} and {}",
                            show_range(a, t),
                            show_range(b, t)
                        ));
                        if let Some(h) = param_help(t) {
                            d = d.with_help(h);
                        }
                        self.diags.push(d.with_help(format!(
                            "use `{wrap}` to wrap around, `{sat}` to saturate, or check the values first"
                        )));
                        return None;
                    }
                }
            }
            BinOp::AddWrap => (TBinOp::Add(Mode::Wrap), full),
            BinOp::SubWrap => (TBinOp::Sub(Mode::Wrap), full),
            BinOp::MulWrap => (TBinOp::Mul(Mode::Wrap), full),
            BinOp::AddSat => (TBinOp::Add(Mode::Saturate), full),
            BinOp::SubSat => (TBinOp::Sub(Mode::Saturate), full),
            BinOp::MulSat => (TBinOp::Mul(Mode::Saturate), full),
            BinOp::Div | BinOp::Rem if cx.comptime => {
                let top = if op == BinOp::Div {
                    TBinOp::Div
                } else {
                    TBinOp::Rem
                };
                let kind = TExprKind::Binary(top, Box::new(l.expr), Box::new(r.expr));
                return Some(Checked::new(kind, t, None).unproven(span));
            }
            BinOp::Div | BinOp::Rem => {
                // Ruled out by the ranges, or by a hole (`b != 0`).
                let (a_term, b_term) = (l.term, r.term);
                if !cx.env.excludes_value(b_term, b, 0) {
                    self.diags.push(
                        Diagnostic::error(rhs.span, "cannot prove that this divisor is not zero")
                            .with_help(format!("the divisor can be {b}")),
                    );
                    return None;
                }
                // For a type parameter, `a` must be above the smallest
                // value of every signed type it can be.
                let min_ruled_out = |min: i128| {
                    if n.param {
                        a.lo > min
                    } else {
                        cx.env.excludes_value(a_term, a, min)
                    }
                };
                if let Some(min) = n.min
                    && !min_ruled_out(min)
                    && !cx.env.excludes_value(b_term, b, -1)
                {
                    let what = if n.param {
                        format!("the smallest `{t}`")
                    } else {
                        format!("`{min}`")
                    };
                    self.diags.push(
                        Diagnostic::error(
                            span,
                            format!("cannot prove that this is not {what} divided by -1"),
                        )
                        .with_help(format!(
                            "the operands can be {} and {}; that one result doesn't fit in `{t}`",
                            show_range(a, t),
                            show_range(b, t)
                        ))
                        .with_help(
                            "handle a divisor of -1 first: in `if b == -1 { ... } else { a / b }`, \
                             the division is proven",
                        ),
                    );
                    return None;
                }
                let range = if op == BinOp::Div {
                    quotient_range(a, b)
                } else {
                    remainder_range(a, b)
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
            // With a non-negative operand, `a & b` lies between 0 and it.
            BinOp::BitAnd => {
                let range = match (a.lo >= 0, b.lo >= 0) {
                    (true, true) => Range {
                        lo: 0,
                        hi: a.hi.min(b.hi),
                    },
                    (true, false) => Range { lo: 0, hi: a.hi },
                    (false, true) => Range { lo: 0, hi: b.hi },
                    (false, false) => full,
                };
                (TBinOp::BitAnd, range)
            }
            // Of non-negative operands, `a | b` is at least the larger one,
            // and neither `|` nor `^` sets a bit above their highest.
            BinOp::BitOr if a.lo >= 0 && b.lo >= 0 => (
                TBinOp::BitOr,
                Range {
                    lo: a.lo.max(b.lo),
                    hi: all_ones(a.hi.max(b.hi)),
                },
            ),
            BinOp::BitXor if a.lo >= 0 && b.lo >= 0 => (
                TBinOp::BitXor,
                Range {
                    lo: 0,
                    hi: all_ones(a.hi.max(b.hi)),
                },
            ),
            BinOp::BitOr => (TBinOp::BitOr, full),
            BinOp::BitXor => (TBinOp::BitXor, full),
            _ => unreachable!("not an arithmetic operator"),
        };
        let upper = if op == BinOp::Div {
            shrunk(l.term, a, b.lo >= 1, b.lo >= 2)
        } else {
            None
        };
        // `F / m` of a form that can't be negative, by a constant `m >= 1`:
        // rounded down, which comparisons can use.
        let quot = match (op, l.form(), exact(b)) {
            (BinOp::Div, Some(f), Some(m)) if m >= 1 && a.lo >= 0 && f.term_count() > 0 => {
                Some((f, m))
            }
            _ => None,
        };
        let kind = TExprKind::Binary(top, Box::new(l.expr), Box::new(r.expr));
        let mut out = Checked::new(kind, t, Some(range));
        out.term = linear;
        out.upper = upper;
        if matches!(
            top,
            TBinOp::Add(Mode::Proven) | TBinOp::Sub(Mode::Proven) | TBinOp::Mul(Mode::Proven)
        ) {
            out.form = form;
        }
        out.quot = quot;
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
        let t = l.ty();
        let Some(n) = num(t) else {
            self.error(
                lhs.span,
                format!("`{}` needs an integer, found `{t}`", op.as_str()),
            );
            return None;
        };
        let r = self.expr(cx, rhs, Some(l.ty()))?;
        if num(r.ty()).is_none() {
            self.error(
                rhs.span,
                format!("the shift amount must be an integer, found `{}`", r.ty()),
            );
            return None;
        }
        let amount = r.int_range();
        let unproven = op != BinOp::ShlWrap
            && !amount.within(Range {
                lo: 0,
                hi: i128::from(n.bits) - 1,
            });
        if unproven && cx.comptime {
            let top = if op == BinOp::Shl {
                TBinOp::Shl
            } else {
                TBinOp::Shr
            };
            let kind = TExprKind::Binary(top, Box::new(l.expr), Box::new(r.expr));
            return Some(Checked::new(kind, t, None).unproven(rhs.span));
        }
        if unproven {
            let mut d = Diagnostic::error(
                rhs.span,
                format!(
                    "cannot prove that this shift amount is less than {}",
                    n.bits
                ),
            )
            .with_help(format!("the amount can be {}", show_range(amount, r.ty())));
            if n.param {
                d = d.with_help(format!("`{t}` can be 8 bits wide"));
            }
            self.diags
                .push(d.with_help("use `<<%` to take the amount modulo the width"));
            return None;
        }
        let a = l.int_range();
        let (top, range) = match op {
            BinOp::Shl => (TBinOp::Shl, n.values),
            BinOp::ShlWrap => (TBinOp::ShlWrap, n.values),
            // `a >> n` is `a` divided by `2^n`, rounded down (an arithmetic
            // shift for signed types): its extremes are at the corners.
            _ => {
                let vals = [
                    a.lo >> amount.lo,
                    a.lo >> amount.hi,
                    a.hi >> amount.lo,
                    a.hi >> amount.hi,
                ];
                let range = Range {
                    lo: *vals.iter().min().expect("four values"),
                    hi: *vals.iter().max().expect("four values"),
                };
                (TBinOp::Shr, range)
            }
        };
        let upper = if top == TBinOp::Shr {
            shrunk(l.term, a, amount.lo >= 0, amount.lo >= 1)
        } else {
            None
        };
        let kind = TExprKind::Binary(top, Box::new(l.expr), Box::new(r.expr));
        let mut out = Checked::new(kind, t, Some(range));
        out.upper = upper;
        Some(out)
    }

    /// A call: of a function, a method (`p.scale(2)`), or an associated
    /// function (`Point.origin()`), or else a variant with a payload, a
    /// conversion or `syscall`. The result of a call to a function that
    /// throws must be `handled` (by `try`, `catch` or `match`, which then
    /// get a value of its result type); otherwise it's an error.
    pub(super) fn call(
        &mut self,
        cx: &mut FnCx,
        callee: &ast::Expr,
        args: &[ast::Expr],
        span: Span,
        handled: bool,
        expected: Option<Ty>,
    ) -> Option<Checked> {
        // `f[u32](...)`: type arguments, when the brackets follow the name
        // of a function (docs/generics.md, `[T]` and indexing), or of a
        // method (`p.conv[u16]()`, its own parameters).
        let names_fn = |ck: &Self, cx: &FnCx, base: &ast::Expr| {
            ck.names_function(cx, base) || matches!(base.kind, ExprKind::Field(..))
        };
        let (callee, explicit) = match &callee.kind {
            ExprKind::Index(base, item) if names_fn(self, cx, base) => (
                &**base,
                Some((vec![ast::TypeArg::Expr((**item).clone())], callee.span)),
            ),
            ExprKind::TypeArgs(base, items) if names_fn(self, cx, base) => {
                (&**base, Some((items.clone(), callee.span)))
            }
            _ => (callee, None),
        };
        // The type arguments of a generic type the callee is an associated
        // function of, when written: `Pair[u8, bool].new(...)`.
        let mut owner_args: Vec<Ty> = Vec::new();
        // The receiver of a method call, with its span.
        let mut receiver: Option<(Checked, Span)> = None;
        // `Trait.method(x, ...)`: a trait's method, called through the
        // trait, with `self` as the first argument.
        let mut via_trait = None;
        if let ExprKind::Field(base, member) = &callee.kind
            && let Some(t) = self.names_trait(cx, base)
        {
            if t == Trait::Ordered && ORDERED_METHODS.contains(&member.name.as_str()) {
                let [first, rest @ ..] = args else {
                    self.error(span, format!("`Ordered.{}` takes 2 arguments", member.name));
                    return None;
                };
                let recv = self.expr(cx, first, None)?;
                return self.ordered_method(cx, recv, member, rest, span);
            }
            let Some(id) = self.trait_fn(t, &member.name) else {
                self.error(
                    member.span,
                    format!("`{t}` has no method `{}`", member.name),
                );
                return None;
            };
            via_trait = Some((id, format!("{t}.{}", member.name)));
        }
        let type_of = match &callee.kind {
            _ if via_trait.is_some() => None,
            ExprKind::Field(base, _) => self.type_path(cx, base),
            _ => None,
        };
        if type_of.is_none()
            && via_trait.is_none()
            && let ExprKind::Field(base, _) = &callee.kind
            && self.unknown_receiver(cx, base)
        {
            return None;
        }
        let (id, name) = match &callee.kind {
            _ if via_trait.is_some() => via_trait.take().expect("checked"),
            ExprKind::Field(_, member) if type_of.is_some() => {
                // `T.name(...)`: a variant, or an associated function.
                let ty = type_of.expect("checked")?;
                if ty
                    .as_enum()
                    .is_some_and(|def| def.variant(&member.name).is_some())
                {
                    return self.enum_variant(cx, ty, member, Some(args), span, expected);
                }
                if !ty.is_decl_form() {
                    owner_args = ty.type_args().to_vec();
                }
                let is_enum = ty.as_enum().is_some();
                let decl = ty.decl();
                let self_ty = ty;
                let ty = if ty.is_decl_form() {
                    nominal_name(ty)
                } else {
                    ty.to_string()
                };
                let name = format!("{ty}.{}", member.name);
                // An associated function of a trait: of a type parameter's
                // bounds, or of a type's impls when it has no function of
                // its own of that name.
                let own = self.methods.contains_key(&(decl, member.name.clone()));
                let from_trait = if own {
                    None
                } else {
                    self.trait_method(cx.pkg, self_ty, &member.name, member.span)?
                };
                let found = match from_trait {
                    Some(id) => {
                        // A trait's own function takes `Self` first.
                        if self.is_trait_fn(id) {
                            owner_args = if self_ty.is_decl_form() {
                                Vec::new()
                            } else {
                                vec![self_ty]
                            };
                        }
                        Some(id)
                    }
                    None if self_ty.as_param().is_some() => None,
                    None => self.find_method(cx, decl, member)?,
                };
                match found {
                    Some(id) if self.sigs[id].has_self => {
                        self.diags.push(
                            Diagnostic::error(
                                callee.span,
                                format!("`{name}` is a method: call it on a value"),
                            )
                            .with_help(format!(
                                "as in `x.{}(...)`, with `x` a `{ty}`",
                                member.name
                            )),
                        );
                        return None;
                    }
                    Some(id) => (id, name),
                    None => {
                        let what = if is_enum {
                            "variant or function"
                        } else {
                            "function"
                        };
                        self.error(
                            member.span,
                            format!("`{ty}` has no {what} `{}`", member.name),
                        );
                        return None;
                    }
                }
            }
            ExprKind::Name(name) if cx.lookup(name).is_none() => {
                if let Some(ty) = Self::type_param(cx, name) {
                    return self.param_conversion(cx, ty, args, span);
                }
                if let Some(&Item::Func(id)) = self.pkgs[cx.pkg].items.get(name) {
                    self.callable(id, callee.span)?;
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
                } else if self.names_compile_error(cx, name) {
                    return self.compile_error_expr(cx, name, args, span);
                } else if name == "Ordering" {
                    return self.enum_from(cx, Ty::ordering(), args, span);
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
                    Item::Func(id) => {
                        self.callable(id, callee.span)?;
                        (id, format!("{pkg_name}.{}", member.name))
                    }
                    Item::Type(ty) if ty.as_enum().is_some() => {
                        return self.enum_from(cx, ty, args, span);
                    }
                    Item::Const(_) | Item::Type(_) | Item::Trait(_) => {
                        self.error(
                            callee.span,
                            format!("`{pkg_name}.{}` is not a function", member.name),
                        );
                        return None;
                    }
                }
            }
            // `value.name(...)`: a method of the value's type.
            ExprKind::Field(base, member) => {
                let recv = self.expr(cx, base, None)?;
                let ty = recv.ty();
                if ty == Ty::Str && member.name == "bytes" {
                    return self.str_bytes(recv, args, span);
                }
                let ordered = ORDERED_METHODS.contains(&member.name.as_str());
                // On a type parameter, the methods of the built-in trait
                // `Ordered` come first, then those of its other bounds; on
                // a type, its own methods, then its traits'.
                if ordered && ty.as_param().is_some() && ty.satisfies(Trait::Ordered) {
                    return self.ordered_method(cx, recv, member, args, span);
                }
                let found = match ty.as_param() {
                    Some(_) => None,
                    None => self.find_method(cx, ty.decl(), member)?,
                };
                let found = match found {
                    Some(id) => Some(id),
                    None => self.trait_method(cx.pkg, ty, &member.name, member.span)?,
                };
                if found.is_none()
                    && ordered
                    && (ty.as_param().is_some() || ty.satisfies(Trait::Ordered))
                {
                    return self.ordered_method(cx, recv, member, args, span);
                }
                if found.is_none() && ty.as_param().is_some() {
                    self.diags.push(
                        Diagnostic::error(
                            member.span,
                            format!("`{ty}` has no method `{}`", member.name),
                        )
                        .with_help(format!(
                            "a type parameter has the methods of its bounds: add a trait that has `{}`, as in `[{ty}: Trait]`",
                            member.name
                        )),
                    );
                    return None;
                }
                let id = match found {
                    Some(id) => id,
                    None => {
                        let msg = match ty.as_struct() {
                            Some(def) if def.field(&member.name).is_some() => {
                                format!("`{}` is a field of `{ty}`, not a method", member.name)
                            }
                            _ => format!("`{ty}` has no method `{}`", member.name),
                        };
                        self.error(member.span, msg);
                        return None;
                    }
                };
                if !self.sigs[id].has_self {
                    self.diags.push(
                        Diagnostic::error(
                            member.span,
                            format!(
                                "`{ty}.{}` has no `self`, so it's called on the type",
                                member.name
                            ),
                        )
                        .with_help(format!("call it as `{ty}.{}(...)`", member.name)),
                    );
                    return None;
                }
                receiver = Some((recv, base.span));
                (id, callee_name(callee))
            }
            _ => {
                self.error(callee.span, "only named functions can be called");
                return None;
            }
        };
        // A call of a function with `comptime` parameters or a pack is a
        // call of its expansion for these arguments.
        let expanded;
        let (id, args) = if self.sigs[id].template.is_some() {
            if let Some((_, bspan)) = &explicit {
                self.error(
                    *bspan,
                    format!("the type arguments of `{name}`, which has `comptime` parameters or a pack, are inferred"),
                );
                return None;
            }
            let (exp, rest) = self.expand_call(cx, id, &name, args, span)?;
            expanded = rest;
            (exp, expanded.as_slice())
        } else {
            (id, args)
        };
        let type_params = self.sigs[id].type_params.clone();
        let owner_params = self.sigs[id].owner_params;
        let generic = !type_params.is_empty();
        if let Some((_, bspan)) = &explicit
            && type_params.len() == owner_params
        {
            self.error(
                *bspan,
                format!("`{name}` is not generic: it takes no type arguments"),
            );
            return None;
        }
        if self.sigs[id].is_unsafe {
            self.require_unsafe(
                cx,
                callee.span,
                &format!("calling the `unsafe fn` `{name}`"),
            );
        }
        let (params, sig_ret) = (self.sigs[id].params.clone(), self.sigs[id].ret);
        let throws = self.sigs[id].throws;
        if throws.is_some() && !handled {
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
        let skip = usize::from(receiver.is_some());
        if args.len() + skip != params.len() {
            self.error(
                span,
                format!(
                    "`{name}` takes {} argument(s), but {} were given",
                    params.len() - skip,
                    args.len()
                ),
            );
            return None;
        }
        let mut inf = Inference::new(type_params.clone());
        for (k, &a) in owner_args.iter().enumerate().take(owner_params) {
            inf.fix(k, a, callee.span);
        }
        if let Some((items, bspan)) = &explicit {
            let own = &type_params[owner_params..];
            if items.len() != own.len() {
                self.error(
                    *bspan,
                    format!(
                        "`{name}` takes {} type argument(s), but {} were given",
                        own.len(),
                        items.len()
                    ),
                );
                return None;
            }
            for (k, item) in items.iter().enumerate() {
                let ty = self.generic_arg(cx, item, own[k])?;
                inf.fix(owner_params + k, ty, item.span());
            }
        }
        let mut targs = Vec::new();
        // The places passed `inout` or `set`, which the call may change.
        let mut changed = Vec::new();
        let mut ok = true;
        if let Some((recv, rspan)) = receiver {
            // The receiver gives the type's arguments: `p.swap()` on a
            // `Pair[u8, bool]`.
            inf.unify(params[0].0, recv.ty(), rspan);
            let e = match params[0].1 {
                Convention::Inout => {
                    let place = self.mutable_place(cx, recv.expr, rspan, Changer::Receiver(&name));
                    match place {
                        Some(p) => {
                            changed.push((p.clone(), Convention::Inout));
                            Some(TExpr {
                                ty: p.ty,
                                kind: TExprKind::Ref(Box::new(p)),
                            })
                        }
                        None => None,
                    }
                }
                Convention::Sink => self.consume(cx, &recv.expr, rspan).map(|()| recv.expr),
                _ => Some(recv.expr),
            };
            ok &= e.is_some();
            targs.push(e);
        }
        // The arguments, in order. One whose parameter's type has a type
        // argument not known yet fixes it, unless it takes its type from
        // the context (a literal, `none`, `.name`, an array literal): that
        // one is checked once the others and the expected type are.
        let mut deferred = Vec::new();
        for (k, (arg, (pty, conv, pname))) in args.iter().zip(&params[skip..]).enumerate() {
            let (pty, conv) = (*pty, *conv);
            targs.push(None);
            let e = if inf.known(pty) {
                self.call_arg(cx, arg, inf.apply(pty), conv, pname, &name, &mut changed)
            } else if self.untyped_int(cx, arg).is_some()
                || needs_context(arg)
                || self.generic_literal(cx, arg)
            {
                deferred.push(k);
                continue;
            } else {
                self.infer_arg(cx, arg, pty, conv, pname, &name, &mut inf, &mut changed)
            };
            match e {
                Some(e) => targs[skip + k] = Some(e),
                None => ok = false,
            }
        }
        if !inf.all_known()
            && let Some(t) = expected
        {
            inf.unify(sig_ret, t, span);
        }
        for k in deferred {
            let (pty, conv, pname) = &params[skip + k];
            if !inf.known(*pty) {
                // A literal of a generic type may fix the arguments itself.
                if self.generic_literal(cx, &args[k]) {
                    let e = self.infer_arg(
                        cx,
                        &args[k],
                        *pty,
                        *conv,
                        pname,
                        &name,
                        &mut inf,
                        &mut changed,
                    );
                    match e {
                        Some(e) => targs[skip + k] = Some(e),
                        None => ok = false,
                    }
                }
                continue;
            }
            match self.call_arg(
                cx,
                &args[k],
                inf.apply(*pty),
                *conv,
                pname,
                &name,
                &mut changed,
            ) {
                Some(e) => targs[skip + k] = Some(e),
                None => ok = false,
            }
        }
        if let Some(p) = inf.unknown() {
            if ok && self.is_pack_param(id, p) {
                self.diags.push(
                    Diagnostic::error(span, format!("cannot tell the type of an argument of `{name}`"))
                        .with_help("give each argument a type, as in `u32(5)`: an integer literal doesn't have one"),
                );
            } else if ok {
                let write = match name.rsplit_once('.') {
                    Some((ty, method)) if type_params[..owner_params].contains(&p) => {
                        format!("write the type's arguments, as in `{ty}[...].{method}(...)`")
                    }
                    _ if p.value_param().is_some() => {
                        format!("write the arguments, as in `{name}[4](...)`")
                    }
                    _ => format!("write the type arguments, as in `{name}[u32](...)`"),
                };
                self.diags.push(
                    Diagnostic::error(
                        span,
                        format!("cannot tell what `{p}` is in this call of `{name}`"),
                    )
                    .with_help(format!(
                        "{write}, or give the result a type, as in `let x: u32 = {name}(...)`"
                    ))
                    .with_help("an integer literal doesn't fix a type argument"),
                );
            }
            return None;
        }
        // A method is named by its type: `Pair.smaller` requires ...
        let bound_name = if self.sigs[id].has_self {
            self.sigs[id].name.clone()
        } else {
            name.clone()
        };
        if generic && !self.check_bounds(id, &bound_name, &inf) {
            ok = false;
        }
        // What the call may have changed: facts about it are forgotten, and
        // a variable passed `set` is assigned (if the call succeeds).
        let mut sets = Vec::new();
        for (place, conv) in &changed {
            match place.kind {
                TExprKind::Local(l) if *conv == Convention::Set => {
                    if cx.env.is_uninit(l) {
                        sets.push(l);
                    }
                    cx.env.assign(l, None);
                }
                _ => forget_place(cx, place),
            }
        }
        cx.call_sets = sets;
        // Nothing after a call to a `never` function runs: what follows it
        // can't be reached, as after a `return`.
        if sig_ret == Ty::Never {
            cx.env.dead = true;
        }
        if !ok {
            return None;
        }
        let targs: Vec<TExpr> = targs.into_iter().map(|a| a.expect("checked")).collect();
        let mut ret = inf.apply(sig_ret);
        if let Some(err) = throws
            && handled
        {
            ret = Ty::result(ret, err);
        }
        if !generic {
            return Some(Checked::new(TExprKind::Call(id, targs), ret, None));
        }
        let types = inf.types();
        if let Some(caller) = cx.func
            && !cx.type_params.is_empty()
        {
            self.generic_calls.push(GenericEdge {
                caller,
                callee: id,
                args: types.clone(),
                span,
            });
        }
        Some(Checked::new(
            TExprKind::GenericCall(id, types, targs),
            ret,
            None,
        ))
    }

    /// The argument `arg` of a call of `name`, for its parameter `pname` of
    /// type `pty` passed `conv`. A place passed `inout` or `set` is added
    /// to `changed`; a value passed `sink` is kept (see
    /// [`Checker::consume`]).
    #[allow(clippy::too_many_arguments)]
    fn call_arg(
        &mut self,
        cx: &mut FnCx,
        arg: &ast::Expr,
        pty: Ty,
        conv: Convention,
        pname: &str,
        name: &str,
        changed: &mut Vec<(TExpr, Convention)>,
    ) -> Option<TExpr> {
        match (&arg.kind, conv) {
            (ExprKind::Ref(inner), Convention::Inout | Convention::Set) => {
                let place = self.ref_arg(cx, inner, pty, conv, arg.span)?;
                changed.push((place.clone(), conv));
                Some(TExpr {
                    kind: TExprKind::Ref(Box::new(place)),
                    ty: pty,
                })
            }
            (ExprKind::Ref(_), _) => {
                let how = match conv {
                    Convention::Sink => "passed `sink`, which moves a value in",
                    _ => "read-only",
                };
                self.diags.push(
                    Diagnostic::error(
                        arg.span,
                        format!(
                            "`&` marks an argument passed `inout` or `set`, but `{pname}` of `{name}` is {how}"
                        ),
                    )
                    .with_help("remove the `&`"),
                );
                None
            }
            (_, Convention::Inout | Convention::Set) => {
                let kw = if conv == Convention::Inout {
                    "inout"
                } else {
                    "set"
                };
                self.diags.push(
                    Diagnostic::error(
                        arg.span,
                        format!("`{name}` takes `{pname}` as `{kw}`, so the argument needs `&`"),
                    )
                    .with_help(
                        "pass a variable (or a field or an element of one) with `&`, as in `&x`: the call may change it",
                    ),
                );
                None
            }
            _ => {
                let c = self.expr(cx, arg, Some(pty))?;
                let c = self.coerce(cx, c, pty, arg.span)?;
                if conv == Convention::Sink {
                    self.consume(cx, &c.expr, arg.span)?;
                }
                Some(c.expr)
            }
        }
    }

    /// Like [`Checker::call_arg`], for a parameter whose type has type
    /// arguments not known yet: the argument is checked on its own first,
    /// and its type fixes them (see [`Inference::unify`]).
    #[allow(clippy::too_many_arguments)]
    fn infer_arg(
        &mut self,
        cx: &mut FnCx,
        arg: &ast::Expr,
        pty: Ty,
        conv: Convention,
        pname: &str,
        name: &str,
        inf: &mut Inference,
        changed: &mut Vec<(TExpr, Convention)>,
    ) -> Option<TExpr> {
        match (&arg.kind, conv) {
            (ExprKind::Ref(inner), Convention::Inout | Convention::Set) => {
                let place = self.ref_place(cx, inner, None, conv)?;
                inf.unify(pty, place.ty, arg.span);
                if !inf.known(pty) {
                    self.error(arg.span, format!("expected `{pty}`, found `{}`", place.ty));
                    return None;
                }
                let pty = inf.apply(pty);
                let place = self.ref_check(cx, place, pty, arg.span)?;
                changed.push((place.clone(), conv));
                Some(TExpr {
                    kind: TExprKind::Ref(Box::new(place)),
                    ty: pty,
                })
            }
            (ExprKind::Ref(_), _) | (_, Convention::Inout | Convention::Set) => {
                self.call_arg(cx, arg, pty, conv, pname, name, changed)
            }
            _ => {
                let c = self.expr(cx, arg, None)?;
                inf.unify(pty, c.ty(), arg.span);
                if !inf.known(pty) {
                    self.error(arg.span, format!("expected `{pty}`, found `{}`", c.ty()));
                    return None;
                }
                let pty = inf.apply(pty);
                let c = self.coerce(cx, c, pty, arg.span)?;
                if conv == Convention::Sink {
                    self.consume(cx, &c.expr, arg.span)?;
                }
                Some(c.expr)
            }
        }
    }

    /// `s.bytes()`: the bytes of the `str` `s`, a `[]u8` view of the same
    /// storage. It's a projection of `s`, not a new value: like any view,
    /// it can be kept in a local and passed on, but not stored or returned.
    fn str_bytes(&mut self, s: Checked, args: &[ast::Expr], span: Span) -> Option<Checked> {
        if !args.is_empty() {
            self.error(span, "`bytes()` takes no arguments");
            return None;
        }
        let u8_ty = Ty::slice(Ty::Int(IntTy::new(false, 8)));
        Some(Checked::new(
            TExprKind::Bytes(Box::new(s.expr)),
            u8_ty,
            None,
        ))
    }

    /// The method or associated function `member` of the type `ty`:
    /// `Some(None)` if there's none, `None` if it's private to another
    /// package (reported).
    /// Whether function `id` can be called here: not in a constant needed
    /// to declare a type or a signature (an array length), which is
    /// evaluated before every function's signature is known.
    fn callable(&mut self, id: FuncId, span: Span) -> Option<()> {
        if id < self.sigs.len() {
            return Some(());
        }
        self.diags.push(
            Diagnostic::error(
                span,
                "a constant needed to declare a type or a signature can't call a function",
            )
            .with_help("types and signatures are declared before functions are checked: compute it from literals and other constants"),
        );
        None
    }

    fn find_method(&mut self, cx: &FnCx, ty: Ty, member: &ast::Ident) -> Option<Option<FuncId>> {
        let Some(&id) = self.methods.get(&(ty, member.name.clone())) else {
            return Some(None);
        };
        self.callable(id, member.span)?;
        let sig = &self.sigs[id];
        if sig.pkg != cx.pkg && !sig.is_pub {
            let path = self.pkgs[sig.pkg].path.clone();
            self.error(
                member.span,
                format!("`{ty}.{}` is private to package `{path}`", member.name),
            );
            return None;
        }
        Some(Some(id))
    }

    /// The place `&inner` passes to a parameter of type `pty` passed `conv`
    /// (`inout` or `set`): a variable, or a field or an element of one,
    /// that can be changed, of exactly the parameter's type, or an array
    /// for an `inout` slice (a view of it whose elements can be changed).
    fn ref_arg(
        &mut self,
        cx: &mut FnCx,
        inner: &ast::Expr,
        pty: Ty,
        conv: Convention,
        span: Span,
    ) -> Option<TExpr> {
        let place = self.ref_place(cx, inner, Some(pty), conv)?;
        self.ref_check(cx, place, pty, span)
    }

    /// The place `&inner` names, for a parameter passed `conv`, checked
    /// with the parameter's type `pty` as the expected type if it's known.
    fn ref_place(
        &mut self,
        cx: &mut FnCx,
        inner: &ast::Expr,
        pty: Option<Ty>,
        conv: Convention,
    ) -> Option<TExpr> {
        // A variable passed `set` may be unassigned: it's written, not read.
        let bare = match &inner.kind {
            ExprKind::Name(n) if conv == Convention::Set => cx.lookup(n),
            _ => None,
        };
        Some(match bare {
            Some(l) => TExpr {
                kind: TExprKind::Local(l),
                ty: cx.locals[l].ty,
            },
            None => self.expr(cx, inner, pty)?.expr,
        })
    }

    /// Check that `place` can be passed `&` to a parameter of type `pty`.
    fn ref_check(&mut self, cx: &FnCx, place: TExpr, pty: Ty, span: Span) -> Option<TExpr> {
        let changer = Changer::Ref;
        if place.ty == pty {
            return self.mutable_place(cx, place, span, changer);
        }
        if let (Some((elem, _)), Some(want)) = (place.ty.as_array(), pty.as_slice())
            && elem == want
        {
            let array = self.mutable_place(cx, place, span, changer)?;
            return Some(TExpr {
                kind: TExprKind::ToSlice(Box::new(array)),
                ty: pty,
            });
        }
        self.diags.push(
            Diagnostic::error(span, format!("expected `{pty}`, found `{}`", place.ty))
                .with_help(
                    "a place passed `inout` or `set` must have exactly the parameter's type (or be an array, for a slice)",
                ),
        );
        None
    }

    /// Check that `place` can be changed by `changer`: a `var` (or a
    /// parameter the function may change), or a field or an element of one,
    /// or an element of an `inout` slice. Returns it.
    fn mutable_place(
        &mut self,
        cx: &FnCx,
        place: TExpr,
        span: Span,
        changer: Changer<'_>,
    ) -> Option<TExpr> {
        let mut root = &place;
        let local = loop {
            match &root.kind {
                TExprKind::Field(base, _)
                | TExprKind::Index(base, _)
                | TExprKind::Slice(base, ..)
                | TExprKind::ToSlice(base) => root = base,
                TExprKind::Local(l) => break *l,
                TExprKind::Table(id) => {
                    let name = &self.tables[*id].name;
                    let what = match changer {
                        Changer::Ref => format!("cannot pass `&{name}`"),
                        Changer::Receiver(method) => {
                            format!("cannot call `{method}`, which takes `inout self`,")
                        }
                    };
                    self.diags.push(
                        Diagnostic::error(span, format!("{what}: `{name}` is a constant"))
                            .with_help(format!("change a copy: `var v = {name}`")),
                    );
                    return None;
                }
                _ => {
                    let diag = match changer {
                        Changer::Ref => Diagnostic::error(
                            span,
                            "`&` needs a variable, or a field or an element of one",
                        )
                        .with_help("this is a temporary value: store it in a `var` first"),
                        Changer::Receiver(method) => Diagnostic::error(
                            span,
                            format!("cannot call `{method}` on a temporary: it takes `inout self`"),
                        )
                        .with_help("store the value in a `var` first"),
                    };
                    self.diags.push(diag);
                    return None;
                }
            }
        };
        let l = &cx.locals[local];
        let name = l.name.clone();
        let changes = match changer {
            Changer::Ref => format!(
                "cannot pass `&{}`",
                place_text(cx, &place).unwrap_or_else(|| name.clone())
            ),
            Changer::Receiver(method) => {
                format!("cannot call `{method}`, which takes `inout self`,")
            }
        };
        if l.ty.is_view() {
            if !l.mutable_view() {
                self.diags.push(
                    Diagnostic::error(
                        span,
                        match changer {
                            Changer::Ref => format!("{changes}: `{name}` is a read-only `{}`", l.ty),
                            Changer::Receiver(_) => format!(
                                "{changes} on an element of `{name}`, a read-only `{}`",
                                l.ty
                            ),
                        },
                    )
                    .with_help(
                        "only the elements of an `inout` slice parameter can be changed (`inout xs: []u8`)",
                    ),
                );
                return None;
            }
        } else if !l.mutable {
            let help = Self::immutable_help(cx, local, &name);
            let msg = match changer {
                Changer::Ref => format!("{changes}: `{name}` is immutable"),
                Changer::Receiver(_) => {
                    format!("{changes} on `{name}`, which is immutable")
                }
            };
            self.diags
                .push(Diagnostic::error(span, msg).with_help(help));
            return None;
        }
        self.check_defer_assign(cx, local, &name, span)?;
        Some(place)
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
        let from = c.ty();
        if num(from).is_none() {
            self.error(arg.span, format!("cannot convert `{from}` to `{to}`"));
            return None;
        }
        let r = c.int_range();
        if !r.within(to.range()) && cx.comptime {
            return Some(c.converted(Ty::Int(to), None).unproven(span));
        }
        if !r.within(to.range()) {
            self.diags.push(
                Diagnostic::error(span, format!("cannot prove that this `{from}` value fits in `{to}`"))
                    .with_help(format!("the value can be {}, and `{to}` holds {}", show_range(r, from), to.range()))
                    .with_help("check the value first; wrapping and saturating conversions are not supported by the compiler yet"),
            );
            return None;
        }
        if from == Ty::Int(to) {
            return Some(c);
        }
        let mut out = c.converted(Ty::Int(to), Some(r));
        out.upper = None;
        Some(out)
    }
}
