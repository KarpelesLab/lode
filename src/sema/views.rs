//! Views that are kept and returned: rule 2 of docs/memory.md, Views.
//!
//! A view (a slice or a `str`) may be kept in a local and returned from a
//! function. What it can see is recorded as the variables it **borrows
//! from**, its roots ([`Roots`]):
//!
//! - a view of (part of) a variable, an array or a value that owns memory,
//!   borrows from that variable; a view parameter borrows from itself (the
//!   caller made sure it stays valid for the call);
//! - a slice, `s.bytes()` and a list's elements borrow from what their base
//!   borrows from;
//! - a string literal, an array constant and a `static` borrow from nothing
//!   (static storage);
//! - a call that returns a view borrows from every argument that can lend
//!   storage ([`lends`]) and isn't passed `sink` or `set`: from what a view
//!   argument borrows from, and from the variable of any other one;
//! - in `unsafe` code, `mem.view` borrows from every parameter of the
//!   function (its author promises the memory is theirs);
//! - a value that isn't a variable (a temporary) ends with its statement:
//!   a view of one can't be kept or returned.
//!
//! A view local's roots are the union of the roots of every value it's
//! given in the function, as far as the checker has seen ([`FnCx::borrows`];
//! a loop whose body adds roots is checked again, see
//! `Checker::loop_body`). When a root changes (it's assigned, passed `&`,
//! moved, or the receiver of an `inout self` method), every view local
//! borrowing from it becomes unassigned, like a variable moved from: using
//! one after that, on some path, is an error at the use, which names the
//! change. So a view borrows from its roots exactly while it's live (used
//! later on some path), and not after its last use. A view local can't
//! borrow from a variable declared in a deeper block than its own, which
//! would end before it.
//!
//! A function returns only views whose roots are its read-only or `inout`
//! parameters (or nothing: static storage). The roots of a call's result,
//! in the caller, are then the variables the caller passed for them.

use std::collections::BTreeSet;

use crate::diag::Diagnostic;
use crate::source::Span;
use crate::types::Ty;

use super::expr::{Checked, SliceLen, place_term};
use super::facts::{Env, Linear};
use super::tree::*;
use super::{Checker, FnCx, read_range};
use crate::types::Range;

/// What a view borrows from (see the module docs).
#[derive(Debug, Default)]
pub(super) struct Roots {
    /// The variables (locals or parameters) whose storage it may view.
    pub(super) locals: BTreeSet<LocalId>,
    /// Whether it may view a temporary, which ends with its statement.
    pub(super) temp: bool,
}

/// Whether a value of type `ty` can hold storage that a view can see: a
/// view, an array, a type parameter, a value that owns memory (one that
/// isn't `Copy`, as a `List`), or a struct, an enum or an optional holding
/// one of those. An integer, a `bool` or a struct of them can't: a function
/// can't return a view of one, so a call's result doesn't borrow from it.
pub(super) fn lends(ty: Ty) -> bool {
    match ty {
        Ty::Str | Ty::Slice(_) | Ty::Array(_) | Ty::Param(_) => true,
        Ty::Optional(_) => ty.as_optional().is_some_and(lends),
        Ty::Struct(_) | Ty::Enum(_) => !ty.is_copy() || ty.members().into_iter().any(lends),
        _ => false,
    }
}

/// Whether `e` is a place: a variable, a `static` or a constant, or a
/// field, an element or a box's value of one.
fn is_place(e: &TExpr) -> bool {
    match &e.kind {
        TExprKind::Local(_) | TExprKind::Static(_) | TExprKind::Table(_) => true,
        TExprKind::Field(base, _)
        | TExprKind::Index(base, _)
        | TExprKind::Payload(base, ..)
        | TExprKind::Deref(base) => is_place(base),
        _ => false,
    }
}

/// The variable a place that changes is part of: a variable, or a field,
/// an element, a slice or a box's value of one (through the pattern
/// bindings that read a variable in place).
pub(super) fn changed_root(cx: &FnCx, e: &TExpr) -> Option<LocalId> {
    match &e.kind {
        TExprKind::Local(l) => match cx.projections.get(l) {
            Some(place) => changed_root(cx, place),
            None => Some(*l),
        },
        TExprKind::Field(base, _)
        | TExprKind::Payload(base, ..)
        | TExprKind::Index(base, _)
        | TExprKind::Deref(base)
        | TExprKind::Slice(base, ..)
        | TExprKind::ToSlice(base)
        | TExprKind::Elements(base)
        | TExprKind::Ref(base) => changed_root(cx, base),
        _ => None,
    }
}

/// The depth of the block that declares `local` (0 for the parameters).
fn scope_depth(cx: &FnCx, local: LocalId) -> usize {
    cx.scopes
        .iter()
        .position(|s| s.values().any(|&l| l == local))
        .unwrap_or(0)
}

/// How a variable a view borrows from stopped being what the view saw.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Change {
    /// Assigned, passed `&` or the receiver of an `inout self` method.
    Changed,
    /// Moved out of.
    Moved,
}

impl Change {
    fn verb(self) -> &'static str {
        match self {
            Change::Changed => "changed",
            Change::Moved => "was moved",
        }
    }
}

/// Where a view local stopped being usable: the variable it borrows from,
/// how it changed, and where.
pub(super) type Stale = (LocalId, Change, Span);

/// `local` changed (`how`): the view locals that borrow from it, if any,
/// can't be used any more (until they're assigned again), in `env`.
pub(super) fn source_changed_in(
    cx_borrows: &std::collections::HashMap<LocalId, BTreeSet<LocalId>>,
    stale: &mut std::collections::HashMap<LocalId, Stale>,
    env: &mut Env,
    local: LocalId,
    how: Change,
    span: Span,
) {
    if env.dead {
        return;
    }
    for (&v, roots) in cx_borrows {
        if v != local && roots.contains(&local) && !env.is_uninit(v) {
            env.declare_uninit(v);
            stale.insert(v, (local, how, span));
        }
    }
}

/// `local` changed (`how`) at `span` (see [`source_changed_in`]).
pub(super) fn source_changed(cx: &mut FnCx, local: LocalId, how: Change, span: Span) {
    source_changed_in(&cx.borrows, &mut cx.stale, &mut cx.env, local, how, span);
}

impl Checker<'_> {
    /// Whether `ty` is a `List` (`std/list`).
    pub(super) fn is_list(&self, ty: Ty) -> bool {
        self.list.is_some_and(|l| ty.same_decl(l))
    }

    /// The elements of the list `c`, as a slice ([`TExprKind::Elements`]),
    /// whose length is the list's `len`: a term when the list is a
    /// variable or a field of one. A list that isn't a place is a
    /// temporary.
    pub(super) fn elements(&mut self, cx: &mut FnCx, c: Checked) -> Checked {
        let c = self.temp(cx, c);
        let ty = c.ty();
        let def = ty.as_struct().expect("a list is a struct");
        let elem = ty.type_args()[0];
        let (k, len_ty) = def.field("len").expect("a list has `len`");
        let len = TExpr {
            kind: TExprKind::Field(Box::new(c.expr.clone()), k as u32),
            ty: len_ty,
        };
        let term = place_term(&len);
        let any = Range {
            lo: 0,
            hi: self.len_max(),
        };
        let range = term
            .and_then(|t| read_range(cx, t))
            .and_then(|r| r.intersect(any))
            .unwrap_or(any);
        let mut out = Checked::new(TExprKind::Elements(Box::new(c.expr)), Ty::slice(elem), None);
        out.len = Some(SliceLen {
            range,
            end: term.map(Linear::of),
            start: Range::exact(0),
        });
        out
    }

    /// What the view `e` borrows from.
    pub(super) fn view_roots(&self, cx: &FnCx, e: &TExpr) -> Roots {
        let mut out = Roots::default();
        self.roots_into(cx, e, &mut out);
        out
    }

    fn roots_into(&self, cx: &FnCx, e: &TExpr, out: &mut Roots) {
        match &e.kind {
            TExprKind::Str(_)
            | TExprKind::Table(_)
            | TExprKind::Static(_)
            | TExprKind::Never(_)
            | TExprKind::Unproven(..) => {}
            TExprKind::Local(l) if cx.temps.contains(l) => out.temp = true,
            // A pattern binding read in place views what it reads.
            TExprKind::Local(l) if cx.projections.contains_key(l) => {
                self.roots_into(cx, &cx.projections[l], out);
            }
            // A view local: what it was given borrows from (a `sink` view
            // parameter given another view too); a parameter, or any
            // other variable, itself.
            TExprKind::Local(l) => {
                let l = *l;
                let given = cx.borrows.get(&l).filter(|_| cx.locals[l].ty.is_view());
                if l < cx.params || given.is_none() {
                    out.locals.insert(l);
                }
                if let Some(roots) = given {
                    out.locals.extend(roots);
                }
            }
            // A call's result that isn't a view is a temporary.
            TExprKind::Call(..)
            | TExprKind::GenericCall(..)
            | TExprKind::Try(_)
            | TExprKind::Catch { .. }
                if !e.ty.is_view() =>
            {
                out.temp = true;
            }
            TExprKind::Field(base, _)
            | TExprKind::Index(base, _)
            | TExprKind::Payload(base, ..)
            | TExprKind::Deref(base)
            | TExprKind::Slice(base, ..)
            | TExprKind::ToSlice(base)
            | TExprKind::Bytes(base)
            | TExprKind::Elements(base)
            | TExprKind::Move(base, _)
            | TExprKind::Ref(base)
            | TExprKind::Try(base) => self.roots_into(cx, base, out),
            TExprKind::Catch { call, handler, .. } => {
                self.roots_into(cx, call, out);
                if let Handler::Value(v) = handler {
                    self.roots_into(cx, v, out);
                }
            }
            TExprKind::Call(f, args) | TExprKind::GenericCall(f, _, args) => {
                let params = self.sigs.get(*f).map(|s| &s.params);
                for (k, arg) in args.iter().enumerate() {
                    let conv = params
                        .and_then(|p| p.get(k))
                        .map_or(Convention::Let, |p| p.1);
                    if matches!(conv, Convention::Sink | Convention::Set) {
                        continue;
                    }
                    let arg = match &arg.kind {
                        TExprKind::Ref(place) => place,
                        _ => arg,
                    };
                    if !lends(arg.ty) {
                        continue;
                    }
                    if arg.ty.is_view() || is_place(arg) {
                        self.roots_into(cx, arg, out);
                    } else {
                        out.temp = true;
                    }
                }
            }
            // `mem.view`: from every parameter that can lend storage.
            TExprKind::Intrinsic(Intrinsic::View | Intrinsic::StrView, _) => {
                for p in 0..cx.params {
                    let local = &cx.locals[p];
                    if matches!(local.convention, Some(Convention::Let | Convention::Inout))
                        && lends(local.ty)
                    {
                        out.locals.insert(p);
                    }
                }
            }
            _ => out.temp = true,
        }
    }

    /// The view `value` is kept in `local` (a `let`, a `var` or an
    /// assignment): it must not view a temporary, a copy of an `inout`
    /// slice, or a variable of a deeper block. What it borrows from is
    /// added to `local`'s roots by [`Checker::record_borrows`].
    pub(super) fn check_kept_view(
        &mut self,
        cx: &FnCx,
        local: LocalId,
        value: &TExpr,
        span: Span,
    ) -> Option<()> {
        if !value.ty.is_view() {
            return Some(());
        }
        let roots = self.view_roots(cx, value);
        let name = cx.locals[local].name.clone();
        if roots.temp {
            self.diags.push(
                Diagnostic::error(
                    span,
                    format!("`{name}` can't keep a view of a temporary value, which ends with its statement"),
                )
                .with_help("store the value in a variable first (`let v = ...`), then view it, or pass the view straight to the function that takes it"),
            );
            return None;
        }
        let depth = scope_depth(cx, local);
        for &r in &roots.locals {
            let rname = &cx.locals[r].name;
            if cx.locals[r].mutable_view() {
                let sliced = !matches!(value.kind, TExprKind::Local(_));
                let what = if sliced { "a slice" } else { "a copy" };
                self.diags.push(
                    Diagnostic::error(
                        span,
                        format!("cannot keep {what} of `{rname}`, an `inout` slice"),
                    )
                    .with_help(format!(
                        "its elements can change; use `{rname}` itself, or pass it to the function that takes the slice"
                    )),
                );
                return None;
            }
            if r != local && scope_depth(cx, r) > depth {
                self.diags.push(
                    Diagnostic::error(
                        span,
                        format!("`{name}` can't keep a view of `{rname}`, which ends before `{name}` does"),
                    )
                    .with_help(format!(
                        "a view can't outlive what it views: declare `{name}` in the block of `{rname}`"
                    )),
                );
                return None;
            }
        }
        Some(())
    }

    /// `local`, a view local, was given `value`: what it borrows from now
    /// includes what `value` borrows from.
    pub(super) fn record_borrows(&self, cx: &mut FnCx, local: LocalId, value: &TExpr) {
        if !cx.locals[local].ty.is_view() {
            return;
        }
        let roots = self.view_roots(cx, value);
        let entry = cx.borrows.entry(local).or_default();
        entry.extend(roots.locals.into_iter().filter(|&r| r != local));
    }

    /// A function returning a view returns `e` at `span`: it may only
    /// borrow from the function's read-only and `inout` parameters (or from
    /// nothing).
    pub(super) fn check_returned_view(&mut self, cx: &FnCx, e: &TExpr, span: Span) {
        let roots = self.view_roots(cx, e);
        let help = "a returned view borrows from the parameters (docs/memory.md, Views): return a view of a parameter, or a value that owns its storage, like a `String`";
        if roots.temp {
            self.diags.push(
                Diagnostic::error(
                    span,
                    "this returns a view of a temporary value, which ends with its statement",
                )
                .with_help(help),
            );
            return;
        }
        for &r in &roots.locals {
            let local = &cx.locals[r];
            let name = &local.name;
            let msg = if r >= cx.params {
                if name.starts_with('$') {
                    "this returns a view of a temporary value, which ends with its statement"
                        .to_owned()
                } else {
                    format!(
                        "this returns a view of `{name}`, a local variable, which ends when the function returns"
                    )
                }
            } else {
                match local.convention {
                    Some(Convention::Sink) => format!(
                        "this returns a view of `{name}`, a `sink` parameter, which the function destroys when it returns"
                    ),
                    Some(Convention::Set) => format!(
                        "this returns a view of `{name}`, a `set` parameter, which the function assigns"
                    ),
                    _ => continue,
                }
            };
            self.diags
                .push(Diagnostic::error(span, msg).with_help(help));
            return;
        }
    }

    /// A `defer` body runs when its block is left, after code it isn't
    /// checked with: it can use a view declared outside it only if what
    /// the view borrows from can't change (read-only parameters, and `let`
    /// variables of `Copy` types). Whether the use of `local` at `span` is
    /// fine (otherwise it's reported).
    pub(super) fn check_deferred_view(&mut self, cx: &FnCx, local: LocalId, span: Span) -> bool {
        if cx.defer_depth == 0 || local >= cx.defer_floor || !cx.locals[local].ty.is_view() {
            return true;
        }
        let Some(roots) = cx.borrows.get(&local) else {
            return true;
        };
        // A read-only parameter, or a `let` whose value is `Copy` (it's
        // never assigned, changed or moved), stays as it is.
        let fixed = |r: LocalId| {
            let l = &cx.locals[r];
            if r < cx.params {
                l.convention == Some(Convention::Let)
            } else {
                !l.mutable && l.ty.is_copy() && !l.name.starts_with('$')
            }
        };
        let Some(&r) = roots.iter().find(|&&r| !fixed(r)) else {
            return true;
        };
        let name = &cx.locals[local].name;
        let rname = &cx.locals[r].name;
        self.diags.push(
            Diagnostic::error(
                span,
                format!("a `defer` body can't use `{name}`, which views `{rname}`: it runs when the block is left, after `{rname}` may have changed"),
            )
            .with_help(format!(
                "keep what the `defer` needs in a variable that isn't a view, or view `{rname}` in the body"
            )),
        );
        false
    }

    /// Report a use of the view `local`, whose root changed (on some path
    /// to here): whether it was one.
    pub(super) fn stale_view_error(&mut self, cx: &FnCx, local: LocalId, span: Span) -> bool {
        let Some(&(src, how, at)) = cx.stale.get(&local) else {
            return false;
        };
        let name = &cx.locals[local].name;
        let src_name = &cx.locals[src].name;
        let verb = how.verb();
        let here = match how {
            Change::Changed => "changes here",
            Change::Moved => "is moved here",
        };
        // The sequence of a `for` loop, read at each iteration.
        if name.starts_with('$') {
            self.diags.push(
                Diagnostic::error(
                    span,
                    format!("this loop goes over a view of `{src_name}`, which the loop's body {}", match how {
                        Change::Changed => "changes",
                        Change::Moved => "moves",
                    }),
                )
                .with_note(at, format!("`{src_name}` {here}"))
                .with_help(format!(
                    "a view can't see what it views change, move or end: loop over the indexes (`for i in 0..{src_name}.len`), or leave the loop (`break`) after the change"
                )),
            );
            return true;
        }
        self.diags.push(
            Diagnostic::error(
                span,
                format!("`{name}` is used after `{src_name}` {verb} (on some path to here), and `{name}` views `{src_name}`"),
            )
            .with_note(at, format!("`{src_name}` {here}"))
            .with_help(format!(
                "a view can't see what it views change, move or end: use `{name}` before changing `{src_name}`, or view `{src_name}` again after"
            )),
        );
        true
    }
}
