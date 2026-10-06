//! The compile-time evaluator (docs/generics.md, The evaluator): a
//! tree-walking interpreter over the checker's typed tree.
//!
//! It runs a constant's value and the condition of an `if comptime`, and the
//! functions they call, which are checked on demand. Values are abstract:
//! integers as `i128` within their type, aggregates as lists, with no memory
//! layout, so results don't depend on the machine the compiler runs on.
//! `usize` is the target's.
//!
//! Evaluation has the program's semantics. A function was checked, and its
//! proof obligations proven, so it can't overflow or index out of bounds;
//! code that only runs at compile time has its unproven operations wrapped
//! in [`TExprKind::Unproven`], which the evaluator checks as it runs. It's
//! hermetic (raw pointers and `syscall` are errors), and bounded by a step
//! budget (a step is one statement or one call), a memory budget, and a
//! limit on nested calls.

use std::rc::Rc;

use super::{Checker, FuncId, Handler, Intrinsic, LocalId, TBinOp, TExpr, TExprKind, TStmt, TUnOp};
use crate::diag::Diagnostic;
use crate::sema::tree::{CmpOp, Mode};
use crate::source::Span;
use crate::types::{IntTy, Ty};

/// The steps an evaluation may take unless `@comptime_budget(n)` says
/// otherwise.
pub(super) const DEFAULT_STEPS: u64 = 1_000_000;

/// The scalars an evaluation may allocate in all (arrays built or copied
/// to be changed).
const MEMORY_BUDGET: u64 = 1 << 24;

/// How deep calls may nest.
const MAX_DEPTH: usize = 1000;

/// A value at compile time.
#[derive(Clone, Debug)]
pub(super) enum Value {
    /// A variable not assigned yet (a `var x: T`, a `set` parameter).
    Uninit,
    Unit,
    Int(i128),
    Bool(bool),
    /// A `str`: bytes `start..start + len` of a string, by index into the
    /// checker's strings.
    Str(StrVal),
    Array(Rc<Vec<Value>>),
    /// A view of `len` elements of an array, from `start`.
    Slice(Rc<Vec<Value>>, usize, usize),
    Struct(Rc<Vec<Value>>),
    /// A value of an enum, an optional or a result: the variant's index and
    /// its payload.
    Variant(u32, Rc<Vec<Value>>),
}

/// A `str` at compile time: part of one of the checker's strings, and the
/// string literal it's part of, when it comes from one in the source (for
/// errors that point into it, like a format string's).
#[derive(Clone, Copy, Debug)]
pub(super) struct StrVal {
    pub(super) id: usize,
    pub(super) start: usize,
    pub(super) len: usize,
    /// The span of the string literal (quotes included) whose value is the
    /// string `id`.
    pub(super) origin: Option<Span>,
}

impl StrVal {
    pub(super) fn bytes<'s>(&self, strings: &'s [Vec<u8>]) -> &'s [u8] {
        &strings[self.id][self.start..self.start + self.len]
    }
}

impl Value {
    pub(super) fn int(&self) -> i128 {
        match self {
            Value::Int(v) => *v,
            Value::Bool(b) => i128::from(*b),
            other => unreachable!("not an integer: {other:?}"),
        }
    }

    fn bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            other => unreachable!("not a bool: {other:?}"),
        }
    }

    fn variant(&self) -> (u32, &[Value]) {
        match self {
            Value::Variant(k, fields) => (*k, fields),
            other => unreachable!("not a variant: {other:?}"),
        }
    }

    /// The elements of an array or a slice.
    fn elems(&self) -> &[Value] {
        match self {
            Value::Array(xs) => xs,
            Value::Slice(xs, start, len) => &xs[*start..start + len],
            other => unreachable!("not an array or slice: {other:?}"),
        }
    }

    fn variant_of(k: u32, fields: Vec<Value>) -> Value {
        Value::Variant(k, Rc::new(fields))
    }
}

/// The elements of an array or a slice.
pub(super) fn elems(v: &Value) -> &[Value] {
    v.elems()
}

/// Whether two values of the same type are equal (`==`).
pub(super) fn equal(a: &Value, b: &Value, strings: &[Vec<u8>]) -> bool {
    match (a, b) {
        (Value::Int(_) | Value::Bool(_), _) => a.int() == b.int(),
        (Value::Unit, _) => true,
        (Value::Str(x), Value::Str(y)) => x.bytes(strings) == y.bytes(strings),
        (Value::Struct(x), Value::Struct(y)) => {
            x.iter().zip(y.iter()).all(|(a, b)| equal(a, b, strings))
        }
        (Value::Variant(k, x), Value::Variant(j, y)) => {
            k == j && x.iter().zip(y.iter()).all(|(a, b)| equal(a, b, strings))
        }
        _ => {
            let (x, y) = (a.elems(), b.elems());
            x.len() == y.len() && x.iter().zip(y).all(|(a, b)| equal(a, b, strings))
        }
    }
}

/// `v` reduced to the integer type `t` (two's complement, modulo `2^bits`).
fn wrap(v: i128, t: IntTy) -> i128 {
    let modulus = 1i128 << t.bits;
    let m = v.rem_euclid(modulus);
    if t.signed && m > t.max() {
        m - modulus
    } else {
        m
    }
}

/// Why an evaluation stopped early.
pub(super) enum Exit {
    /// It failed: a compile error.
    Fail(Fail),
    Break,
    Continue,
    Return(Value),
    /// A `throw` (or `try`) leaving the function with an error.
    Throw(Value),
}

/// A failed evaluation.
pub(super) enum Fail {
    /// A function it runs has errors, which are reported.
    Reported,
    /// A `compile_error` was reached: its message, and where it's
    /// reported.
    User { msg: String, span: Span },
    Error {
        msg: String,
        /// Where it failed, when that's known (an unproven operation).
        span: Option<Span>,
        help: Vec<String>,
        /// The functions running when it failed, innermost first.
        trace: Vec<FuncId>,
    },
}

fn fail<T>(msg: impl Into<String>) -> Result<T, Exit> {
    Err(Exit::Fail(Fail::Error {
        msg: msg.into(),
        span: None,
        help: Vec::new(),
        trace: Vec::new(),
    }))
}

type R<T> = Result<T, Exit>;

/// The variables of one function call, and its type arguments.
struct Frame {
    locals: Vec<Value>,
    /// Each type parameter of the function, with its type argument.
    subst: Vec<(Ty, Ty)>,
}

impl Frame {
    fn ty(&self, ty: Ty) -> Ty {
        if self.subst.is_empty() {
            return ty;
        }
        ty.subst(&|p| self.subst.iter().find(|(q, _)| *q == p).map(|(_, a)| *a))
    }

    fn int_ty(&self, ty: Ty) -> IntTy {
        match self.ty(ty) {
            Ty::Int(t) => t,
            Ty::Bool => IntTy::new(false, 1),
            other => unreachable!("not an integer type: {other}"),
        }
    }
}

/// One step of a path into a value, from a local.
#[derive(Clone, Copy, Debug)]
enum Step {
    Index(usize),
    Field(u32),
    Payload(u32),
    /// The elements `start..end` of an array or slice, as a slice.
    Range(usize, usize),
}

/// A place: a local and the path into it.
struct Place {
    local: LocalId,
    path: Vec<Step>,
}

/// A running evaluation.
pub(super) struct Eval<'c, 'a> {
    ck: &'c mut Checker<'a>,
    steps: u64,
    budget: u64,
    cells: u64,
    depth: usize,
}

/// What [`Checker::evaluate`] reports a failure for: the thing evaluated
/// (`the value of `X``) and where it is.
pub(super) struct Subject<'s> {
    pub what: &'s str,
    pub span: Span,
    /// The span of a `@comptime_budget` that set the budget, if one did.
    pub budget_span: Option<Span>,
}

impl<'a> Checker<'a> {
    /// Evaluate `e`, an expression checked with `locals` locals (hidden ones,
    /// for a constant), within `budget` steps. A failure is reported here,
    /// about `subject`.
    pub(super) fn evaluate(
        &mut self,
        e: &TExpr,
        locals: usize,
        budget: u64,
        subject: &Subject<'_>,
    ) -> Option<Value> {
        self.evaluate_with(e, locals, &[], budget, subject)
    }

    /// [`Checker::evaluate`], with the values `init` of some of the locals
    /// (those known when compiling).
    pub(super) fn evaluate_with(
        &mut self,
        e: &TExpr,
        locals: usize,
        init: &[(LocalId, Value)],
        budget: u64,
        subject: &Subject<'_>,
    ) -> Option<Value> {
        let mut ev = Eval {
            ck: self,
            steps: 0,
            budget,
            cells: 0,
            depth: 0,
        };
        let mut frame = Frame {
            locals: vec![Value::Uninit; locals],
            subst: Vec::new(),
        };
        for (l, v) in init {
            frame.locals[*l] = v.clone();
        }
        let out = ev.expr(&mut frame, e);
        let fail = match out {
            Ok(v) => return Some(v),
            Err(Exit::Fail(f)) => f,
            Err(_) => Fail::Error {
                msg: "this can't leave the evaluation".to_owned(),
                span: None,
                help: Vec::new(),
                trace: Vec::new(),
            },
        };
        let (msg, span, help, trace) = match fail {
            Fail::Reported => return None,
            Fail::User { msg, span } => {
                self.diags.push(Diagnostic::error(span, msg));
                return None;
            }
            Fail::Error {
                msg,
                span,
                help,
                trace,
            } => (msg, span, help, trace),
        };
        let mut d = Diagnostic::error(
            span.unwrap_or(subject.span),
            format!("evaluating {} at compile time: {msg}", subject.what),
        );
        for h in help {
            d = d.with_help(h);
        }
        if msg.starts_with("it takes more than") {
            d = d.with_help(match subject.budget_span {
                Some(_) => "raise the budget in `@comptime_budget(n)`".to_owned(),
                None => {
                    "raise the budget with `@comptime_budget(n)` on the line before the `const`"
                        .to_owned()
                }
            });
        }
        // The calls, innermost first: a run of calls of one function (a
        // recursion) is one note, and only the ends of a long chain are
        // shown.
        let mut runs: Vec<(FuncId, usize)> = Vec::new();
        for &f in &trace {
            match runs.last_mut() {
                Some((g, n)) if *g == f => *n += 1,
                _ => runs.push((f, 1)),
            }
        }
        const SHOWN: usize = 4;
        for (k, &(f, n)) in runs.iter().enumerate() {
            if runs.len() > 2 * SHOWN && k >= SHOWN && k < runs.len() - SHOWN {
                if k == SHOWN {
                    let hidden: usize = runs[SHOWN..runs.len() - SHOWN].iter().map(|r| r.1).sum();
                    d = d.with_help(format!("{hidden} more calls are not shown"));
                }
                continue;
            }
            let sig = &self.sigs[f];
            let note = match n {
                1 => format!("in `{}`", sig.name),
                n => format!("in `{}`, {n} calls deep", sig.name),
            };
            d = d.with_note(sig.span, note);
        }
        self.diags.push(d);
        None
    }
}

impl Eval<'_, '_> {
    fn step(&mut self) -> R<()> {
        self.steps += 1;
        if self.steps > self.budget {
            return fail(format!("it takes more than {} steps", self.budget));
        }
        Ok(())
    }

    /// Count `n` scalars against the memory budget.
    fn alloc(&mut self, n: u64) -> R<()> {
        self.cells = self.cells.saturating_add(n);
        if self.cells > MEMORY_BUDGET {
            return fail(format!(
                "it uses more than {MEMORY_BUDGET} scalars of memory"
            ));
        }
        Ok(())
    }

    fn block(&mut self, frame: &mut Frame, stmts: &[TStmt]) -> R<()> {
        let mut defers: Vec<(&[TStmt], bool)> = Vec::new();
        let mut out = Ok(());
        for s in stmts {
            if let TStmt::Defer { body, on_error } = s {
                defers.push((body, *on_error));
                continue;
            }
            out = self.stmt(frame, s);
            if out.is_err() {
                break;
            }
        }
        if matches!(out, Err(Exit::Fail(_))) {
            return out;
        }
        let threw = matches!(out, Err(Exit::Throw(_)));
        for (body, on_error) in defers.into_iter().rev() {
            if !on_error || threw {
                // A `defer` body never leaves itself: only a failure stops it.
                if let Err(Exit::Fail(f)) = self.block(frame, body) {
                    return Err(Exit::Fail(f));
                }
            }
        }
        out
    }

    fn stmt(&mut self, frame: &mut Frame, s: &TStmt) -> R<()> {
        if let TStmt::Loc(_) = s {
            return Ok(());
        }
        self.step()?;
        match s {
            TStmt::Init(l, e) | TStmt::Assign(l, e) => {
                let v = self.expr(frame, e)?;
                frame.locals[*l] = v;
            }
            TStmt::Store(place, e) => {
                let place = self.place(frame, place)?;
                let v = self.expr(frame, e)?;
                self.store(frame, &place, v)?;
            }
            TStmt::Expr(e) => {
                self.expr(frame, e)?;
            }
            TStmt::Return(e) => {
                let v = match e {
                    Some(e) => self.expr(frame, e)?,
                    None => Value::Unit,
                };
                return Err(Exit::Return(v));
            }
            TStmt::If(c, then, otherwise) => {
                if self.expr(frame, c)?.bool() {
                    self.block(frame, then)?;
                } else {
                    self.block(frame, otherwise)?;
                }
            }
            TStmt::While(c, body) => loop {
                if !self.expr(frame, c)?.bool() {
                    break;
                }
                match self.block(frame, body) {
                    Ok(()) | Err(Exit::Continue) => {}
                    Err(Exit::Break) => break,
                    Err(e) => return Err(e),
                }
                self.step()?;
            },
            TStmt::Loop(body) => loop {
                match self.block(frame, body) {
                    Ok(()) | Err(Exit::Continue) => {}
                    Err(Exit::Break) => break,
                    Err(e) => return Err(e),
                }
                self.step()?;
            },
            TStmt::For {
                var,
                start,
                end,
                body,
            } => {
                let a = self.expr(frame, start)?.int();
                let b = self.expr(frame, end)?.int();
                let mut i = a;
                while i < b {
                    frame.locals[*var] = Value::Int(i);
                    match self.block(frame, body) {
                        Ok(()) | Err(Exit::Continue) => {}
                        Err(Exit::Break) => break,
                        Err(e) => return Err(e),
                    }
                    self.step()?;
                    i += 1;
                }
            }
            TStmt::Loc(_) => {}
            TStmt::Break => return Err(Exit::Break),
            TStmt::Continue => return Err(Exit::Continue),
            TStmt::Block(body) => self.block(frame, body)?,
            TStmt::Match { value, arms } => {
                let v = self.expr(frame, value)?;
                let (k, _) = v.variant();
                let arm = arms
                    .iter()
                    .find(|a| a.variants.contains(&k))
                    .expect("every variant is in an arm");
                self.block(frame, &arm.body)?;
            }
            TStmt::Throw(e) => {
                let v = self.expr(frame, e)?;
                return Err(Exit::Throw(v));
            }
            TStmt::Defer { .. } => unreachable!("handled by `block`"),
            // Nothing is destroyed at compile time: a `deinit` releases what
            // a program holds when it runs, and a value made while compiling
            // holds nothing (docs/allocation.md, When destruction runs).
            TStmt::Drop { .. } | TStmt::Destroy(_) => {}
        }
        Ok(())
    }

    fn exprs(&mut self, frame: &mut Frame, es: &[TExpr]) -> R<Vec<Value>> {
        es.iter().map(|e| self.expr(frame, e)).collect()
    }

    fn expr(&mut self, frame: &mut Frame, e: &TExpr) -> R<Value> {
        // `a.lt(b)` of a type that implements `Ordered` with an `impl`.
        if let TExprKind::Compare(a, _) | TExprKind::Binary(_, a, _) = &e.kind
            && let Some(call) = self.ck.dispatch.ordered_expr(e, frame.ty(a.ty))
        {
            return self.expr(frame, &call);
        }
        Ok(match &e.kind {
            TExprKind::Int(v) => Value::Int(*v),
            TExprKind::Bool(b) => Value::Bool(*b),
            TExprKind::Str(id) => Value::Str(StrVal {
                id: *id,
                start: 0,
                len: self.ck.strings[*id].len(),
                origin: None,
            }),
            TExprKind::Table(id) => {
                let table = &self.ck.tables[*id];
                let mut values = table.values.iter().copied();
                let v = build(table.ty, &mut values);
                debug_assert!(values.next().is_none());
                v
            }
            TExprKind::Local(l) => match &frame.locals[*l] {
                Value::Uninit => return fail("a variable is used before it's assigned"),
                v => v.clone(),
            },
            TExprKind::Call(f, args) => self.call(frame, *f, Vec::new(), args)?,
            TExprKind::GenericCall(f, types, args) => {
                let types: Vec<Ty> = types.iter().map(|&t| frame.ty(t)).collect();
                // A trait's method runs the method of `Self`'s impl.
                let (g, types) = self.ck.dispatch.resolve(*f, &types);
                let v = self.call(frame, g, types, args)?;
                // An impl's method that doesn't throw, called through a
                // trait's that does: its value is a success.
                match e.ty.as_result() {
                    Some((ok, _)) if g != *f && self.ck.sigs[g].throws.is_none() => match ok {
                        Ty::Unit => Value::variant_of(0, Vec::new()),
                        _ => Value::variant_of(0, vec![v]),
                    },
                    _ => v,
                }
            }
            TExprKind::Compare(a, b) => {
                let (a, b) = (self.expr(frame, a)?.int(), self.expr(frame, b)?.int());
                let k = match a.cmp(&b) {
                    std::cmp::Ordering::Less => 0,
                    std::cmp::Ordering::Equal => 1,
                    std::cmp::Ordering::Greater => 2,
                };
                Value::variant_of(k, Vec::new())
            }
            TExprKind::Unary(op, inner) => {
                let v = self.expr(frame, inner)?;
                match op {
                    TUnOp::Not => Value::Bool(!v.bool()),
                    TUnOp::Neg => {
                        let t = frame.int_ty(e.ty);
                        let r = -v.int();
                        if r < t.min() || r > t.max() {
                            return fail(format!("`-({})` doesn't fit in `{t}`", v.int()));
                        }
                        Value::Int(r)
                    }
                    TUnOp::BitNot => Value::Int(wrap(!v.int(), frame.int_ty(e.ty))),
                }
            }
            TExprKind::Binary(op, l, r) => {
                let a = self.expr(frame, l)?;
                let b = self.expr(frame, r)?;
                self.binary(frame, *op, l.ty, a, b)?
            }
            TExprKind::And(l, r) => {
                Value::Bool(self.expr(frame, l)?.bool() && self.expr(frame, r)?.bool())
            }
            TExprKind::Or(l, r) => {
                Value::Bool(self.expr(frame, l)?.bool() || self.expr(frame, r)?.bool())
            }
            TExprKind::Convert(inner) => {
                let v = self.expr(frame, inner)?.int();
                let t = frame.int_ty(e.ty);
                if v < t.min() || v > t.max() {
                    return fail(format!("{v} doesn't fit in `{t}`"));
                }
                Value::Int(v)
            }
            TExprKind::ViewLen(inner) => match self.expr(frame, inner)? {
                Value::Str(s) => Value::Int(s.len as i128),
                v => Value::Int(v.elems().len() as i128),
            },
            TExprKind::ArrayLen(inner) => {
                self.expr(frame, inner)?;
                let (_, n) = frame.ty(inner.ty).as_known_array().expect("an array");
                Value::Int(i128::from(n))
            }
            TExprKind::ArrayLit(items) => {
                let vs = self.exprs(frame, items)?;
                self.alloc(vs.len() as u64)?;
                Value::Array(Rc::new(vs))
            }
            TExprKind::ArrayRepeat(inner) => {
                let (_, n) = frame.ty(e.ty).as_known_array().expect("an array");
                let v = self.expr(frame, inner)?;
                self.alloc(n)?;
                Value::Array(Rc::new(vec![v; n as usize]))
            }
            TExprKind::Index(base, index) => {
                let b = self.expr(frame, base)?;
                let i = self.expr(frame, index)?.int();
                let xs = b.elems();
                match usize::try_from(i).ok().filter(|&i| i < xs.len()) {
                    Some(i) => xs[i].clone(),
                    None => {
                        return fail(format!(
                            "the index {i} is out of bounds: the length is {}",
                            xs.len()
                        ));
                    }
                }
            }
            TExprKind::Slice(base, start, end) => {
                let b = self.expr(frame, base)?;
                if let Value::Str(sv) = b {
                    return self.str_slice(frame, sv, start.as_deref(), end.as_deref());
                }
                let len = b.elems().len();
                let s = match start {
                    Some(s) => self.expr(frame, s)?.int(),
                    None => 0,
                };
                let t = match end {
                    Some(t) => self.expr(frame, t)?.int(),
                    None => len as i128,
                };
                if s < 0 || s > t || t > len as i128 {
                    return fail(format!(
                        "the slice {s}..{t} is out of bounds: the length is {len}"
                    ));
                }
                let (s, t) = (s as usize, t as usize);
                match b {
                    Value::Slice(xs, start, _) => Value::Slice(xs, start + s, t - s),
                    Value::Array(xs) => Value::Slice(xs, s, t - s),
                    other => unreachable!("not a view: {other:?}"),
                }
            }
            TExprKind::StructLit(fields) => {
                let def = frame.ty(e.ty).as_struct().expect("a struct");
                let mut vs = vec![Value::Unit; def.fields.len()];
                for (k, v) in fields {
                    vs[*k as usize] = self.expr(frame, v)?;
                }
                // An `@uninit` field `unsafe` code left out: an array of
                // integers, zeros while compiling, which its package never
                // reads before writing.
                for (k, f) in def.fields.iter().enumerate() {
                    if f.uninit && !fields.iter().any(|(i, _)| *i as usize == k) {
                        let (_, n) = f.ty.as_known_array().expect("an array");
                        self.alloc(n)?;
                        vs[k] = Value::Array(Rc::new(vec![Value::Int(0); n as usize]));
                    }
                }
                self.check_fields(frame.ty(e.ty), &vs)?;
                Value::Struct(Rc::new(vs))
            }
            TExprKind::Refined(inner, k) => {
                let v = self.expr(frame, inner)?;
                if let Some(msg) = self.ck.refined_fails(*k, &v) {
                    return fail(msg);
                }
                v
            }
            TExprKind::Field(base, k) => match self.expr(frame, base)? {
                Value::Struct(fields) => fields[*k as usize].clone(),
                other => unreachable!("not a struct: {other:?}"),
            },
            TExprKind::ToSlice(inner) => match self.expr(frame, inner)? {
                Value::Array(xs) => {
                    let n = xs.len();
                    Value::Slice(xs, 0, n)
                }
                other => unreachable!("not an array: {other:?}"),
            },
            TExprKind::StrPtr(_) | TExprKind::PtrAdd(..) => {
                return fail("raw pointers don't exist at compile time");
            }
            TExprKind::Syscall(_) => {
                return Err(Exit::Fail(Fail::Error {
                    msg: "it reaches a `syscall`".to_owned(),
                    span: None,
                    help: vec!["compile-time code is hermetic: no system calls, no I/O".to_owned()],
                    trace: Vec::new(),
                }));
            }
            TExprKind::Bytes(inner) => {
                let Value::Str(s) = self.expr(frame, inner)? else {
                    unreachable!("`bytes` of a string")
                };
                let bytes: Vec<Value> = s
                    .bytes(&self.ck.strings)
                    .iter()
                    .map(|&b| Value::Int(i128::from(b)))
                    .collect();
                self.alloc(bytes.len() as u64)?;
                let n = bytes.len();
                Value::Slice(Rc::new(bytes), 0, n)
            }
            TExprKind::Variant(k, fields) => {
                let vs = self.exprs(frame, fields)?;
                Value::variant_of(*k, vs)
            }
            TExprKind::Payload(base, variant, field) => {
                let v = self.expr(frame, base)?;
                let (k, fields) = v.variant();
                debug_assert_eq!(k, *variant);
                fields[*field as usize].clone()
            }
            TExprKind::Coalesce(opt, default) => {
                let v = self.expr(frame, opt)?;
                match v.variant() {
                    (1, fields) => fields[0].clone(),
                    _ => self.expr(frame, default)?,
                }
            }
            TExprKind::EnumValue(inner) => {
                let v = self.expr(frame, inner)?;
                let def = frame.ty(inner.ty).as_enum().expect("an enum");
                Value::Int(def.variants[v.variant().0 as usize].value)
            }
            TExprKind::EnumFrom(inner) => {
                let v = self.expr(frame, inner)?.int();
                let enum_ty = frame.ty(e.ty).as_optional().expect("an optional enum");
                let def = enum_ty.as_enum().expect("an enum");
                match def.variants.iter().position(|var| var.value == v) {
                    Some(k) => Value::variant_of(1, vec![Value::variant_of(k as u32, Vec::new())]),
                    None => Value::variant_of(0, Vec::new()),
                }
            }
            TExprKind::Try(call) => {
                let v = self.expr(frame, call)?;
                match v.variant() {
                    (0, fields) => fields.first().cloned().unwrap_or(Value::Unit),
                    (_, fields) => return Err(Exit::Throw(fields[0].clone())),
                }
            }
            TExprKind::Catch {
                call,
                binding,
                handler,
            } => {
                let v = self.expr(frame, call)?;
                match v.variant() {
                    (0, fields) => fields.first().cloned().unwrap_or(Value::Unit),
                    (_, fields) => {
                        if let Some(b) = binding {
                            frame.locals[*b] = fields[0].clone();
                        }
                        match handler {
                            Handler::Value(d) => self.expr(frame, d)?,
                            Handler::Block(body) => {
                                self.block(frame, body)?;
                                Value::Unit
                            }
                        }
                    }
                }
            }
            TExprKind::Throw(inner) => {
                let v = self.expr(frame, inner)?;
                return Err(Exit::Throw(v));
            }
            TExprKind::Ref(_) => unreachable!("only a call's argument"),
            // Values are abstract here: a move or a temporary is its value
            // (see `TStmt::Drop` in `Eval::stmt`).
            TExprKind::Move(inner, _) | TExprKind::Temp(_, inner) => self.expr(frame, inner)?,
            TExprKind::Intrinsic(Intrinsic::Swap, args) => {
                let places = args
                    .iter()
                    .map(|a| match &a.kind {
                        TExprKind::Ref(place) => self.place(frame, place),
                        _ => unreachable!("`swap` takes two places"),
                    })
                    .collect::<R<Vec<Place>>>()?;
                let a = self.load(frame, &places[0]);
                let b = self.load(frame, &places[1]);
                self.store(frame, &places[0], b)?;
                self.store(frame, &places[1], a)?;
                Value::Unit
            }
            TExprKind::Intrinsic(Intrinsic::Take, args) => {
                let TExprKind::Ref(place) = &args[0].kind else {
                    unreachable!("`take` takes a place")
                };
                let place = self.place(frame, place)?;
                let v = self.load(frame, &place);
                self.store(frame, &place, Value::variant_of(0, Vec::new()))?;
                v
            }
            TExprKind::Intrinsic(Intrinsic::Forget, args) => {
                self.expr(frame, &args[0])?;
                Value::Unit
            }
            TExprKind::Clone(inner) => {
                let v = self.expr(frame, inner)?;
                self.clone_value(frame.ty(inner.ty), v)?
            }
            TExprKind::Never(inner) => {
                self.expr(frame, inner)?;
                return fail("a `never` function returned");
            }
            TExprKind::CompileError {
                place,
                message,
                values,
                span,
            } => {
                let place = match place {
                    Some(p) => Some(self.expr(frame, p)?),
                    None => None,
                };
                let Value::Str(message) = self.expr(frame, message)? else {
                    unreachable!("a `str` message")
                };
                let values = self.exprs(frame, values)?;
                let msg = match self.ck.user_message(message, &values) {
                    Ok(msg) => msg,
                    Err(why) => return fail(why),
                };
                let span = place.and_then(|p| self.ck.place_span(&p)).unwrap_or(*span);
                return Err(Exit::Fail(Fail::User { msg, span }));
            }
            TExprKind::Unproven(span, inner) => match self.expr(frame, inner) {
                Err(Exit::Fail(Fail::Error {
                    msg,
                    span: None,
                    help,
                    trace,
                })) if trace.is_empty() => {
                    return Err(Exit::Fail(Fail::Error {
                        msg,
                        span: Some(*span),
                        help,
                        trace,
                    }));
                }
                other => other?,
            },
        })
    }

    /// `s[start..end]` of a `str`, in code that only runs at compile time:
    /// the bounds must be in it, and on character boundaries.
    fn str_slice(
        &mut self,
        frame: &mut Frame,
        sv: StrVal,
        start: Option<&TExpr>,
        end: Option<&TExpr>,
    ) -> R<Value> {
        let s = match start {
            Some(e) => self.expr(frame, e)?.int(),
            None => 0,
        };
        let t = match end {
            Some(e) => self.expr(frame, e)?.int(),
            None => sv.len as i128,
        };
        if s < 0 || s > t || t > sv.len as i128 {
            return fail(format!(
                "the slice {s}..{t} is out of bounds: the length is {}",
                sv.len
            ));
        }
        let bytes = sv.bytes(&self.ck.strings);
        let boundary = |i: usize| i == bytes.len() || bytes[i] & 0xc0 != 0x80;
        for i in [s as usize, t as usize] {
            if !boundary(i) {
                return fail(format!("the slice {s}..{t} splits a character at {i}"));
            }
        }
        Ok(Value::Str(StrVal {
            start: sv.start + s as usize,
            len: (t - s) as usize,
            ..sv
        }))
    }

    fn binary(&mut self, frame: &Frame, op: TBinOp, ty: Ty, a: Value, b: Value) -> R<Value> {
        if let TBinOp::Cmp(c) = op {
            let r = match c {
                CmpOp::Eq => equal(&a, &b, &self.ck.strings),
                CmpOp::Ne => !equal(&a, &b, &self.ck.strings),
                CmpOp::Lt => a.int() < b.int(),
                CmpOp::Le => a.int() <= b.int(),
                CmpOp::Gt => a.int() > b.int(),
                CmpOp::Ge => a.int() >= b.int(),
            };
            return Ok(Value::Bool(r));
        }
        let t = frame.int_ty(ty);
        let (x, y) = (a.int(), b.int());
        let fits = |v: i128| v >= t.min() && v <= t.max();
        let arith = |mode: Mode, exact: Option<i128>, wrapped: i128, sign: bool, name: &str| match (
            mode, exact,
        ) {
            (Mode::Wrap, _) => Ok(Value::Int(wrap(wrapped, t))),
            (Mode::Saturate, Some(v)) => Ok(Value::Int(v.clamp(t.min(), t.max()))),
            (Mode::Saturate, None) => Ok(Value::Int(if sign { t.max() } else { t.min() })),
            (Mode::Proven, Some(v)) if fits(v) => Ok(Value::Int(v)),
            (Mode::Proven, _) => fail(format!("{x} {name} {y} overflows `{t}`")),
        };
        let v = match op {
            TBinOp::Add(m) => return arith(m, x.checked_add(y), x.wrapping_add(y), x > 0, "+"),
            TBinOp::Sub(m) => return arith(m, x.checked_sub(y), x.wrapping_sub(y), x > 0, "-"),
            TBinOp::Mul(m) => {
                let sign = (x < 0) == (y < 0);
                return arith(m, x.checked_mul(y), x.wrapping_mul(y), sign, "*");
            }
            TBinOp::Div | TBinOp::Rem => {
                if y == 0 {
                    return fail(format!("{x} is divided by zero"));
                }
                let q = x / y;
                if !fits(q) {
                    return fail(format!("{x} / {y} overflows `{t}`"));
                }
                if op == TBinOp::Div { q } else { x % y }
            }
            TBinOp::BitAnd => x & y,
            TBinOp::BitOr => x | y,
            TBinOp::BitXor => x ^ y,
            TBinOp::Shl | TBinOp::Shr => {
                if y < 0 || y >= i128::from(t.bits) {
                    return fail(format!(
                        "the shift amount {y} isn't less than {}, the width of `{t}`",
                        t.bits
                    ));
                }
                if op == TBinOp::Shl {
                    wrap(((x as u128) << y) as i128, t)
                } else {
                    x >> y
                }
            }
            TBinOp::ShlWrap => {
                let s = y.rem_euclid(i128::from(t.bits));
                wrap(((x as u128) << s) as i128, t)
            }
            TBinOp::Cmp(_) => unreachable!("handled above"),
        };
        Ok(Value::Int(v))
    }

    /// Call function `f` with type arguments `types` (concrete) and
    /// arguments `args`, evaluated in `frame`.
    fn call(&mut self, frame: &mut Frame, f: FuncId, types: Vec<Ty>, args: &[TExpr]) -> R<Value> {
        self.step()?;
        let func = match self.ck.func_for_eval(f) {
            Ok(Some(func)) => func,
            Ok(None) => return Err(Exit::Fail(Fail::Reported)),
            Err(msg) => return fail(msg),
        };
        if self.depth >= MAX_DEPTH {
            return fail(format!("calls nest more than {MAX_DEPTH} deep"));
        }
        // The arguments, and the places the `inout` and `set` ones refer to.
        let mut callee = Frame {
            locals: vec![Value::Uninit; func.locals.len()],
            subst: func.type_params.iter().copied().zip(types).collect(),
        };
        // Value parameters are locals too, assigned first.
        for &(param, local) in &func.value_params {
            let v = callee.ty(param).as_value().expect("a value argument");
            callee.locals[local] = Value::Int(v);
        }
        let mut places = Vec::new();
        for (&p, arg) in func.params.iter().zip(args) {
            let v = match &arg.kind {
                TExprKind::Ref(place) => {
                    let place = self.place(frame, place)?;
                    let v = if func.locals[p].convention == Some(super::Convention::Set)
                        && !func.locals[p].ty.is_view()
                    {
                        Value::Uninit
                    } else {
                        self.load(frame, &place)
                    };
                    places.push((p, place));
                    v
                }
                _ => self.expr(frame, arg)?,
            };
            callee.locals[p] = v;
        }
        let failed = self.ck.vparams_fail(f, &|t| callee.ty(t)).or_else(|| {
            self.ck
                .params_fail(f, &func.params, &callee.locals, &|t| callee.ty(t))
        });
        if let Some(msg) = failed {
            return fail(msg);
        }
        self.depth += 1;
        let out = self.block(&mut callee, &func.body);
        self.depth -= 1;
        let out = match out {
            Ok(()) => Ok(Value::Unit),
            Err(Exit::Return(v)) => Ok(v),
            Err(Exit::Throw(e)) => Err(e),
            Err(Exit::Fail(Fail::Error {
                msg,
                span,
                help,
                mut trace,
            })) => {
                trace.push(f);
                return Err(Exit::Fail(Fail::Error {
                    msg,
                    span,
                    help,
                    trace,
                }));
            }
            Err(Exit::Fail(f)) => return Err(Exit::Fail(f)),
            Err(Exit::Break | Exit::Continue) => unreachable!("a loop's own"),
        };
        // `inout` and `set` arguments get the parameters' last values, even
        // when the call throws, as in memory.
        for (p, place) in places {
            let v = std::mem::replace(&mut callee.locals[p], Value::Uninit);
            if !matches!(v, Value::Uninit) {
                self.store(frame, &place, v)?;
            }
        }
        Ok(match (func.throws, out) {
            (None, Ok(v)) => v,
            (Some(_), Ok(Value::Unit)) if func.ret == Ty::Unit => Value::variant_of(0, Vec::new()),
            (Some(_), Ok(v)) => Value::variant_of(0, vec![v]),
            (Some(_), Err(e)) => Value::variant_of(1, vec![e]),
            (None, Err(_)) => unreachable!("only a function that throws can throw"),
        })
    }

    /// A call of `f`, with its type arguments, whose parameters are all
    /// passed by value: `args`, of the parameters' types `tys`.
    fn call_values(&mut self, f: FuncId, types: Vec<Ty>, args: Vec<(Value, Ty)>) -> R<Value> {
        let exprs: Vec<TExpr> = args.iter().map(|(v, t)| materialize(v, *t)).collect();
        let mut frame = Frame {
            locals: Vec::new(),
            subst: Vec::new(),
        };
        self.call(&mut frame, f, types, &exprs)
    }

    /// `v.clone()`, for a value `v` of type `ty`: its type's `impl Clone`
    /// runs, or else each part is cloned (a copy for a `Copy` part).
    fn clone_value(&mut self, ty: Ty, v: Value) -> R<Value> {
        if ty.is_copy() {
            return Ok(v);
        }
        if let Some(f) = self.ck.dispatch.clone_impl(ty) {
            let types = ty.type_args().to_vec();
            return self.call_values(f, types, vec![(v, ty)]);
        }
        let clone_all = |ev: &mut Self, vs: &[Value], tys: &[Ty]| -> R<Vec<Value>> {
            vs.iter()
                .zip(tys)
                .map(|(v, &t)| ev.clone_value(t, v.clone()))
                .collect()
        };
        Ok(match (&v, ty) {
            (Value::Struct(fields), _) => {
                let tys: Vec<Ty> = ty
                    .as_struct()
                    .expect("a struct")
                    .fields
                    .iter()
                    .map(|f| f.ty)
                    .collect();
                Value::Struct(std::rc::Rc::new(clone_all(self, fields, &tys)?))
            }
            (Value::Variant(k, fields), _) => {
                let def = ty.sum().expect("an enum or an optional");
                let tys: Vec<Ty> = def.variants[*k as usize]
                    .fields
                    .iter()
                    .map(|f| f.ty)
                    .collect();
                Value::Variant(*k, std::rc::Rc::new(clone_all(self, fields, &tys)?))
            }
            (Value::Array(xs), _) => {
                let (elem, _) = ty.as_array().expect("an array");
                let tys = vec![elem; xs.len()];
                Value::Array(std::rc::Rc::new(clone_all(self, xs, &tys)?))
            }
            _ => v,
        })
    }

    /// A struct value `vs` of type `sty` must meet its fields' refinements.
    fn check_fields(&self, sty: Ty, vs: &[Value]) -> R<()> {
        match self.ck.fields_fail(sty, vs) {
            Some(msg) => fail(msg),
            None => Ok(()),
        }
    }

    /// The place an expression names (a local, an element, a field, a
    /// payload field, or a slice of an array or slice).
    fn place(&mut self, frame: &mut Frame, e: &TExpr) -> R<Place> {
        Ok(match &e.kind {
            TExprKind::Local(l) => Place {
                local: *l,
                path: Vec::new(),
            },
            TExprKind::Index(base, index) => {
                let mut p = self.place(frame, base)?;
                let i = self.expr(frame, index)?.int();
                let len = self.load(frame, &p).elems().len();
                match usize::try_from(i).ok().filter(|&i| i < len) {
                    Some(i) => p.path.push(Step::Index(i)),
                    None => {
                        return fail(format!(
                            "the index {i} is out of bounds: the length is {len}"
                        ));
                    }
                }
                p
            }
            TExprKind::Field(base, k) => {
                let mut p = self.place(frame, base)?;
                p.path.push(Step::Field(*k));
                p
            }
            TExprKind::Payload(base, _, k) => {
                let mut p = self.place(frame, base)?;
                p.path.push(Step::Payload(*k));
                p
            }
            TExprKind::ToSlice(base) => {
                let p = self.place(frame, base)?;
                let len = self.load(frame, &p).elems().len();
                let mut p = p;
                p.path.push(Step::Range(0, len));
                p
            }
            TExprKind::Slice(base, start, end) => {
                let mut p = self.place(frame, base)?;
                let len = self.load(frame, &p).elems().len();
                let s = match start {
                    Some(s) => self.expr(frame, s)?.int(),
                    None => 0,
                };
                let t = match end {
                    Some(t) => self.expr(frame, t)?.int(),
                    None => len as i128,
                };
                if s < 0 || s > t || t > len as i128 {
                    return fail(format!(
                        "the slice {s}..{t} is out of bounds: the length is {len}"
                    ));
                }
                p.path.push(Step::Range(s as usize, t as usize));
                p
            }
            TExprKind::Unproven(_, inner) => self.place(frame, inner)?,
            other => unreachable!("not a place: {other:?}"),
        })
    }

    fn load(&self, frame: &Frame, p: &Place) -> Value {
        let mut v = frame.locals[p.local].clone();
        for step in &p.path {
            v = match *step {
                Step::Index(i) => v.elems()[i].clone(),
                Step::Field(k) => match &v {
                    Value::Struct(fields) => fields[k as usize].clone(),
                    other => unreachable!("not a struct: {other:?}"),
                },
                Step::Payload(k) => v.variant().1[k as usize].clone(),
                Step::Range(s, t) => match v {
                    Value::Array(xs) => Value::Slice(xs, s, t - s),
                    Value::Slice(xs, start, _) => Value::Slice(xs, start + s, t - s),
                    other => unreachable!("not a view: {other:?}"),
                },
            };
        }
        v
    }

    fn store(&mut self, frame: &mut Frame, p: &Place, v: Value) -> R<()> {
        let mut cells = 0;
        set_path(&mut frame.locals[p.local], &p.path, v, &mut cells);
        self.alloc(cells)
    }
}

/// Make `rc` unique to change it, counting the scalars copied if it wasn't.
fn unique<'v>(rc: &'v mut Rc<Vec<Value>>, cells: &mut u64) -> &'v mut Vec<Value> {
    if Rc::strong_count(rc) > 1 {
        *cells += rc.len() as u64;
    }
    Rc::make_mut(rc)
}

/// Replace the part of `root` at `path` with `v`.
fn set_path(root: &mut Value, path: &[Step], v: Value, cells: &mut u64) {
    let Some((step, rest)) = path.split_first() else {
        *root = v;
        return;
    };
    match (*step, root) {
        (Step::Index(i), Value::Array(xs)) => set_path(&mut unique(xs, cells)[i], rest, v, cells),
        (Step::Index(i), Value::Slice(xs, start, _)) => {
            let start = *start;
            set_path(&mut unique(xs, cells)[start + i], rest, v, cells)
        }
        (Step::Field(k), Value::Struct(fields)) => {
            set_path(&mut unique(fields, cells)[k as usize], rest, v, cells)
        }
        (Step::Payload(k), Value::Variant(_, fields)) => {
            set_path(&mut unique(fields, cells)[k as usize], rest, v, cells)
        }
        (Step::Range(s, t), target) => {
            // Only a whole slice is stored there: the elements an `inout`
            // slice parameter ends with.
            debug_assert!(rest.is_empty());
            let new = v.elems().to_vec();
            debug_assert_eq!(new.len(), t - s);
            let (xs, base) = match target {
                Value::Array(xs) => (xs, 0),
                Value::Slice(xs, start, _) => {
                    let start = *start;
                    (xs, start)
                }
                other => unreachable!("not a view: {other:?}"),
            };
            unique(xs, cells)[base + s..base + t].clone_from_slice(&new);
        }
        (step, other) => unreachable!("{step:?} of {other:?}"),
    }
}

/// The value of type `ty` whose scalars are the next ones of `values`
/// (an array constant's).
fn build(ty: Ty, values: &mut impl Iterator<Item = i128>) -> Value {
    match ty.as_known_array() {
        Some((elem, n)) => Value::Array(Rc::new((0..n).map(|_| build(elem, values)).collect())),
        None => {
            let v = values.next().expect("enough scalars");
            if ty == Ty::Bool {
                Value::Bool(v != 0)
            } else {
                Value::Int(v)
            }
        }
    }
}

/// The scalars of `v`, an array constant's value, in memory order.
pub(super) fn flatten(v: &Value, out: &mut Vec<i128>) {
    match v {
        Value::Array(xs) => xs.iter().for_each(|x| flatten(x, out)),
        other => out.push(other.int()),
    }
}

/// The expression of type `ty` that builds `v`.
pub(super) fn materialize(v: &Value, ty: Ty) -> TExpr {
    let kind = match v {
        Value::Int(x) => TExprKind::Int(*x),
        Value::Bool(b) => TExprKind::Bool(*b),
        Value::Str(s) => {
            debug_assert!(s.start == 0, "a whole string");
            TExprKind::Str(s.id)
        }
        Value::Array(xs) => {
            let (elem, _) = ty.as_array().expect("an array");
            TExprKind::ArrayLit(xs.iter().map(|x| materialize(x, elem)).collect())
        }
        Value::Struct(fields) => {
            let def = ty.as_struct().expect("a struct");
            TExprKind::StructLit(
                fields
                    .iter()
                    .zip(&def.fields)
                    .enumerate()
                    .map(|(k, (x, f))| (k as u32, materialize(x, f.ty)))
                    .collect(),
            )
        }
        Value::Variant(k, fields) => {
            let def = ty.sum().expect("an enum or optional");
            let var = &def.variants[*k as usize];
            TExprKind::Variant(
                *k,
                fields
                    .iter()
                    .zip(&var.fields)
                    .map(|(x, f)| materialize(x, f.ty))
                    .collect(),
            )
        }
        Value::Unit | Value::Uninit | Value::Slice(..) => {
            unreachable!("not a constant's value: {v:?}")
        }
    };
    TExpr { kind, ty }
}

/// How many scalars `v` holds.
pub(super) fn scalars(v: &Value) -> u64 {
    match v {
        Value::Array(xs) | Value::Struct(xs) | Value::Variant(_, xs) => {
            xs.iter().map(scalars).sum()
        }
        Value::Slice(xs, s, n) => xs[*s..s + n].iter().map(scalars).sum(),
        _ => 1,
    }
}
