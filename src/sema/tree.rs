//! The typed tree: the checker's output and the lowering pass's input.
//!
//! Every operation in it is already known to be safe: the checker rejects
//! arithmetic, division, shifts and conversions it can't prove, so lowering
//! never needs a run-time check. That includes indexing: every
//! [`TExprKind::Index`] is proven to be in bounds.

pub use crate::ast::Convention;
use crate::source::Span;
use crate::types::Ty;

pub type LocalId = usize;
pub type FuncId = usize;

/// A checked program: the functions of every package, flattened.
#[derive(Debug)]
pub struct Program {
    pub funcs: Vec<Func>,
    /// The contents of every string literal, indexed by [`TExprKind::Str`].
    pub strings: Vec<Vec<u8>>,
    /// Every array constant, indexed by [`TExprKind::Table`].
    pub tables: Vec<Table>,
    /// The root package's `main` function, if it has one.
    pub main: Option<FuncId>,
    /// The path of every package, by index (`std/io`), for the symbols of
    /// generic instances.
    pub packages: Vec<String>,
    /// Warnings about the program (it has no errors). They don't stop it
    /// from compiling.
    pub warnings: Vec<crate::diag::Diagnostic>,
}

/// An array constant (`const DAYS: [12]u8 = [31, 28, ...]`), placed in
/// read-only data.
#[derive(Debug)]
pub struct Table {
    /// The constant's name, for messages.
    pub name: String,
    /// An array type, of integers or `bool`, or of arrays of them.
    pub ty: Ty,
    /// The scalars, in memory order (row by row); `bool` as 0 or 1.
    pub values: Vec<i128>,
}

#[derive(Clone, Debug)]
pub struct Func {
    pub name: String,
    /// The linker symbol: `<package path>.<name>`, e.g. `std/io.print`. An
    /// instance of a generic function adds its type arguments:
    /// `std/math.max[u32]`.
    pub symbol: String,
    /// The generic parameters of a generic function ([`Ty::Param`]s: types
    /// and values), which its types mention; for a method of a generic
    /// type, the type's first. Empty for a function that isn't generic.
    /// Only instances of it, made by `crate::mono`, are lowered.
    pub type_params: Vec<Ty>,
    /// For a method of a generic type, how many of `type_params` are the
    /// type's (they come first): the symbol puts their arguments after the
    /// type's name, `std/buf.StackBuf[64].push`.
    pub owner_params: usize,
    /// The locals holding the value parameters among `type_params`, which
    /// an instance assigns first.
    pub value_params: Vec<(Ty, LocalId)>,
    pub params: Vec<LocalId>,
    /// The type of the value it returns (`T` in `throws(E) -> T`).
    pub ret: Ty,
    /// The error type of a function that throws.
    pub throws: Option<Ty>,
    pub locals: Vec<Local>,
    pub body: Vec<TStmt>,
    pub span: Span,
}

impl Func {
    /// What a call returns: `ret`, or for a function that throws, the
    /// result `throws(E) -> ret`, which holds the value or the error.
    pub fn result_ty(&self) -> Ty {
        match self.throws {
            Some(err) => Ty::result(self.ret, err),
            None => self.ret,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Local {
    pub name: String,
    pub ty: Ty,
    /// Whether it can be assigned: a `var`, or an `inout`, `sink` or `set`
    /// parameter (but not an `inout` slice, whose elements are what can
    /// be assigned).
    pub mutable: bool,
    /// For a parameter, how it's passed (docs/memory.md).
    pub convention: Option<Convention>,
}

impl Local {
    /// Whether this is a slice whose elements can be assigned: an `inout`
    /// slice parameter.
    pub fn mutable_view(&self) -> bool {
        self.ty.is_view() && self.convention == Some(Convention::Inout)
    }

    /// Whether the parameter is passed as the address of the caller's
    /// place, which the callee reads and writes in place.
    pub fn by_ref(&self) -> bool {
        matches!(self.convention, Some(Convention::Inout | Convention::Set))
    }
}

#[derive(Clone, Debug)]
pub enum TStmt {
    /// Initialize a local.
    Init(LocalId, TExpr),
    Assign(LocalId, TExpr),
    /// `place = value`, where `place` is an [`TExprKind::Index`] or a
    /// [`TExprKind::Field`] of a `var` array or struct (possibly nested, as
    /// in `a[i].x`).
    Store(TExpr, TExpr),
    Expr(TExpr),
    Return(Option<TExpr>),
    If(TExpr, Vec<TStmt>, Vec<TStmt>),
    While(TExpr, Vec<TStmt>),
    Loop(Vec<TStmt>),
    /// `for var in start..end`: `start` and `end` are evaluated once, then
    /// the body runs with `var` set to each value from `start` up to, but not
    /// including, `end`. `continue` moves on to the next value.
    For {
        var: LocalId,
        start: TExpr,
        end: TExpr,
        body: Vec<TStmt>,
    },
    Break,
    Continue,
    /// A nested block (an `unsafe` block).
    Block(Vec<TStmt>),
    /// `match value { ... }` on an enum or an optional. `value` is a local
    /// (the checker copies anything else into a hidden one first), so arms
    /// can read its payload with [`TExprKind::Payload`]. Every variant is
    /// in exactly one arm.
    Match {
        value: TExpr,
        arms: Vec<TArm>,
    },
    /// `throw value`: leave the function with the error `value`, of the
    /// function's error type.
    Throw(TExpr),
    /// `defer` (or `errdefer`, with `on_error`): `body` runs when control
    /// leaves the enclosing statement list, in reverse order of the
    /// `defer`s, or only when it leaves the function with an error. The
    /// body never leaves itself: no `return`, `throw` or `try`, and its
    /// `break` and `continue` stay in its own loops.
    Defer {
        body: Vec<TStmt>,
        on_error: bool,
    },
}

/// One arm of a [`TStmt::Match`]: the variants it handles (by index) and
/// its body, which starts by binding the payload fields it names.
#[derive(Clone, Debug)]
pub struct TArm {
    pub variants: Vec<u32>,
    pub body: Vec<TStmt>,
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
    /// A string literal, by index into [`Program::strings`].
    Str(usize),
    /// An array constant, by index into [`Program::tables`]: a value in
    /// read-only memory, never a place that can be changed.
    Table(usize),
    Local(LocalId),
    Call(FuncId, Vec<TExpr>),
    /// A call of a generic function (or a method of a generic type), with
    /// its generic arguments (a [`Ty::Value`] for a value parameter), which
    /// may mention the caller's own parameters. `crate::mono` turns it into
    /// a [`TExprKind::Call`] of an instance.
    GenericCall(FuncId, Vec<Ty>, Vec<TExpr>),
    /// `a.cmp(b)` of two values of an `Ordered` type (an integer or
    /// `bool`, once instantiated): the `Ordering` of `a` to `b`.
    Compare(Box<TExpr>, Box<TExpr>),
    Unary(TUnOp, Box<TExpr>),
    Binary(TBinOp, Box<TExpr>, Box<TExpr>),
    /// Short-circuit `&&`.
    And(Box<TExpr>, Box<TExpr>),
    /// Short-circuit `||`.
    Or(Box<TExpr>, Box<TExpr>),
    /// An integer conversion to `ty`, proven not to lose information.
    Convert(Box<TExpr>),
    /// `s.len` of a view (a `str` or a slice).
    ViewLen(Box<TExpr>),
    /// `a.len` of an array: the constant length of its type. The array is
    /// still evaluated, for any calls in it.
    ArrayLen(Box<TExpr>),
    /// `[a, b, c]`, of type `[N]T`.
    ArrayLit(Vec<TExpr>),
    /// `[value; N]`, `N` being the length of its array type; `value` is
    /// evaluated once.
    ArrayRepeat(Box<TExpr>),
    /// `base[index]` of an array or slice, with the index proven to be in
    /// bounds. An array-typed element is a place, like any array value.
    Index(Box<TExpr>, Box<TExpr>),
    /// `base[start..end]` of a view (an array is a [`TExprKind::ToSlice`]
    /// of it), with `0 <= start <= end <= base.len` proven. A missing start
    /// is 0, a missing end the base's length. A view of the same storage,
    /// `end - start` elements from `start` on. The bounds are integers of
    /// any type, evaluated after the base.
    Slice(Box<TExpr>, Option<Box<TExpr>>, Option<Box<TExpr>>),
    /// `T{name: value, ...}`: a struct literal. Every field is given exactly
    /// once; the values are in source order (the order they're evaluated
    /// in), each with its field's index in the declaration.
    StructLit(Vec<(u32, TExpr)>),
    /// `base.name`: field number `n` (in declaration order) of a struct. Like
    /// an element, a field that's an array or a struct is a place.
    Field(Box<TExpr>, u32),
    /// An array viewed as a slice of all its elements.
    ToSlice(Box<TExpr>),
    /// `s.ptr` of a `str` or a slice (unsafe). For an array, `a.ptr` is this
    /// over a [`TExprKind::ToSlice`] of it.
    StrPtr(Box<TExpr>),
    /// `s.bytes()`: the bytes of a `str`, as a `[]u8` view of the same
    /// storage (read-only, like every slice that isn't `inout`).
    Bytes(Box<TExpr>),
    /// `p + n`: a pointer moved forward by `n` elements (unsafe).
    PtrAdd(Box<TExpr>, Box<TExpr>),
    /// The `syscall(nr, args...)` intrinsic (unsafe). Integer operands are
    /// passed as 64-bit values, sign- or zero-extended by their type.
    Syscall(Vec<TExpr>),
    /// A value of an enum or an optional: variant number `n` (in
    /// declaration order; for an optional, 0 is `none` and 1 is `some`) and
    /// its payload fields, in order (the order they're evaluated in).
    Variant(u32, Vec<TExpr>),
    /// `base`'s payload field `field` of variant `variant`, which `base` is
    /// known to hold (it's read in the arm of a `match` for that variant).
    /// A place, like a struct field.
    Payload(Box<TExpr>, u32, u32),
    /// `opt ?? default`: the value in the optional `opt`, or else `default`,
    /// which is only evaluated when `opt` is `none`.
    Coalesce(Box<TExpr>, Box<TExpr>),
    /// The integer value of a C-style enum value (of the enum's tag type).
    EnumValue(Box<TExpr>),
    /// The C-style enum value whose value is the integer operand, as an
    /// optional of the enum: `none` if no variant has that value.
    EnumFrom(Box<TExpr>),
    /// `try call`: the value of `call` (a [`TExprKind::Call`] of a result
    /// type), or, if it failed, leave the function with its error (of the
    /// same type as the function's).
    Try(Box<TExpr>),
    /// `call catch ...`: the value of `call` (a [`TExprKind::Call`] of a
    /// result type), or, if it failed, the handler's. The error is stored
    /// in `binding` first, if there's one.
    Catch {
        call: Box<TExpr>,
        binding: Option<LocalId>,
        handler: Handler,
    },
    /// `throw value`, as the default of `??`: leave the function with an
    /// error. It has no value of its own.
    Throw(Box<TExpr>),
    /// `&place`, a call argument passed `inout` or `set`: the address of
    /// a place of a `var` (or of a parameter the callee may change), which
    /// is a [`TExprKind::Local`], [`TExprKind::Field`] or
    /// [`TExprKind::Index`], or a [`TExprKind::ToSlice`] of one for an
    /// `inout` slice, or a [`TExprKind::Slice`] of an array or `inout`
    /// slice. Of the place's type.
    Ref(Box<TExpr>),
    /// A call to a `never` function (a [`TExprKind::Call`] of type
    /// [`Ty::Never`]) where a value of another type is expected, as in
    /// `opt ?? fail()`. The call doesn't return, so there's never a value.
    Never(Box<TExpr>),
    /// An operation whose proof obligation (overflow, an index in bounds,
    /// a lossless conversion...) wasn't proven, in code that only runs at
    /// compile time: a constant's value or an `if comptime` condition. The
    /// evaluator checks it as it runs, and a failure is an error at the
    /// span (docs/generics.md, Proof obligations in compile-time code).
    /// Never lowered.
    Unproven(Span, Box<TExpr>),
}

/// What a [`TExprKind::Catch`] does with an error.
#[derive(Clone, Debug)]
pub enum Handler {
    /// A fallback value, of the call's value type.
    Value(Box<TExpr>),
    /// A block. When the `catch` has a value (it's not a statement on its
    /// own), the block always leaves.
    Block(Vec<TStmt>),
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

/// The expressions a statement evaluates itself (not those of the
/// statements nested in it).
pub fn stmt_exprs(s: &TStmt) -> Vec<&TExpr> {
    match s {
        TStmt::Init(_, e)
        | TStmt::Assign(_, e)
        | TStmt::Expr(e)
        | TStmt::Throw(e)
        | TStmt::If(e, ..)
        | TStmt::While(e, _)
        | TStmt::Match { value: e, .. } => vec![e],
        TStmt::Store(place, e) => vec![place, e],
        TStmt::Return(e) => e.iter().collect(),
        TStmt::For { start, end, .. } => vec![start, end],
        TStmt::Loop(_) | TStmt::Break | TStmt::Continue | TStmt::Block(_) | TStmt::Defer { .. } => {
            Vec::new()
        }
    }
}

/// The subexpressions of an expression (not itself, and not those in the
/// blocks of a `catch`).
pub fn subexprs(e: &TExpr) -> Vec<&TExpr> {
    match &e.kind {
        TExprKind::Int(_)
        | TExprKind::Bool(_)
        | TExprKind::Str(_)
        | TExprKind::Table(_)
        | TExprKind::Local(_) => Vec::new(),
        TExprKind::Call(_, items)
        | TExprKind::GenericCall(_, _, items)
        | TExprKind::ArrayLit(items)
        | TExprKind::Syscall(items)
        | TExprKind::Variant(_, items) => items.iter().collect(),
        TExprKind::Binary(_, l, r)
        | TExprKind::And(l, r)
        | TExprKind::Or(l, r)
        | TExprKind::Index(l, r)
        | TExprKind::Compare(l, r)
        | TExprKind::PtrAdd(l, r)
        | TExprKind::Coalesce(l, r) => vec![l, r],
        TExprKind::StructLit(fields) => fields.iter().map(|(_, v)| v).collect(),
        TExprKind::Slice(base, start, end) => std::iter::once(&**base)
            .chain(start.as_deref())
            .chain(end.as_deref())
            .collect(),
        TExprKind::Unary(_, inner)
        | TExprKind::Field(inner, _)
        | TExprKind::Convert(inner)
        | TExprKind::ViewLen(inner)
        | TExprKind::ArrayLen(inner)
        | TExprKind::ArrayRepeat(inner)
        | TExprKind::ToSlice(inner)
        | TExprKind::StrPtr(inner)
        | TExprKind::Bytes(inner)
        | TExprKind::Payload(inner, ..)
        | TExprKind::EnumValue(inner)
        | TExprKind::EnumFrom(inner)
        | TExprKind::Try(inner)
        | TExprKind::Throw(inner)
        | TExprKind::Ref(inner)
        | TExprKind::Never(inner)
        | TExprKind::Unproven(_, inner) => vec![inner],
        TExprKind::Catch { call, handler, .. } => match handler {
            Handler::Value(v) => vec![call, v],
            Handler::Block(_) => vec![call],
        },
    }
}

/// [`stmt_exprs`], mutably.
pub fn stmt_exprs_mut(s: &mut TStmt) -> Vec<&mut TExpr> {
    match s {
        TStmt::Init(_, e)
        | TStmt::Assign(_, e)
        | TStmt::Expr(e)
        | TStmt::Throw(e)
        | TStmt::If(e, ..)
        | TStmt::While(e, _)
        | TStmt::Match { value: e, .. } => vec![e],
        TStmt::Store(place, e) => vec![place, e],
        TStmt::Return(e) => e.iter_mut().collect(),
        TStmt::For { start, end, .. } => vec![start, end],
        TStmt::Loop(_) | TStmt::Break | TStmt::Continue | TStmt::Block(_) | TStmt::Defer { .. } => {
            Vec::new()
        }
    }
}

/// The statement lists nested in a statement: its branches, bodies and
/// arms (not the blocks of the `catch`es in its expressions).
pub fn stmt_blocks_mut(s: &mut TStmt) -> Vec<&mut Vec<TStmt>> {
    match s {
        TStmt::If(_, then, otherwise) => vec![then, otherwise],
        TStmt::While(_, body)
        | TStmt::For { body, .. }
        | TStmt::Loop(body)
        | TStmt::Block(body)
        | TStmt::Defer { body, .. } => vec![body],
        TStmt::Match { arms, .. } => arms.iter_mut().map(|a| &mut a.body).collect(),
        TStmt::Init(..)
        | TStmt::Assign(..)
        | TStmt::Store(..)
        | TStmt::Expr(_)
        | TStmt::Return(_)
        | TStmt::Throw(_)
        | TStmt::Break
        | TStmt::Continue => Vec::new(),
    }
}

/// [`subexprs`], mutably.
pub fn subexprs_mut(e: &mut TExpr) -> Vec<&mut TExpr> {
    match &mut e.kind {
        TExprKind::Int(_)
        | TExprKind::Bool(_)
        | TExprKind::Str(_)
        | TExprKind::Table(_)
        | TExprKind::Local(_) => Vec::new(),
        TExprKind::Call(_, items)
        | TExprKind::GenericCall(_, _, items)
        | TExprKind::ArrayLit(items)
        | TExprKind::Syscall(items)
        | TExprKind::Variant(_, items) => items.iter_mut().collect(),
        TExprKind::Binary(_, l, r)
        | TExprKind::And(l, r)
        | TExprKind::Or(l, r)
        | TExprKind::Index(l, r)
        | TExprKind::Compare(l, r)
        | TExprKind::PtrAdd(l, r)
        | TExprKind::Coalesce(l, r) => vec![l, r],
        TExprKind::StructLit(fields) => fields.iter_mut().map(|(_, v)| v).collect(),
        TExprKind::Slice(base, start, end) => std::iter::once(&mut **base)
            .chain(start.as_deref_mut())
            .chain(end.as_deref_mut())
            .collect(),
        TExprKind::Unary(_, inner)
        | TExprKind::Field(inner, _)
        | TExprKind::Convert(inner)
        | TExprKind::ViewLen(inner)
        | TExprKind::ArrayLen(inner)
        | TExprKind::ArrayRepeat(inner)
        | TExprKind::ToSlice(inner)
        | TExprKind::StrPtr(inner)
        | TExprKind::Bytes(inner)
        | TExprKind::Payload(inner, ..)
        | TExprKind::EnumValue(inner)
        | TExprKind::EnumFrom(inner)
        | TExprKind::Try(inner)
        | TExprKind::Throw(inner)
        | TExprKind::Ref(inner)
        | TExprKind::Never(inner)
        | TExprKind::Unproven(_, inner) => vec![inner],
        TExprKind::Catch { call, handler, .. } => match handler {
            Handler::Value(v) => vec![call, v],
            Handler::Block(_) => vec![call],
        },
    }
}

/// The blocks of the `catch`es in an expression, at any depth.
pub fn expr_blocks<'a>(e: &'a TExpr, out: &mut Vec<&'a [TStmt]>) {
    if let TExprKind::Catch {
        handler: Handler::Block(b),
        ..
    } = &e.kind
    {
        out.push(b);
    }
    for sub in subexprs(e) {
        expr_blocks(sub, out);
    }
}

/// The blocks of the `catch`es in the expressions statement `s` evaluates
/// itself.
fn stmt_blocks(s: &TStmt) -> Vec<&[TStmt]> {
    let mut out = Vec::new();
    for e in stmt_exprs(s) {
        expr_blocks(e, &mut out);
    }
    out
}

/// Whether evaluating `e` always calls a `never` function: `e` is such a
/// call, or one of the subexpressions always evaluated with it is (not the
/// right side of `&&`, `||` or `??`, nor a `catch` handler, which may not
/// run).
pub fn expr_diverges(e: &TExpr) -> bool {
    if e.ty == Ty::Never {
        return true;
    }
    match &e.kind {
        TExprKind::And(l, _) | TExprKind::Or(l, _) | TExprKind::Coalesce(l, _) => expr_diverges(l),
        TExprKind::Catch { call, .. } => expr_diverges(call),
        _ => subexprs(e).into_iter().any(expr_diverges),
    }
}

/// Whether statement `s` always calls a `never` function in the
/// expressions it evaluates itself (a value, a condition, a bound): the
/// code after it can't be reached, as after a `return`.
fn stmt_calls_never(s: &TStmt) -> bool {
    stmt_exprs(s).into_iter().any(expr_diverges)
}

/// Whether control can't fall off the end of `stmts` (for "missing return").
pub fn terminates(stmts: &[TStmt]) -> bool {
    stmts.iter().any(|s| match s {
        _ if stmt_calls_never(s) => true,
        TStmt::Return(_) | TStmt::Throw(_) => true,
        TStmt::If(_, then, otherwise) => terminates(then) && terminates(otherwise),
        TStmt::Loop(body) => !breaks(body),
        TStmt::Block(body) => terminates(body),
        TStmt::Match { arms, .. } => arms.iter().all(|a| terminates(&a.body)),
        _ => false,
    })
}

/// Whether control can't reach the statement after `stmts`: every path ends
/// in `return`, `break` or `continue`, a call to a `never` function, or an
/// endless loop.
pub fn diverges(stmts: &[TStmt]) -> bool {
    stmts.iter().any(|s| match s {
        _ if stmt_calls_never(s) => true,
        TStmt::Return(_) | TStmt::Throw(_) | TStmt::Break | TStmt::Continue => true,
        TStmt::If(_, then, otherwise) => diverges(then) && diverges(otherwise),
        TStmt::Loop(body) => !breaks(body),
        TStmt::Block(body) => diverges(body),
        TStmt::Match { arms, .. } => arms.iter().all(|a| diverges(&a.body)),
        _ => false,
    })
}

/// Whether `stmts` contain a `break` that leaves the enclosing loop
/// (including one in the block of a `catch`, and in the condition or the
/// bounds of a nested loop, which are evaluated outside of it).
pub fn breaks(stmts: &[TStmt]) -> bool {
    stmts.iter().any(|s| {
        let nested = match s {
            TStmt::Break => true,
            TStmt::If(_, then, otherwise) => breaks(then) || breaks(otherwise),
            TStmt::Block(body) => breaks(body),
            TStmt::Match { arms, .. } => arms.iter().any(|a| breaks(&a.body)),
            _ => false,
        };
        nested || stmt_blocks(s).into_iter().any(breaks)
    })
}
