//! The typed tree: the checker's output and the lowering pass's input.
//!
//! Every operation in it is already known to be safe: the checker rejects
//! arithmetic, division, shifts and conversions it can't prove, so lowering
//! never needs a run-time check. That includes indexing: every
//! [`TExprKind::Index`] is proven to be in bounds.

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
    /// The root package's `main` function, if it has one.
    pub main: Option<FuncId>,
}

#[derive(Debug)]
pub struct Func {
    pub name: String,
    /// The linker symbol: `<package path>.<name>`, e.g. `std/io.print`.
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
}

#[derive(Debug)]
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
    /// `s.len` of a view (a `str` or a slice).
    ViewLen(Box<TExpr>),
    /// `a.len` of an array: the constant length of its type. The array is
    /// still evaluated, for any calls in it.
    ArrayLen(Box<TExpr>),
    /// `[a, b, c]`, of type `[N]T`.
    ArrayLit(Vec<TExpr>),
    /// `[value; N]`; `value` is evaluated once.
    ArrayRepeat(Box<TExpr>, u64),
    /// `base[index]` of an array or slice, with the index proven to be in
    /// bounds. An array-typed element is a place, like any array value.
    Index(Box<TExpr>, Box<TExpr>),
    /// `T{name: value, ...}`: a struct literal. Every field is given exactly
    /// once; the values are in source order (the order they're evaluated
    /// in), each with its field's index in the declaration.
    StructLit(Vec<(u32, TExpr)>),
    /// `base.name`: field number `n` (in declaration order) of a struct. Like
    /// an element, a field that's an array or a struct is a place.
    Field(Box<TExpr>, u32),
    /// An array viewed as a slice of all its elements.
    ToSlice(Box<TExpr>),
    /// `s.ptr` of a `str` (unsafe).
    StrPtr(Box<TExpr>),
    /// `p + n`: a pointer moved forward by `n` elements (unsafe).
    PtrAdd(Box<TExpr>, Box<TExpr>),
    /// The `syscall(nr, args...)` intrinsic (unsafe). Integer operands are
    /// passed as 64-bit values, sign- or zero-extended by their type.
    Syscall(Vec<TExpr>),
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

/// Whether control can't fall off the end of `stmts` (for "missing return").
pub fn terminates(stmts: &[TStmt]) -> bool {
    stmts.iter().any(|s| match s {
        TStmt::Return(_) => true,
        TStmt::If(_, then, otherwise) => terminates(then) && terminates(otherwise),
        TStmt::Loop(body) => !breaks(body),
        TStmt::Block(body) => terminates(body),
        _ => false,
    })
}

/// Whether control can't reach the statement after `stmts`: every path ends
/// in `return`, `break` or `continue`, or an endless loop.
pub fn diverges(stmts: &[TStmt]) -> bool {
    stmts.iter().any(|s| match s {
        TStmt::Return(_) | TStmt::Break | TStmt::Continue => true,
        TStmt::If(_, then, otherwise) => diverges(then) && diverges(otherwise),
        TStmt::Loop(body) => !breaks(body),
        TStmt::Block(body) => diverges(body),
        _ => false,
    })
}

/// Whether `stmts` contain a `break` that leaves the enclosing loop.
pub fn breaks(stmts: &[TStmt]) -> bool {
    stmts.iter().any(|s| match s {
        TStmt::Break => true,
        TStmt::If(_, then, otherwise) => breaks(then) || breaks(otherwise),
        TStmt::Block(body) => breaks(body),
        _ => false,
    })
}
