//! The typed tree: the checker's output and the lowering pass's input.
//!
//! Every operation in it is already known to be safe: the checker rejects
//! arithmetic, division, shifts and conversions it can't prove, so lowering
//! never needs a run-time check. That includes indexing: every
//! [`TExprKind::Index`] is proven to be in bounds.

use std::collections::HashMap;

pub use crate::ast::Convention;
use crate::source::Span;
use crate::types::{Trait, Ty};

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
    /// Which function a call of a trait's method runs, by `Self`.
    pub dispatch: Dispatch,
    /// The `deinit` of each struct or enum that declares one (by its
    /// declared form, [`Ty::decl`]).
    pub deinits: HashMap<Ty, FuncId>,
    /// Every `static`, indexed by [`TExprKind::Static`].
    pub statics: Vec<Static>,
    /// What the compiler knows of `std/alloc`, if the program imports it.
    pub alloc: Option<AllocInfo>,
}

/// A `static`: a global initialized when compiling (docs/memory.md,
/// Globals).
#[derive(Clone, Debug)]
pub struct Static {
    /// Its linker symbol: `<package path>.<name>`.
    pub symbol: String,
    pub ty: Ty,
    /// Its initial value, a literal (as a constant's).
    pub init: TExpr,
}

/// The items of `std/alloc` the compiler implements the allocator context
/// with (docs/allocation.md, Lowering the context).
#[derive(Clone, Copy, Debug)]
pub struct AllocInfo {
    /// The `Allocator` trait.
    pub allocator: Trait,
    /// `alloc.Handle`: which allocator, and where. Its fields are the
    /// allocator's number among the program's allocator types and its
    /// address; when the program installs no allocator but the root, it
    /// has none (a handle is zero-sized).
    pub handle: Ty,
    /// The root allocator, a `static` (`alloc.ROOT`), and its type.
    pub root: usize,
    pub root_ty: Ty,
    /// `alloc.Box[T]` as declared, and its `into_inner`, which the
    /// destruction of a chain of boxes calls.
    pub boxed: Ty,
    pub into_inner: Option<FuncId>,
}

/// The methods declared in traits, and those each `impl` gives: what a call
/// of a trait's method runs once `Self` is known (see
/// [`Dispatch::resolve`]).
#[derive(Clone, Debug, Default)]
pub struct Dispatch {
    /// The functions declared in traits (with a default body or not): their
    /// trait and name.
    pub trait_fns: HashMap<FuncId, (Trait, String)>,
    /// The methods each `impl` declares, by trait and named type (in its
    /// declared form), by name.
    pub impls: HashMap<(Trait, Ty), HashMap<String, FuncId>>,
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
    /// Whether it's a function with `comptime` parameters or a pack, which
    /// is never lowered: its calls are to its expansions, each a function
    /// of its own (docs/generics.md, Format strings).
    pub template: bool,
    /// Whether it declares `uses alloc`: it gets the allocator in context
    /// (docs/allocation.md, Lowering the context).
    pub uses_alloc: bool,
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
    /// Whether it may be unassigned where it's destroyed or assigned: moved
    /// out of on some path, declared without a value, a `set` parameter, or
    /// a temporary. Lowering keeps a flag for it, when its type needs
    /// destruction, that says whether it holds a value (docs/allocation.md,
    /// Moves).
    pub drop_flag: bool,
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
    /// Where the statements after it come from, up to the next one: the
    /// checker puts one before each statement it checks. It does nothing;
    /// lowering uses it for debug information (`lode build -g`).
    Loc(Span),
    /// From here to the end of the enclosing statement list, `local` owns
    /// its value: it's destroyed at every exit of the list, like a `defer`
    /// registered here, unless it's unassigned there (moved out, or never
    /// assigned: its drop flag says). `init` says whether it's assigned
    /// here (just before); without it, it starts unassigned. Its type isn't
    /// `Copy`; for a type that needs no destruction it does nothing
    /// (docs/allocation.md, When destruction runs).
    Drop {
        local: LocalId,
        init: bool,
    },
    /// Destroy the value at a place now: a field of `self` in a `deinit`,
    /// the parts of a value in a destruction made by `crate::mono`, or a
    /// temporary at the end of its statement. A local with a drop flag is
    /// destroyed only if it holds a value, and is unassigned after.
    Destroy(TExpr),
    /// `with alloc = h { ... }`: the statements run with the handle in
    /// `local` (an `alloc.Handle`, assigned before) as the allocator in
    /// context.
    With(LocalId, Vec<TStmt>),
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
    /// The value of a place rooted at `local` (the local itself, or a field
    /// of it whose other fields need no destruction), moved out: the local
    /// is unassigned after it (its drop flag cleared), so it isn't
    /// destroyed (docs/allocation.md, Moves).
    Move(Box<TExpr>, LocalId),
    /// A value that isn't kept (a call's result passed to a read-only
    /// parameter, a field read from it, a statement's value): it's stored
    /// in the hidden local `local`, which the statement around it destroys
    /// at its end, or at an exit before. Of its value's type, which isn't
    /// `Copy`.
    Temp(LocalId, Box<TExpr>),
    /// A function of the standard library that the compiler implements
    /// (`@intrinsic`), with its arguments.
    Intrinsic(Intrinsic, Vec<TExpr>),
    /// `needs_deinit[T]()`: whether destroying a value of the type does
    /// anything (a `bool`), for a type that mentions type parameters;
    /// `crate::mono` makes it the literal of each instance.
    NeedsDeinit(Ty),
    /// `x.clone()` of a value of a type that's `Clone` without an `impl`
    /// of its own: the value read in place, copied (a `Copy` type), or
    /// cloned part by part. `crate::mono` makes it a copy or a call. Of a
    /// result type when cloning may fail (a type parameter's, or a part's
    /// clone that allocates): `throws(AllocError) -> T`.
    Clone(Box<TExpr>),
    /// A `static`, by index into [`Program::statics`]: a place in global
    /// memory (only in `unsafe` code).
    Static(usize),
    /// The value a pointer points to, as a place: `b.value` of a
    /// `Box[T]` (the pointer is its `ptr` field), and the allocators the
    /// compiler calls through a handle.
    Deref(Box<TExpr>),
    /// `size_of[T]()` (`false`) or `align_of[T]()` (`true`): a `usize`
    /// that the layout of each instance's `T` gives, when lowering.
    Layout(Ty, bool),
    /// An operation whose proof obligation (overflow, an index in bounds,
    /// a lossless conversion...) wasn't proven, in code that only runs at
    /// compile time: a constant's value or an `if comptime` condition. The
    /// evaluator checks it as it runs, and a failure is an error at the
    /// span (docs/generics.md, Proof obligations in compile-time code).
    /// Never lowered.
    Unproven(Span, Box<TExpr>),
    /// `Digit(x)`, a conversion to a named refinement (by its number) that
    /// wasn't proven, in code that only runs at compile time: the evaluator
    /// checks the refinement as it runs. Always inside a
    /// [`TExprKind::Unproven`]. Never lowered.
    Refined(Box<TExpr>, usize),
    /// `compile_error(message, values...)` or `compile_error_at(place,
    /// message, values...)` in code that only runs at compile time: an
    /// error when it's reached, of type `never`. It's reported at `place`
    /// when that's part of a string literal in the source, and otherwise at
    /// `span`. Never lowered.
    CompileError {
        place: Option<Box<TExpr>>,
        message: Box<TExpr>,
        values: Vec<TExpr>,
        span: Span,
    },
}

/// The functions the compiler implements (see [`TExprKind::Intrinsic`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Intrinsic {
    /// `mem.swap(&a, &b)`: exchange two places' values.
    Swap,
    /// `mem.forget(x)`: `x` is moved in, and never destroyed.
    Forget,
    /// `mem.take(&opt)`: the optional's value, leaving `none`.
    Take,
    /// `p.read()`: the value at the pointer, moved out (unsafe).
    PtrRead,
    /// `p.write(v)`: `v` moved to the pointer, without destroying what
    /// was there (unsafe).
    PtrWrite,
    /// `p.destroy()`: destroy the value at the pointer, in place (unsafe).
    PtrDestroy,
    /// `p.cast[U]()`: the same address, as a `*U` (unsafe).
    PtrCast,
    /// `p.addr()`: the address, a `usize`.
    PtrAddr,
    /// `mem.from_addr[T](a)`: the address `a`, as a `*T` (unsafe).
    FromAddr,
    /// `alloc.current()`: the handle of the allocator in context.
    AllocCurrent,
    /// `alloc.root()`: the handle of the root allocator.
    AllocRoot,
    /// `alloc.handle(a)`: a handle of the allocator `a` (unsafe).
    AllocHandle,
    /// `h.alloc(size, align)`, `h.resize(p, old, new, align)` and
    /// `h.free(p, size, align)` on an `alloc.Handle`: the method of the
    /// allocator it names (`crate::mono` makes them calls).
    HandleAlloc,
    HandleResize,
    HandleFree,
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
        TStmt::Destroy(place) => vec![place],
        TStmt::Loop(_)
        | TStmt::Break
        | TStmt::Continue
        | TStmt::Block(_)
        | TStmt::With(..)
        | TStmt::Defer { .. }
        | TStmt::Drop { .. }
        | TStmt::Loc(_) => Vec::new(),
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
        | TExprKind::NeedsDeinit(_)
        | TExprKind::Static(_)
        | TExprKind::Layout(..)
        | TExprKind::Local(_) => Vec::new(),
        TExprKind::Call(_, items)
        | TExprKind::GenericCall(_, _, items)
        | TExprKind::ArrayLit(items)
        | TExprKind::Syscall(items)
        | TExprKind::Intrinsic(_, items)
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
        | TExprKind::Move(inner, _)
        | TExprKind::Temp(_, inner)
        | TExprKind::Clone(inner)
        | TExprKind::Deref(inner)
        | TExprKind::Refined(inner, _)
        | TExprKind::Unproven(_, inner) => vec![inner],
        TExprKind::Catch { call, handler, .. } => match handler {
            Handler::Value(v) => vec![call, v],
            Handler::Block(_) => vec![call],
        },
        TExprKind::CompileError {
            place,
            message,
            values,
            ..
        } => place
            .as_deref()
            .into_iter()
            .chain(std::iter::once(&**message))
            .chain(values)
            .collect(),
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
        TStmt::Destroy(place) => vec![place],
        TStmt::Loop(_)
        | TStmt::Break
        | TStmt::Continue
        | TStmt::Block(_)
        | TStmt::With(..)
        | TStmt::Defer { .. }
        | TStmt::Drop { .. }
        | TStmt::Loc(_) => Vec::new(),
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
        | TStmt::With(_, body)
        | TStmt::Defer { body, .. } => vec![body],
        TStmt::Match { arms, .. } => arms.iter_mut().map(|a| &mut a.body).collect(),
        TStmt::Init(..)
        | TStmt::Assign(..)
        | TStmt::Store(..)
        | TStmt::Expr(_)
        | TStmt::Return(_)
        | TStmt::Throw(_)
        | TStmt::Break
        | TStmt::Continue
        | TStmt::Drop { .. }
        | TStmt::Destroy(_)
        | TStmt::Loc(_) => Vec::new(),
    }
}

/// [`subexprs`], mutably.
pub fn subexprs_mut(e: &mut TExpr) -> Vec<&mut TExpr> {
    match &mut e.kind {
        TExprKind::Int(_)
        | TExprKind::Bool(_)
        | TExprKind::Str(_)
        | TExprKind::Table(_)
        | TExprKind::NeedsDeinit(_)
        | TExprKind::Static(_)
        | TExprKind::Layout(..)
        | TExprKind::Local(_) => Vec::new(),
        TExprKind::Call(_, items)
        | TExprKind::GenericCall(_, _, items)
        | TExprKind::ArrayLit(items)
        | TExprKind::Syscall(items)
        | TExprKind::Intrinsic(_, items)
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
        | TExprKind::Move(inner, _)
        | TExprKind::Temp(_, inner)
        | TExprKind::Clone(inner)
        | TExprKind::Deref(inner)
        | TExprKind::Refined(inner, _)
        | TExprKind::Unproven(_, inner) => vec![inner],
        TExprKind::Catch { call, handler, .. } => match handler {
            Handler::Value(v) => vec![call, v],
            Handler::Block(_) => vec![call],
        },
        TExprKind::CompileError {
            place,
            message,
            values,
            ..
        } => place
            .as_deref_mut()
            .into_iter()
            .chain(std::iter::once(&mut **message))
            .chain(values)
            .collect(),
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
        TStmt::Block(body) | TStmt::With(_, body) => terminates(body),
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
        TStmt::Block(body) | TStmt::With(_, body) => diverges(body),
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
            TStmt::Block(body) | TStmt::With(_, body) => breaks(body),
            TStmt::Match { arms, .. } => arms.iter().any(|a| breaks(&a.body)),
            _ => false,
        };
        nested || stmt_blocks(s).into_iter().any(breaks)
    })
}
