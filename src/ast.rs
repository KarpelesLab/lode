//! The syntax tree produced by the parser.

use crate::source::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ident {
    pub name: String,
    pub span: Span,
}

/// One source file.
#[derive(Debug)]
pub struct File {
    pub id: crate::source::FileId,
    pub package: Option<Ident>,
    pub imports: Vec<Import>,
    pub items: Vec<Item>,
    /// The file's text, for errors that point into a string literal (set
    /// by `crate::load`; empty otherwise).
    pub source: String,
}

#[derive(Debug)]
pub struct Import {
    pub path: String,
    pub alias: Option<Ident>,
    pub span: Span,
}

#[derive(Debug)]
pub enum Item {
    Fn(FnDecl),
    Const(ConstDecl),
    Struct(StructDecl),
    Enum(EnumDecl),
    /// `if comptime cond { items } else { items }` at package level: the
    /// declarations of the branch `cond` picks for the target.
    If(ItemIf),
    /// `compile_error("message")` at package level: an error when the
    /// declarations around it are compiled (in a taken branch of an
    /// `if comptime`, or at all). The call expression.
    CompileError(Expr),
    /// `trait Name: Super { ... }`
    Trait(TraitDecl),
    /// `impl Trait for Type { ... }`
    Impl(ImplDecl),
}

/// A trait named in a bound or an `impl`: `Ordered`, or `io.Writer` for a
/// trait of another package.
#[derive(Clone, Debug)]
pub struct Bound {
    pub pkg: Option<Ident>,
    pub name: Ident,
}

impl Bound {
    pub fn span(&self) -> Span {
        match &self.pkg {
            Some(p) => p.span.to(self.name.span),
            None => self.name.span,
        }
    }

    /// How it's written: `Ordered`, `io.Writer`.
    pub fn text(&self) -> String {
        match &self.pkg {
            Some(p) => format!("{}.{}", p.name, self.name.name),
            None => self.name.name.clone(),
        }
    }
}

/// `trait Name: Super + Other { item ... }`, one item per line.
#[derive(Debug)]
pub struct TraitDecl {
    pub is_pub: bool,
    pub name: Ident,
    pub supers: Vec<Bound>,
    pub items: Vec<TraitItem>,
    pub span: Span,
}

/// An item of a trait.
#[derive(Debug)]
pub enum TraitItem {
    /// `fn name(self, ...) -> T`: a required method (or associated
    /// function, without `self`); with a body, a default one. Without a
    /// body, the declaration's body is empty and `default` is false.
    Method { decl: Box<FnDecl>, default: bool },
    /// `type Name: Bound + Other`: an associated type.
    Type { name: Ident, bounds: Vec<Bound> },
    /// `const NAME: T`: an associated constant.
    Const { name: Ident, ty: TypeExpr },
}

/// `impl[A: Bound] Trait for Type[A] { item ... }`.
#[derive(Debug)]
pub struct ImplDecl {
    /// The generic parameters: one per parameter of a generic type.
    pub generics: Vec<GenericParam>,
    pub trait_: Bound,
    pub ty: TypeExpr,
    pub items: Vec<ImplItem>,
    pub span: Span,
}

/// An item of an `impl`.
#[derive(Debug)]
pub enum ImplItem {
    Method(FnDecl),
    /// `type Name = T`.
    Type {
        name: Ident,
        ty: TypeExpr,
    },
    /// `const NAME: T = value`.
    Const(ConstDecl),
}

/// `if comptime cond { ... } else ...` at package level.
#[derive(Debug)]
pub struct ItemIf {
    pub cond: Expr,
    pub then: Vec<Item>,
    pub otherwise: Option<ItemElse>,
    pub span: Span,
}

/// The `else` of a package-level `if comptime`.
#[derive(Debug)]
pub enum ItemElse {
    If(Box<ItemIf>),
    Items(Vec<Item>),
}

/// `enum Name { variant ... }` or `enum Name: T { variant = value ... }`,
/// one variant per line.
#[derive(Debug)]
pub struct EnumDecl {
    pub is_pub: bool,
    pub name: Ident,
    /// The generic parameters of a generic enum, `[L, R]`.
    pub generics: Vec<GenericParam>,
    /// The integer type of a C-style enum, whose variants have values.
    pub tag: Option<TypeExpr>,
    pub variants: Vec<VariantDecl>,
    pub span: Span,
}

/// `name`, `name(field: T, ...)` or `name = value`.
#[derive(Debug)]
pub struct VariantDecl {
    pub name: Ident,
    /// The payload fields; `None` without parentheses.
    pub fields: Option<Vec<FieldDecl>>,
    pub value: Option<Expr>,
}

/// `struct Name { field: T ... }`, one field per line.
#[derive(Debug)]
pub struct StructDecl {
    pub is_pub: bool,
    pub name: Ident,
    /// The generic parameters of a generic struct, `[A, B]` or
    /// `[N: usize]`.
    pub generics: Vec<GenericParam>,
    pub fields: Vec<FieldDecl>,
    pub span: Span,
}

#[derive(Debug)]
pub struct FieldDecl {
    pub name: Ident,
    pub ty: TypeExpr,
}

#[derive(Debug)]
pub struct FnDecl {
    pub is_pub: bool,
    /// `unsafe fn`: callers must be in an `unsafe` context.
    pub is_unsafe: bool,
    /// For a method or an associated function, `fn Type.name(...)`: the
    /// type it belongs to (`Type`, or `pkg.Type`, which is an error).
    pub owner: Option<TypeExpr>,
    /// For a method of a generic type, the names it gives the type's
    /// parameters, with the bounds it adds: `[A, B]` in
    /// `fn Pair[A, B].swap`.
    pub owner_generics: Vec<GenericParam>,
    pub name: Ident,
    /// The generic parameters of a generic function (or the method's own),
    /// `[T: Ordered, U]`.
    pub generics: Vec<GenericParam>,
    /// The parameters. A method's first is `self`, whose type is the
    /// owner's.
    pub params: Vec<Param>,
    /// `throws(E)`, or `throws` alone (an inferred error set).
    pub throws: Option<Throws>,
    pub ret: Option<TypeExpr>,
    pub body: Block,
    pub span: Span,
}

/// A generic parameter, `T` or `T: Ordered + Copy`: its name and the
/// traits bounding it. A value parameter (`N: usize`) has its integer type
/// as its one bound.
#[derive(Debug)]
pub struct GenericParam {
    pub name: Ident,
    pub bounds: Vec<Bound>,
    /// `..A: Format`: a pack, any number of type parameters, each with the
    /// bounds (docs/generics.md, Format strings).
    pub pack: bool,
}

/// The `throws` clause of a function: `throws(E)` names the error type,
/// `throws` alone asks for it to be inferred.
#[derive(Debug)]
pub struct Throws {
    pub ty: Option<TypeExpr>,
    pub span: Span,
}

/// `const NAME: T = value` at package level.
#[derive(Debug)]
pub struct ConstDecl {
    /// `@comptime_budget(n)` on the line before: the most steps evaluating
    /// the value may take, instead of the default.
    pub budget: Option<Expr>,
    pub is_pub: bool,
    pub name: Ident,
    /// `None` for an untyped constant, which adapts to its context like a literal.
    pub ty: Option<TypeExpr>,
    pub value: Expr,
    pub span: Span,
}

/// Parameter passing conventions (docs/memory.md).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Convention {
    /// Read-only access for the duration of the call (the default).
    Let,
    Inout,
    Sink,
    Set,
}

#[derive(Debug)]
pub struct Param {
    /// `comptime name: T`: the argument is known when compiling, and each
    /// value gives the function an expansion of its own.
    pub comptime: bool,
    pub convention: Convention,
    pub name: Ident,
    pub ty: TypeExpr,
}

impl Param {
    /// Whether this is a method's `self` (its type is the method's owner).
    pub fn is_self(&self) -> bool {
        self.name.name == "self"
    }
}

#[derive(Clone, Debug)]
pub enum TypeExpr {
    /// A named type such as `u32`, `bool` or `Point`.
    Named(Ident),
    /// A type of another package: `pkg.Name`.
    Qualified(Ident, Ident),
    /// `()`
    Unit(Span),
    /// A raw pointer `*T`.
    Ptr(Box<TypeExpr>, Span),
    /// A fixed-size array `[N]T`; `N` must be a constant.
    Array(Box<Expr>, Box<TypeExpr>, Span),
    /// A slice `[]T`.
    Slice(Box<TypeExpr>, Span),
    /// An optional `?T`.
    Optional(Box<TypeExpr>, Span),
    /// A generic type with its arguments: `Pair[u8, bool]`,
    /// `StackBuf[64]`. The base is a [`TypeExpr::Named`] or a
    /// [`TypeExpr::Qualified`]; an argument is a type, or a value for a
    /// value parameter.
    Generic(Box<TypeExpr>, Vec<TypeArg>, Span),
    /// `..A`: the type of a pack parameter, `args: ..A`, where `A` is a
    /// pack of type parameters.
    Pack(Ident, Span),
}

impl TypeExpr {
    pub fn span(&self) -> Span {
        match self {
            TypeExpr::Named(id) => id.span,
            TypeExpr::Qualified(pkg, name) => pkg.span.to(name.span),
            TypeExpr::Unit(span)
            | TypeExpr::Ptr(_, span)
            | TypeExpr::Array(_, _, span)
            | TypeExpr::Slice(_, span)
            | TypeExpr::Optional(_, span)
            | TypeExpr::Generic(_, _, span)
            | TypeExpr::Pack(_, span) => *span,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum Stmt {
    /// `let x: T = e` (`mutable: false`) or `var x: T = e` (`mutable: true`).
    /// With `otherwise`, `let x = opt else { ... }`: `e` is an optional, and
    /// the block runs (and must leave) when it's `none`.
    Let {
        mutable: bool,
        name: Ident,
        ty: Option<TypeExpr>,
        init: Option<Expr>,
        otherwise: Option<Block>,
        span: Span,
    },
    /// `comptime let x: T = e`: a value computed when compiling.
    ComptimeLet {
        name: Ident,
        ty: Option<TypeExpr>,
        init: Expr,
        span: Span,
    },
    /// `target = value`, or `target op= value` when `op` is set.
    Assign {
        target: Expr,
        op: Option<BinOp>,
        value: Expr,
        span: Span,
    },
    Expr(Expr),
    Return {
        value: Option<Expr>,
        span: Span,
    },
    If(IfStmt),
    While {
        cond: Expr,
        body: Block,
        span: Span,
    },
    Loop {
        body: Block,
        span: Span,
    },
    /// `for var in iter { ... }`; with `comptime`, `comptime for`: the
    /// body is repeated for each element of a list known when compiling,
    /// with `var` known too.
    For {
        comptime: bool,
        var: Ident,
        iter: ForIter,
        body: Block,
        span: Span,
    },
    Break(Span),
    Continue(Span),
    /// `unsafe { ... }`
    Unsafe(Block),
    /// `match value { pattern => body ... }`; with `comptime`, `match
    /// comptime value`: the value is known when compiling, and only the
    /// arm it picks is checked.
    Match {
        comptime: bool,
        value: Expr,
        arms: Vec<Arm>,
        span: Span,
    },
    /// `throw value`: leave the function with the error `value`.
    Throw {
        value: Expr,
        span: Span,
    },
    /// `defer { ... }` (or `defer` and one statement): run the block when
    /// leaving the enclosing block. With `on_error` (`errdefer`), only when
    /// leaving the function with an error.
    Defer {
        body: Block,
        on_error: bool,
        span: Span,
    },
}

impl Stmt {
    /// The statement's span.
    pub fn span(&self) -> Span {
        match self {
            Stmt::Let { span, .. }
            | Stmt::ComptimeLet { span, .. }
            | Stmt::Assign { span, .. }
            | Stmt::Return { span, .. }
            | Stmt::While { span, .. }
            | Stmt::Loop { span, .. }
            | Stmt::For { span, .. }
            | Stmt::Break(span)
            | Stmt::Continue(span)
            | Stmt::Match { span, .. }
            | Stmt::Throw { span, .. }
            | Stmt::Defer { span, .. } => *span,
            Stmt::Expr(e) => e.span,
            Stmt::If(i) => i.span,
            Stmt::Unsafe(b) => b.span,
        }
    }
}

/// `pattern => body` in a `match`. A body written as a single statement is
/// a block of that statement.
#[derive(Clone, Debug)]
pub struct Arm {
    pub pattern: Pattern,
    pub body: Block,
}

#[derive(Clone, Debug)]
pub enum Pattern {
    /// `_`: every variant not matched by an earlier arm.
    Wildcard(Span),
    /// `name` or `name(a, _, c)`: a variant, binding its payload fields by
    /// position (`_` skips one).
    Variant {
        name: Ident,
        bindings: Option<Vec<Ident>>,
        span: Span,
    },
    /// A value known when compiling, matched against an integer or a
    /// `bool`: `3`, `-1`, `'a'`, `true`, `pkg.MAX`. A bare name (`MAX`) is
    /// parsed as a [`Pattern::Variant`]; against an integer, it names a
    /// constant.
    Value(Expr),
    /// `lo..=hi`: the integers from `lo` to `hi`, both included.
    Range(Expr, Expr, Span),
    /// `a | b | c`: any of the alternatives.
    Or(Vec<Pattern>, Span),
}

impl Pattern {
    pub fn span(&self) -> Span {
        match self {
            Pattern::Wildcard(span)
            | Pattern::Variant { span, .. }
            | Pattern::Range(_, _, span)
            | Pattern::Or(_, span) => *span,
            Pattern::Value(e) => e.span,
        }
    }

    /// The alternatives of the pattern: itself, or those of an `Or`.
    pub fn alternatives(&self) -> &[Pattern] {
        match self {
            Pattern::Or(alts, _) => alts,
            _ => std::slice::from_ref(self),
        }
    }
}

/// What a `for` loop goes over.
#[derive(Clone, Debug)]
pub enum ForIter {
    /// `a..b`: the integers from `a` up to, but not including, `b`.
    Range(Expr, Expr),
    /// The elements of an array or slice.
    Each(Expr),
}

#[derive(Clone, Debug)]
pub struct IfStmt {
    /// `if comptime cond`: `cond` is known when compiling, and only the
    /// branch it picks is checked.
    pub comptime: bool,
    /// `if let name = cond`: `cond` is an optional, and the `then` block
    /// runs with its value bound to `name` when it's not `none`.
    pub binding: Option<Ident>,
    pub cond: Expr,
    pub then: Block,
    pub otherwise: Option<Else>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum Else {
    If(Box<IfStmt>),
    Block(Block),
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Int(u128),
    Char(u32),
    Str(Vec<u8>),
    Bool(bool),
    Name(String),
    Unary(UnOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    Field(Box<Expr>, Ident),
    Paren(Box<Expr>),
    /// `[a, b, c]`
    ArrayLit(Vec<Expr>),
    /// `[value; count]`; the count must be a constant.
    ArrayRepeat(Box<Expr>, Box<Expr>),
    /// `base[index]`: an index, or a generic argument when `base` names a
    /// generic function (the checker decides).
    Index(Box<Expr>, Box<Expr>),
    /// `base[start..end]`, where either bound may be left out (`a[i..]`,
    /// `a[..j]`, `a[..]`).
    Slice(Box<Expr>, Option<Box<Expr>>, Option<Box<Expr>>),
    /// `base[a, b]`: brackets with several items, or with an item only a
    /// type can be (`?u8`, `[]u8`, `[4]u8`). The generic arguments of
    /// `base`, which must name a generic function.
    TypeArgs(Box<Expr>, Vec<TypeArg>),
    /// `Point{x: 1, y: 2}`: a struct literal, with its fields in source order.
    StructLit(TypeExpr, Vec<FieldInit>),
    /// `none`: the empty optional.
    None,
    /// `.name`: a variant of the enum the context expects (`.name(a, b)`
    /// is a call of it).
    Dot(Ident),
    /// `try call`: the call's value, or its error passed on to the caller.
    Try(Box<Expr>),
    /// `call catch e { ... }`, `call catch _ { ... }` or `call catch value`.
    Catch {
        value: Box<Expr>,
        /// The name the error is bound to in the block (`None` for `_`, and
        /// for a fallback value).
        binding: Option<Ident>,
        handler: CatchHandler,
    },
    /// `throw value` in an expression: only after `??`.
    Throw(Box<Expr>),
    /// `&place`: an argument passed `inout` or `set` (only in a call's
    /// arguments).
    Ref(Box<Expr>),
    /// `..args`: a pack passed on whole, as a call's last argument.
    Spread(Box<Expr>),
}

/// An item in the brackets of [`ExprKind::TypeArgs`]: a type, or an
/// expression that should name one (`u32`, `geo.Point`).
#[derive(Clone, Debug)]
pub enum TypeArg {
    Type(TypeExpr),
    Expr(Expr),
}

impl TypeArg {
    pub fn span(&self) -> Span {
        match self {
            TypeArg::Type(t) => t.span(),
            TypeArg::Expr(e) => e.span,
        }
    }
}

/// What a `catch` does with an error.
#[derive(Clone, Debug)]
pub enum CatchHandler {
    /// `catch e { ... }`: run a block.
    Block(Block),
    /// `catch value`: use a fallback value.
    Value(Box<Expr>),
}

/// `name: value` in a struct literal.
#[derive(Clone, Debug)]
pub struct FieldInit {
    pub name: Ident,
    pub value: Expr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
    BitNot,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    AddWrap,
    SubWrap,
    MulWrap,
    AddSat,
    SubSat,
    MulSat,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    ShlWrap,
    Shr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    /// `a ?? b`: the value of the optional `a`, or `b` if it's `none`.
    Coalesce,
}

impl BinOp {
    pub fn as_str(self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Rem => "%",
            BinOp::AddWrap => "+%",
            BinOp::SubWrap => "-%",
            BinOp::MulWrap => "*%",
            BinOp::AddSat => "+|",
            BinOp::SubSat => "-|",
            BinOp::MulSat => "*|",
            BinOp::BitAnd => "&",
            BinOp::BitOr => "|",
            BinOp::BitXor => "^",
            BinOp::Shl => "<<",
            BinOp::ShlWrap => "<<%",
            BinOp::Shr => ">>",
            BinOp::Eq => "==",
            BinOp::Ne => "!=",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::And => "&&",
            BinOp::Or => "||",
            BinOp::Coalesce => "??",
        }
    }
}
