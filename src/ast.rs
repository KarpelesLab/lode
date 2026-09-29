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
}

#[derive(Debug)]
pub struct FnDecl {
    pub is_pub: bool,
    /// `unsafe fn`: callers must be in an `unsafe` context.
    pub is_unsafe: bool,
    pub name: Ident,
    pub params: Vec<Param>,
    pub ret: Option<TypeExpr>,
    pub body: Block,
    pub span: Span,
}

/// `const NAME: T = value` at package level.
#[derive(Debug)]
pub struct ConstDecl {
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
    pub convention: Convention,
    pub name: Ident,
    pub ty: TypeExpr,
}

#[derive(Clone, Debug)]
pub enum TypeExpr {
    /// A named type such as `u32` or `bool`.
    Named(Ident),
    /// `()`
    Unit(Span),
    /// A raw pointer `*T`.
    Ptr(Box<TypeExpr>, Span),
}

impl TypeExpr {
    pub fn span(&self) -> Span {
        match self {
            TypeExpr::Named(id) => id.span,
            TypeExpr::Unit(span) | TypeExpr::Ptr(_, span) => *span,
        }
    }
}

#[derive(Debug)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: Span,
}

#[derive(Debug)]
pub enum Stmt {
    /// `let x: T = e` (`mutable: false`) or `var x: T = e` (`mutable: true`).
    Let {
        mutable: bool,
        name: Ident,
        ty: Option<TypeExpr>,
        init: Option<Expr>,
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
    Break(Span),
    Continue(Span),
    /// `unsafe { ... }`
    Unsafe(Block),
}

#[derive(Debug)]
pub struct IfStmt {
    pub cond: Expr,
    pub then: Block,
    pub otherwise: Option<Else>,
    pub span: Span,
}

#[derive(Debug)]
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
        }
    }
}
