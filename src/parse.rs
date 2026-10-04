//! The parser: tokens to [`ast::File`](crate::ast::File).
//!
//! Recursive descent for items and statements, precedence climbing for
//! expressions. On a syntax error the parser records a diagnostic and skips to
//! the end of the statement or item, so one run reports several errors.

use crate::ast::*;
use crate::diag::Diagnostic;
use crate::lex::{Kw, P, Tok, Token};
use crate::source::{FileId, Span};

/// Parse a token stream (as produced by [`crate::lex::lex`]) of source file `id`.
pub fn parse(toks: Vec<Token>, id: FileId) -> (File, Vec<Diagnostic>) {
    let mut p = Parser {
        toks,
        pos: 0,
        diags: Vec::new(),
        no_struct_lit: false,
    };
    let file = p.file(id);
    (file, p.diags)
}

/// A syntax error has been recorded; the caller should recover.
struct Failed;

type PResult<T> = Result<T, Failed>;

struct Parser {
    toks: Vec<Token>,
    pos: usize,
    diags: Vec<Diagnostic>,
    /// In the header of `if`, `while` and `for`, where a `{` after a name
    /// starts the block, as in Go: `if p == q {`. Parentheses and brackets
    /// allow struct literals again.
    no_struct_lit: bool,
}

/// Binary operator precedence, higher binds tighter.
fn binop_info(tok: &Tok) -> Option<(BinOp, u8)> {
    let Tok::P(p) = tok else { return None };
    Some(match p {
        P::OrOr => (BinOp::Or, 1),
        P::AndAnd => (BinOp::And, 2),
        P::EqEq => (BinOp::Eq, 3),
        P::NotEq => (BinOp::Ne, 3),
        P::Lt => (BinOp::Lt, 3),
        P::Le => (BinOp::Le, 3),
        P::Gt => (BinOp::Gt, 3),
        P::Ge => (BinOp::Ge, 3),
        P::Pipe => (BinOp::BitOr, 4),
        P::Caret => (BinOp::BitXor, 5),
        P::Amp => (BinOp::BitAnd, 6),
        P::Shl => (BinOp::Shl, 7),
        P::ShlWrap => (BinOp::ShlWrap, 7),
        P::Shr => (BinOp::Shr, 7),
        P::Plus => (BinOp::Add, 8),
        P::Minus => (BinOp::Sub, 8),
        P::AddWrap => (BinOp::AddWrap, 8),
        P::SubWrap => (BinOp::SubWrap, 8),
        P::AddSat => (BinOp::AddSat, 8),
        P::SubSat => (BinOp::SubSat, 8),
        P::Star => (BinOp::Mul, 9),
        P::Slash => (BinOp::Div, 9),
        P::Percent => (BinOp::Rem, 9),
        P::MulWrap => (BinOp::MulWrap, 9),
        P::MulSat => (BinOp::MulSat, 9),
        _ => return None,
    })
}

const COMPARISON: u8 = 3;

impl Parser {
    // --- token helpers ------------------------------------------------------

    fn peek(&self) -> &Tok {
        &self.toks[self.pos].tok
    }

    fn peek_at(&self, ahead: usize) -> &Tok {
        let i = (self.pos + ahead).min(self.toks.len() - 1);
        &self.toks[i].tok
    }

    fn span(&self) -> Span {
        self.toks[self.pos].span
    }

    fn prev_span(&self) -> Span {
        self.toks[self.pos.saturating_sub(1)].span
    }

    fn bump(&mut self) -> Token {
        let t = self.toks[self.pos].clone();
        if self.pos < self.toks.len() - 1 {
            self.pos += 1;
        }
        t
    }

    fn at_p(&self, p: P) -> bool {
        *self.peek() == Tok::P(p)
    }

    fn at_kw(&self, kw: Kw) -> bool {
        *self.peek() == Tok::Kw(kw)
    }

    fn eat_p(&mut self, p: P) -> bool {
        let found = self.at_p(p);
        if found {
            self.bump();
        }
        found
    }

    fn eat_kw(&mut self, kw: Kw) -> bool {
        let found = self.at_kw(kw);
        if found {
            self.bump();
        }
        found
    }

    fn skip_newlines(&mut self) {
        while matches!(self.peek(), Tok::Newline | Tok::P(P::Semi)) {
            self.bump();
        }
    }

    fn error<T>(&mut self, span: Span, msg: impl Into<String>) -> PResult<T> {
        self.diags.push(Diagnostic::error(span, msg));
        Err(Failed)
    }

    fn expected<T>(&mut self, what: &str) -> PResult<T> {
        let found = self.peek().clone();
        self.error(self.span(), format!("expected {what}, found {found}"))
    }

    fn expect_p(&mut self, p: P) -> PResult<Span> {
        if self.at_p(p) {
            Ok(self.bump().span)
        } else {
            self.expected(&format!("`{}`", p.as_str()))
        }
    }

    fn ident(&mut self, what: &str) -> PResult<Ident> {
        if let Tok::Ident(name) = self.peek() {
            let name = name.clone();
            let span = self.bump().span;
            Ok(Ident { name, span })
        } else {
            self.expected(what)
        }
    }

    /// Skip to the end of the current statement: a newline or `;` at bracket
    /// depth 0, or just before a `}` that closes the enclosing block.
    fn sync_statement(&mut self) {
        let mut depth = 0usize;
        loop {
            match self.peek() {
                Tok::Eof => return,
                Tok::Newline | Tok::P(P::Semi) if depth == 0 => return,
                Tok::P(P::RBrace) if depth == 0 => return,
                Tok::P(P::LBrace | P::LParen | P::LBracket) => depth += 1,
                Tok::P(P::RBrace | P::RParen | P::RBracket) => depth = depth.saturating_sub(1),
                _ => {}
            }
            self.bump();
        }
    }

    /// Skip to the start of the next top-level item.
    fn sync_item(&mut self) {
        let mut depth = 0usize;
        loop {
            match self.peek() {
                Tok::Eof => return,
                Tok::P(P::LBrace | P::LParen | P::LBracket) => depth += 1,
                Tok::P(P::RBrace | P::RParen | P::RBracket) => depth = depth.saturating_sub(1),
                Tok::Newline if depth == 0 => {
                    self.bump();
                    return;
                }
                _ => {}
            }
            self.bump();
        }
    }

    // --- items --------------------------------------------------------------

    fn file(&mut self, id: FileId) -> File {
        let mut file = File {
            id,
            package: None,
            imports: Vec::new(),
            items: Vec::new(),
        };
        self.skip_newlines();
        if self.eat_kw(Kw::Package) {
            match self.ident("a package name") {
                Ok(name) => file.package = Some(name),
                Err(Failed) => self.sync_item(),
            }
            self.skip_newlines();
        }
        while self.at_kw(Kw::Import) {
            match self.import() {
                Ok(import) => file.imports.push(import),
                Err(Failed) => self.sync_item(),
            }
            self.skip_newlines();
        }
        while *self.peek() != Tok::Eof {
            match self.item() {
                Ok(item) => file.items.push(item),
                Err(Failed) => self.sync_item(),
            }
            self.skip_newlines();
        }
        file
    }

    fn import(&mut self) -> PResult<Import> {
        let start = self.bump().span;
        let alias = if let Tok::Ident(_) = self.peek() {
            Some(self.ident("an alias")?)
        } else {
            None
        };
        let Tok::Str(bytes) = self.peek().clone() else {
            return self.expected("an import path string");
        };
        self.bump();
        let path = String::from_utf8(bytes).unwrap_or_default();
        Ok(Import {
            path,
            alias,
            span: start.to(self.prev_span()),
        })
    }

    fn item(&mut self) -> PResult<Item> {
        let start = self.span();
        let is_pub = self.eat_kw(Kw::Pub);
        match self.peek().clone() {
            Tok::Kw(Kw::Fn) => self.fn_decl(is_pub, false, start).map(Item::Fn),
            Tok::Kw(Kw::Unsafe) if *self.peek_at(1) == Tok::Kw(Kw::Fn) => {
                self.bump();
                self.fn_decl(is_pub, true, start).map(Item::Fn)
            }
            Tok::Kw(Kw::Const) => self.const_decl(is_pub, start).map(Item::Const),
            Tok::Kw(Kw::Struct) => self.struct_decl(is_pub, start).map(Item::Struct),
            Tok::Kw(
                kw @ (Kw::Enum
                | Kw::Trait
                | Kw::Impl
                | Kw::Type
                | Kw::Alias
                | Kw::Static
                | Kw::Unsafe),
            ) => self.error(
                self.span(),
                format!(
                    "`{}` declarations are not supported by the compiler yet",
                    kw.as_str()
                ),
            ),
            _ => self.expected("a declaration (like `fn`)"),
        }
    }

    fn const_decl(&mut self, is_pub: bool, start: Span) -> PResult<ConstDecl> {
        self.bump(); // const
        let name = self.ident("a constant name")?;
        let ty = if self.eat_p(P::Colon) {
            Some(self.type_expr()?)
        } else {
            None
        };
        self.expect_p(P::Eq)?;
        let value = self.expr()?;
        Ok(ConstDecl {
            is_pub,
            name,
            ty,
            span: start.to(value.span),
            value,
        })
    }

    fn struct_decl(&mut self, is_pub: bool, start: Span) -> PResult<StructDecl> {
        self.bump(); // struct
        let name = self.ident("a struct name")?;
        if self.at_p(P::LBracket) {
            return self.error(
                self.span(),
                "generic structs are not supported by the compiler yet",
            );
        }
        self.expect_p(P::LBrace)?;
        let mut fields = Vec::new();
        loop {
            self.skip_newlines();
            if self.at_p(P::RBrace) {
                break;
            }
            if self.at_kw(Kw::Pub) {
                return self.error(
                    self.span(),
                    "fields can't be marked `pub`: they're visible wherever the struct is",
                );
            }
            let field = self.ident("a field name or `}`")?;
            self.expect_p(P::Colon)?;
            let ty = self.type_expr()?;
            fields.push(FieldDecl { name: field, ty });
            if !matches!(self.peek(), Tok::Newline | Tok::P(P::Semi | P::RBrace)) {
                return self.expected("a new line after the field");
            }
        }
        let end = self.bump().span;
        Ok(StructDecl {
            is_pub,
            name,
            fields,
            span: start.to(end),
        })
    }

    fn fn_decl(&mut self, is_pub: bool, is_unsafe: bool, start: Span) -> PResult<FnDecl> {
        self.bump(); // fn
        let name = self.ident("a function name")?;
        if self.at_p(P::Dot) {
            return self.error(self.span(), "methods are not supported by the compiler yet");
        }
        if self.at_p(P::LBracket) {
            return self.error(
                self.span(),
                "generic functions are not supported by the compiler yet",
            );
        }
        self.expect_p(P::LParen)?;
        let mut params = Vec::new();
        loop {
            self.skip_newlines();
            if self.eat_p(P::RParen) {
                break;
            }
            params.push(self.param()?);
            self.skip_newlines();
            if !self.eat_p(P::Comma) {
                self.skip_newlines();
                self.expect_p(P::RParen)?;
                break;
            }
        }
        let ret = if self.eat_p(P::Arrow) {
            Some(self.type_expr()?)
        } else {
            None
        };
        for kw in [Kw::Throws, Kw::Uses, Kw::Where] {
            if self.at_kw(kw) {
                return self.error(
                    self.span(),
                    format!(
                        "`{}` clauses are not supported by the compiler yet",
                        kw.as_str()
                    ),
                );
            }
        }
        let body = self.block()?;
        Ok(FnDecl {
            is_pub,
            is_unsafe,
            name,
            params,
            ret,
            span: start.to(body.span),
            body,
        })
    }

    fn param(&mut self) -> PResult<Param> {
        let convention = if self.eat_kw(Kw::Inout) {
            Convention::Inout
        } else if self.eat_kw(Kw::Sink) {
            Convention::Sink
        } else if self.eat_kw(Kw::Set) {
            Convention::Set
        } else {
            Convention::Let
        };
        let name = self.ident("a parameter name")?;
        self.expect_p(P::Colon)?;
        let ty = self.type_expr()?;
        Ok(Param {
            convention,
            name,
            ty,
        })
    }

    fn type_expr(&mut self) -> PResult<TypeExpr> {
        match self.peek() {
            Tok::Ident(_) => {
                let name = self.ident("a type")?;
                if self.eat_p(P::Dot) {
                    let member = self.ident("a type name")?;
                    return Ok(TypeExpr::Qualified(name, member));
                }
                Ok(TypeExpr::Named(name))
            }
            Tok::P(P::LParen) if *self.peek_at(1) == Tok::P(P::RParen) => {
                let start = self.bump().span;
                let end = self.bump().span;
                Ok(TypeExpr::Unit(start.to(end)))
            }
            Tok::P(P::Star) => {
                let start = self.bump().span;
                let inner = self.type_expr()?;
                let span = start.to(inner.span());
                Ok(TypeExpr::Ptr(Box::new(inner), span))
            }
            Tok::P(P::LBracket) => {
                let start = self.bump().span;
                if self.eat_p(P::RBracket) {
                    let elem = self.type_expr()?;
                    let span = start.to(elem.span());
                    return Ok(TypeExpr::Slice(Box::new(elem), span));
                }
                let len = self.expr()?;
                self.expect_p(P::RBracket)?;
                let elem = self.type_expr()?;
                let span = start.to(elem.span());
                Ok(TypeExpr::Array(Box::new(len), Box::new(elem), span))
            }
            Tok::P(P::Question) => self.error(
                self.span(),
                "this kind of type is not supported by the compiler yet",
            ),
            _ => self.expected("a type"),
        }
    }

    // --- statements ---------------------------------------------------------

    fn block(&mut self) -> PResult<Block> {
        let start = self.expect_p(P::LBrace)?;
        let mut stmts = Vec::new();
        loop {
            self.skip_newlines();
            match self.peek() {
                Tok::P(P::RBrace) => break,
                Tok::Eof => return self.expected("`}`"),
                _ => {}
            }
            match self.stmt() {
                Ok(stmt) => {
                    stmts.push(stmt);
                    if !matches!(self.peek(), Tok::Newline | Tok::P(P::Semi | P::RBrace)) {
                        let _ = self.expected::<()>("end of line after the statement");
                        self.sync_statement();
                    }
                }
                Err(Failed) => self.sync_statement(),
            }
        }
        let end = self.bump().span;
        Ok(Block {
            stmts,
            span: start.to(end),
        })
    }

    fn stmt(&mut self) -> PResult<Stmt> {
        let start = self.span();
        match self.peek().clone() {
            Tok::Kw(kw @ (Kw::Let | Kw::Var)) => {
                self.bump();
                let name = self.ident("a variable name")?;
                let ty = if self.eat_p(P::Colon) {
                    Some(self.type_expr()?)
                } else {
                    None
                };
                let init = if self.eat_p(P::Eq) {
                    Some(self.expr()?)
                } else {
                    None
                };
                Ok(Stmt::Let {
                    mutable: kw == Kw::Var,
                    name,
                    ty,
                    init,
                    span: start.to(self.prev_span()),
                })
            }
            Tok::Kw(Kw::Return) => {
                self.bump();
                let value = if matches!(self.peek(), Tok::Newline | Tok::P(P::Semi | P::RBrace)) {
                    None
                } else {
                    Some(self.expr()?)
                };
                Ok(Stmt::Return {
                    value,
                    span: start.to(self.prev_span()),
                })
            }
            Tok::Kw(Kw::If) => Ok(Stmt::If(self.if_stmt()?)),
            Tok::Kw(Kw::While) => {
                self.bump();
                let cond = self.header_expr()?;
                let body = self.block()?;
                Ok(Stmt::While {
                    cond,
                    span: start.to(body.span),
                    body,
                })
            }
            Tok::Kw(Kw::Loop) => {
                self.bump();
                let body = self.block()?;
                Ok(Stmt::Loop {
                    span: start.to(body.span),
                    body,
                })
            }
            Tok::Kw(Kw::Unsafe) => {
                self.bump();
                Ok(Stmt::Unsafe(self.block()?))
            }
            Tok::Kw(Kw::Break) => Ok(Stmt::Break(self.bump().span)),
            Tok::Kw(Kw::Continue) => Ok(Stmt::Continue(self.bump().span)),
            Tok::Kw(Kw::For) => {
                self.bump();
                let var = self.ident("a loop variable name")?;
                if !self.eat_kw(Kw::In) {
                    return self.expected("`in`");
                }
                let first = self.header_expr()?;
                let iter = if self.eat_p(P::DotDot) {
                    ForIter::Range(first, self.header_expr()?)
                } else {
                    ForIter::Each(first)
                };
                let body = self.block()?;
                Ok(Stmt::For {
                    var,
                    iter,
                    span: start.to(body.span),
                    body,
                })
            }
            Tok::Kw(
                kw @ (Kw::Match | Kw::Defer | Kw::Errdefer | Kw::Throw | Kw::Scope | Kw::Comptime),
            ) => self.error(
                self.span(),
                format!("`{}` is not supported by the compiler yet", kw.as_str()),
            ),
            _ => {
                let target = self.expr()?;
                let op = match self.peek() {
                    Tok::P(P::Eq) => None,
                    Tok::P(P::AddAssign) => Some(BinOp::Add),
                    Tok::P(P::SubAssign) => Some(BinOp::Sub),
                    Tok::P(P::MulAssign) => Some(BinOp::Mul),
                    Tok::P(P::DivAssign) => Some(BinOp::Div),
                    Tok::P(P::RemAssign) => Some(BinOp::Rem),
                    Tok::P(P::ShlAssign) => Some(BinOp::Shl),
                    Tok::P(P::ShrAssign) => Some(BinOp::Shr),
                    _ => return Ok(Stmt::Expr(target)),
                };
                self.bump();
                let value = self.expr()?;
                Ok(Stmt::Assign {
                    span: target.span.to(value.span),
                    target,
                    op,
                    value,
                })
            }
        }
    }

    fn if_stmt(&mut self) -> PResult<IfStmt> {
        let start = self.bump().span; // if
        if self.at_kw(Kw::Let) {
            return self.error(self.span(), "`if let` is not supported by the compiler yet");
        }
        let cond = self.header_expr()?;
        let then = self.block()?;
        // `else` belongs on the same line as `}`, but accept it on the next one.
        if *self.peek() == Tok::Newline && *self.peek_at(1) == Tok::Kw(Kw::Else) {
            self.bump();
        }
        let otherwise = if self.eat_kw(Kw::Else) {
            if self.at_kw(Kw::If) {
                Some(Else::If(Box::new(self.if_stmt()?)))
            } else {
                Some(Else::Block(self.block()?))
            }
        } else {
            None
        };
        let end = match &otherwise {
            Some(Else::If(i)) => i.span,
            Some(Else::Block(b)) => b.span,
            None => then.span,
        };
        Ok(IfStmt {
            cond,
            then,
            otherwise,
            span: start.to(end),
        })
    }

    // --- expressions --------------------------------------------------------

    fn expr(&mut self) -> PResult<Expr> {
        self.binary(1)
    }

    /// An expression in a header (`if`, `while`, `for`): a `{` after a name
    /// starts the block, not a struct literal.
    fn header_expr(&mut self) -> PResult<Expr> {
        let saved = std::mem::replace(&mut self.no_struct_lit, true);
        let e = self.expr();
        self.no_struct_lit = saved;
        e
    }

    /// An expression inside brackets, where struct literals are allowed
    /// again.
    fn nested_expr(&mut self) -> PResult<Expr> {
        let saved = std::mem::replace(&mut self.no_struct_lit, false);
        let e = self.expr();
        self.no_struct_lit = saved;
        e
    }

    /// Whether a `{` here starts a struct literal of the type just parsed.
    fn at_struct_lit(&self) -> bool {
        !self.no_struct_lit && self.at_p(P::LBrace)
    }

    /// `{name: value, ...}` after the type of a struct literal.
    fn struct_literal(&mut self, ty: TypeExpr) -> PResult<Expr> {
        let start = ty.span();
        self.bump(); // {
        let mut fields = Vec::new();
        loop {
            self.skip_newlines();
            if self.eat_p(P::RBrace) {
                break;
            }
            let name = self.ident("a field name")?;
            self.expect_p(P::Colon)?;
            self.skip_newlines();
            let value = self.nested_expr()?;
            fields.push(FieldInit { name, value });
            self.skip_newlines();
            if !self.eat_p(P::Comma) {
                self.skip_newlines();
                self.expect_p(P::RBrace)?;
                break;
            }
        }
        Ok(Expr {
            kind: ExprKind::StructLit(ty, fields),
            span: start.to(self.prev_span()),
        })
    }

    fn binary(&mut self, min_prec: u8) -> PResult<Expr> {
        let mut lhs = self.unary()?;
        while let Some((op, prec)) = binop_info(self.peek()) {
            if prec < min_prec {
                break;
            }
            let op_span = self.bump().span;
            let rhs = self.binary(prec + 1)?;
            if prec == COMPARISON
                && matches!(lhs.kind, ExprKind::Binary(prev, ..) if is_comparison(prev))
            {
                return self.error(op_span, "comparisons cannot be chained; use `&&`");
            }
            let span = lhs.span.to(rhs.span);
            lhs = Expr {
                kind: ExprKind::Binary(op, Box::new(lhs), Box::new(rhs)),
                span,
            };
        }
        Ok(lhs)
    }

    fn unary(&mut self) -> PResult<Expr> {
        let op = match self.peek() {
            Tok::P(P::Minus) => UnOp::Neg,
            Tok::P(P::Bang) => UnOp::Not,
            Tok::P(P::Tilde) => UnOp::BitNot,
            _ => return self.postfix(),
        };
        let start = self.bump().span;
        let operand = self.unary()?;
        let span = start.to(operand.span);
        Ok(Expr {
            kind: ExprKind::Unary(op, Box::new(operand)),
            span,
        })
    }

    fn postfix(&mut self) -> PResult<Expr> {
        let mut e = self.primary()?;
        loop {
            if self.eat_p(P::LParen) {
                let mut args = Vec::new();
                loop {
                    self.skip_newlines();
                    if self.eat_p(P::RParen) {
                        break;
                    }
                    args.push(self.nested_expr()?);
                    self.skip_newlines();
                    if !self.eat_p(P::Comma) {
                        self.skip_newlines();
                        self.expect_p(P::RParen)?;
                        break;
                    }
                }
                let span = e.span.to(self.prev_span());
                e = Expr {
                    kind: ExprKind::Call(Box::new(e), args),
                    span,
                };
            } else if self.eat_p(P::Dot) {
                let field = self.ident("a field or method name")?;
                if let ExprKind::Name(pkg) = &e.kind
                    && self.at_struct_lit()
                {
                    // `pkg.Name{...}`
                    let pkg = Ident {
                        name: pkg.clone(),
                        span: e.span,
                    };
                    e = self.struct_literal(TypeExpr::Qualified(pkg, field))?;
                    continue;
                }
                let span = e.span.to(field.span);
                e = Expr {
                    kind: ExprKind::Field(Box::new(e), field),
                    span,
                };
            } else if self.eat_p(P::LBracket) {
                self.skip_newlines();
                let index = self.nested_expr()?;
                self.skip_newlines();
                self.expect_p(P::RBracket)?;
                let span = e.span.to(self.prev_span());
                e = Expr {
                    kind: ExprKind::Index(Box::new(e), Box::new(index)),
                    span,
                };
            } else {
                return Ok(e);
            }
        }
    }

    fn primary(&mut self) -> PResult<Expr> {
        let span = self.span();
        let kind = match self.peek().clone() {
            Tok::Int(v) => ExprKind::Int(v),
            Tok::Char(c) => ExprKind::Char(c),
            Tok::Str(s) => ExprKind::Str(s),
            Tok::Kw(Kw::True) => ExprKind::Bool(true),
            Tok::Kw(Kw::False) => ExprKind::Bool(false),
            Tok::Ident(name) => {
                let id = self.ident("a name")?;
                if self.at_struct_lit() {
                    return self.struct_literal(TypeExpr::Named(id));
                }
                return Ok(Expr {
                    kind: ExprKind::Name(name),
                    span,
                });
            }
            Tok::P(P::LParen) => {
                self.bump();
                self.skip_newlines();
                let inner = self.nested_expr()?;
                self.skip_newlines();
                self.expect_p(P::RParen)?;
                return Ok(Expr {
                    kind: ExprKind::Paren(Box::new(inner)),
                    span: span.to(self.prev_span()),
                });
            }
            Tok::P(P::LBracket) => return self.array_literal(),
            Tok::Kw(kw @ (Kw::Try | Kw::None)) => {
                return self.error(
                    span,
                    format!("`{}` is not supported by the compiler yet", kw.as_str()),
                );
            }
            _ => return self.expected("an expression"),
        };
        self.bump();
        Ok(Expr { kind, span })
    }

    /// `[a, b, c]` or `[value; count]`.
    fn array_literal(&mut self) -> PResult<Expr> {
        let saved = std::mem::replace(&mut self.no_struct_lit, false);
        let e = self.array_literal_inner();
        self.no_struct_lit = saved;
        e
    }

    fn array_literal_inner(&mut self) -> PResult<Expr> {
        let start = self.bump().span; // [
        let mut elems = Vec::new();
        loop {
            self.skip_newlines_only();
            if self.eat_p(P::RBracket) {
                break;
            }
            elems.push(self.expr()?);
            if elems.len() == 1 && self.eat_p(P::Semi) {
                self.skip_newlines_only();
                let count = self.expr()?;
                self.skip_newlines_only();
                self.expect_p(P::RBracket)?;
                let value = elems.pop().expect("one element");
                return Ok(Expr {
                    kind: ExprKind::ArrayRepeat(Box::new(value), Box::new(count)),
                    span: start.to(self.prev_span()),
                });
            }
            self.skip_newlines_only();
            if !self.eat_p(P::Comma) {
                self.skip_newlines_only();
                self.expect_p(P::RBracket)?;
                break;
            }
        }
        Ok(Expr {
            kind: ExprKind::ArrayLit(elems),
            span: start.to(self.prev_span()),
        })
    }

    /// Skip newlines but not `;` (which separates a repeat literal's parts).
    fn skip_newlines_only(&mut self) {
        while *self.peek() == Tok::Newline {
            self.bump();
        }
    }
}

fn is_comparison(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::lex;

    fn parse_ok(src: &str) -> File {
        let (toks, diags) = lex(src, 0);
        assert!(diags.is_empty(), "{diags:?}");
        let (file, diags) = parse(toks, 0);
        assert!(diags.is_empty(), "{diags:?}");
        file
    }

    fn parse_errors(src: &str) -> Vec<String> {
        let (toks, _) = lex(src, 0);
        parse(toks, 0).1.into_iter().map(|d| d.message).collect()
    }

    #[test]
    fn parses_function_with_statements() {
        let file = parse_ok(
            "package main\n\nfn add(a: u32, b: u32) -> u32 {\n\tlet c = a +% b\n\treturn c\n}\n",
        );
        assert_eq!(file.package.unwrap().name, "main");
        let Item::Fn(f) = &file.items[0] else {
            panic!()
        };
        assert_eq!(f.name.name, "add");
        assert_eq!(f.params.len(), 2);
        assert_eq!(f.body.stmts.len(), 2);
    }

    #[test]
    fn precedence() {
        let file = parse_ok("fn f() -> bool {\n\treturn 1 + 2 * 3 == 7 && true\n}\n");
        let Item::Fn(f) = &file.items[0] else {
            panic!()
        };
        let Stmt::Return { value: Some(e), .. } = &f.body.stmts[0] else {
            panic!()
        };
        let ExprKind::Binary(BinOp::And, lhs, _) = &e.kind else {
            panic!("{e:?}")
        };
        let ExprKind::Binary(BinOp::Eq, sum, _) = &lhs.kind else {
            panic!()
        };
        let ExprKind::Binary(BinOp::Add, _, prod) = &sum.kind else {
            panic!()
        };
        assert!(matches!(prod.kind, ExprKind::Binary(BinOp::Mul, ..)));
    }

    #[test]
    fn arrays_slices_and_for() {
        let file = parse_ok(
            "fn f(xs: []u8, m: [][4]u8) {\n\tvar a: [N][2]u8 = [[1, 2], [3,\n\t\t4]]\n\tlet z = [0; 16]\n\ta[i][0] = xs[1]\n\tfor i in 0..xs.len {\n\t}\n\tfor x in xs {\n\t}\n}\n",
        );
        let Item::Fn(f) = &file.items[0] else {
            panic!()
        };
        assert!(matches!(f.params[0].ty, TypeExpr::Slice(..)));
        let TypeExpr::Slice(row, _) = &f.params[1].ty else {
            panic!()
        };
        assert!(matches!(**row, TypeExpr::Array(..)));
        let Stmt::Let {
            ty: Some(TypeExpr::Array(_, inner, _)),
            init: Some(init),
            ..
        } = &f.body.stmts[0]
        else {
            panic!("{:?}", f.body.stmts[0])
        };
        assert!(matches!(**inner, TypeExpr::Array(..)));
        assert!(matches!(&init.kind, ExprKind::ArrayLit(rows) if rows.len() == 2));
        let Stmt::Let { init: Some(z), .. } = &f.body.stmts[1] else {
            panic!()
        };
        assert!(matches!(z.kind, ExprKind::ArrayRepeat(..)));
        let Stmt::Assign { target, .. } = &f.body.stmts[2] else {
            panic!()
        };
        assert!(
            matches!(&target.kind, ExprKind::Index(base, _) if matches!(base.kind, ExprKind::Index(..)))
        );
        assert!(matches!(
            &f.body.stmts[3],
            Stmt::For {
                iter: ForIter::Range(..),
                ..
            }
        ));
        assert!(matches!(
            &f.body.stmts[4],
            Stmt::For {
                iter: ForIter::Each(..),
                ..
            }
        ));
    }

    #[test]
    fn structs() {
        let file = parse_ok(
            "pub struct P {\n\tx: u32\n\tq: os.Q\n}\nfn f() {\n\tlet p = P{x: 1, q: os.Q{\n\t\ta: [1],\n\t}}\n\tp.q.a[0] += 1\n}\n",
        );
        let Item::Struct(s) = &file.items[0] else {
            panic!()
        };
        assert!(s.is_pub && s.fields.len() == 2);
        assert!(matches!(s.fields[1].ty, TypeExpr::Qualified(..)));
        let Item::Fn(f) = &file.items[1] else {
            panic!()
        };
        let Stmt::Let {
            init: Some(init), ..
        } = &f.body.stmts[0]
        else {
            panic!()
        };
        let ExprKind::StructLit(TypeExpr::Named(_), fields) = &init.kind else {
            panic!("{init:?}")
        };
        assert!(matches!(
            fields[1].value.kind,
            ExprKind::StructLit(TypeExpr::Qualified(..), _)
        ));
        // In an `if` header, `{` after a name starts the block.
        let errs = parse_errors("fn f() {\n\tif p == P{x: 2} {\n\t}\n}\n");
        assert!(!errs.is_empty());
        parse_ok("fn f() {\n\tif p == (P{x: 2}) {\n\t}\n\tfor x in [P{x: 1}] {\n\t}\n}\n");
    }

    #[test]
    fn else_on_next_line_and_multiline_args() {
        parse_ok("fn f() {\n\tif a {\n\t\tg(1,\n\t\t\t2)\n\t}\n\telse {\n\t}\n}\n");
    }

    #[test]
    fn reports_and_recovers() {
        let errs = parse_errors("fn f() {\n\tlet = 1\n\treturn 1 < 2 < 3\n}\nenum S {}\n");
        assert_eq!(errs.len(), 3, "{errs:?}");
        assert!(errs[1].contains("chained"));
        assert!(errs[2].contains("not supported"));
    }
}
