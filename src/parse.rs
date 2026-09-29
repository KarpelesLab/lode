//! The parser: tokens to [`ast::File`](crate::ast::File).
//!
//! Recursive descent for items and statements, precedence climbing for
//! expressions. On a syntax error the parser records a diagnostic and skips to
//! the end of the statement or item, so one run reports several errors.

use crate::ast::*;
use crate::diag::Diagnostic;
use crate::lex::{Kw, P, Tok, Token};
use crate::source::Span;

/// Parse a token stream (as produced by [`crate::lex::lex`]).
pub fn parse(toks: Vec<Token>) -> (File, Vec<Diagnostic>) {
    let mut p = Parser {
        toks,
        pos: 0,
        diags: Vec::new(),
    };
    let file = p.file();
    (file, p.diags)
}

/// A syntax error has been recorded; the caller should recover.
struct Failed;

type PResult<T> = Result<T, Failed>;

struct Parser {
    toks: Vec<Token>,
    pos: usize,
    diags: Vec<Diagnostic>,
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

    fn file(&mut self) -> File {
        let mut file = File {
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
            Tok::Kw(Kw::Fn) => self.fn_decl(is_pub, start).map(Item::Fn),
            Tok::Kw(
                kw @ (Kw::Struct
                | Kw::Enum
                | Kw::Trait
                | Kw::Impl
                | Kw::Type
                | Kw::Alias
                | Kw::Const
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

    fn fn_decl(&mut self, is_pub: bool, start: Span) -> PResult<FnDecl> {
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
            Tok::Ident(_) => Ok(TypeExpr::Named(self.ident("a type")?)),
            Tok::P(P::LParen) if *self.peek_at(1) == Tok::P(P::RParen) => {
                let start = self.bump().span;
                let end = self.bump().span;
                Ok(TypeExpr::Unit(start.to(end)))
            }
            Tok::P(P::Question | P::LBracket | P::Star) => self.error(
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
                let cond = self.expr()?;
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
            Tok::Kw(Kw::Break) => Ok(Stmt::Break(self.bump().span)),
            Tok::Kw(Kw::Continue) => Ok(Stmt::Continue(self.bump().span)),
            Tok::Kw(
                kw @ (Kw::For
                | Kw::Match
                | Kw::Defer
                | Kw::Errdefer
                | Kw::Throw
                | Kw::Scope
                | Kw::Unsafe
                | Kw::Comptime),
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
        let cond = self.expr()?;
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
                    args.push(self.expr()?);
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
                let span = e.span.to(field.span);
                e = Expr {
                    kind: ExprKind::Field(Box::new(e), field),
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
            Tok::Ident(name) => ExprKind::Name(name),
            Tok::P(P::LParen) => {
                self.bump();
                self.skip_newlines();
                let inner = self.expr()?;
                self.skip_newlines();
                self.expect_p(P::RParen)?;
                return Ok(Expr {
                    kind: ExprKind::Paren(Box::new(inner)),
                    span: span.to(self.prev_span()),
                });
            }
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
        let (toks, diags) = lex(src);
        assert!(diags.is_empty(), "{diags:?}");
        let (file, diags) = parse(toks);
        assert!(diags.is_empty(), "{diags:?}");
        file
    }

    fn parse_errors(src: &str) -> Vec<String> {
        let (toks, _) = lex(src);
        parse(toks).1.into_iter().map(|d| d.message).collect()
    }

    #[test]
    fn parses_function_with_statements() {
        let file = parse_ok(
            "package main\n\nfn add(a: u32, b: u32) -> u32 {\n\tlet c = a +% b\n\treturn c\n}\n",
        );
        assert_eq!(file.package.unwrap().name, "main");
        let Item::Fn(f) = &file.items[0];
        assert_eq!(f.name.name, "add");
        assert_eq!(f.params.len(), 2);
        assert_eq!(f.body.stmts.len(), 2);
    }

    #[test]
    fn precedence() {
        let file = parse_ok("fn f() -> bool {\n\treturn 1 + 2 * 3 == 7 && true\n}\n");
        let Item::Fn(f) = &file.items[0];
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
    fn else_on_next_line_and_multiline_args() {
        parse_ok("fn f() {\n\tif a {\n\t\tg(1,\n\t\t\t2)\n\t}\n\telse {\n\t}\n}\n");
    }

    #[test]
    fn reports_and_recovers() {
        let errs = parse_errors("fn f() {\n\tlet = 1\n\treturn 1 < 2 < 3\n}\nstruct S {}\n");
        assert_eq!(errs.len(), 3, "{errs:?}");
        assert!(errs[1].contains("chained"));
        assert!(errs[2].contains("not supported"));
    }
}
