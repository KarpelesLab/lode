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

/// Where a function is declared: at package level, or in a trait or an
/// `impl`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Member {
    No,
    Trait,
    Impl,
}

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
        P::Coalesce => (BinOp::Coalesce, COALESCE),
        P::Pipe => (BinOp::BitOr, 5),
        P::Caret => (BinOp::BitXor, 6),
        P::Amp => (BinOp::BitAnd, 7),
        P::Shl => (BinOp::Shl, 8),
        P::ShlWrap => (BinOp::ShlWrap, 8),
        P::Shr => (BinOp::Shr, 8),
        P::Plus => (BinOp::Add, 9),
        P::Minus => (BinOp::Sub, 9),
        P::AddWrap => (BinOp::AddWrap, 9),
        P::SubWrap => (BinOp::SubWrap, 9),
        P::AddSat => (BinOp::AddSat, 9),
        P::SubSat => (BinOp::SubSat, 9),
        P::Star => (BinOp::Mul, 10),
        P::Slash => (BinOp::Div, 10),
        P::Percent => (BinOp::Rem, 10),
        P::MulWrap => (BinOp::MulWrap, 10),
        P::MulSat => (BinOp::MulSat, 10),
        _ => return None,
    })
}

const COMPARISON: u8 = 3;

/// `??` binds tighter than comparisons (`x ?? 0 == 1` compares the value),
/// looser than arithmetic, and groups to the right: `a ?? b ?? c` is
/// `a ?? (b ?? c)`.
const COALESCE: u8 = 4;

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
        if self.at_p(P::At) {
            return self.attributed_item();
        }
        if self.at_kw(Kw::If) {
            return self.item_if().map(Item::If);
        }
        if matches!(self.peek(), Tok::Ident(n) if n == "compile_error")
            && *self.peek_at(1) == Tok::P(P::LParen)
        {
            return Ok(Item::CompileError(self.expr()?));
        }
        let is_pub = self.eat_kw(Kw::Pub);
        match self.peek().clone() {
            Tok::Kw(Kw::Fn) => self.fn_decl(is_pub, false, start).map(Item::Fn),
            Tok::Kw(Kw::Unsafe) if *self.peek_at(1) == Tok::Kw(Kw::Fn) => {
                self.bump();
                self.fn_decl(is_pub, true, start).map(Item::Fn)
            }
            Tok::Kw(Kw::Const) => self.const_decl(is_pub, start).map(Item::Const),
            Tok::Kw(Kw::Struct) => self.struct_decl(is_pub, start).map(Item::Struct),
            Tok::Kw(Kw::Enum) => self.enum_decl(is_pub, start).map(Item::Enum),
            Tok::Kw(Kw::Trait) => self.trait_decl(is_pub, start).map(Item::Trait),
            Tok::Kw(Kw::Impl) if is_pub => self.error(
                start,
                "an `impl` is not marked `pub`: it's visible wherever its trait and type are",
            ),
            Tok::Kw(Kw::Impl) => self.impl_decl(start).map(Item::Impl),
            Tok::Kw(kw @ (Kw::Type | Kw::Alias | Kw::Static | Kw::Unsafe)) => self.error(
                self.span(),
                format!(
                    "`{}` declarations are not supported by the compiler yet",
                    kw.as_str()
                ),
            ),
            _ => self.expected("a declaration (like `fn`)"),
        }
    }

    /// `@comptime_budget(n)` on its own line, then the `const` it applies
    /// to.
    fn attributed_item(&mut self) -> PResult<Item> {
        let at = self.bump().span; // @
        let name = self.ident("an attribute name")?;
        if name.name != "comptime_budget" {
            return self.error(
                at.to(name.span),
                format!("unknown attribute `@{}`", name.name),
            );
        }
        self.expect_p(P::LParen)?;
        let budget = self.nested_expr()?;
        self.expect_p(P::RParen)?;
        self.skip_newlines();
        let start = self.span();
        let is_pub = self.eat_kw(Kw::Pub);
        if !self.at_kw(Kw::Const) {
            return self.error(
                at.to(name.span),
                "`@comptime_budget` applies to a `const` declaration, on the next line",
            );
        }
        let mut c = self.const_decl(is_pub, start)?;
        c.budget = Some(budget);
        Ok(Item::Const(c))
    }

    /// `if comptime cond { items } else ...` at package level.
    fn item_if(&mut self) -> PResult<ItemIf> {
        let start = self.bump().span; // if
        if !self.eat_kw(Kw::Comptime) {
            return self.error(
                start,
                "a declaration can only be in an `if comptime`, whose condition is known when compiling",
            );
        }
        let cond = self.header_expr()?;
        let then = self.item_block()?;
        if *self.peek() == Tok::Newline && *self.peek_at(1) == Tok::Kw(Kw::Else) {
            self.bump();
        }
        let otherwise = if self.eat_kw(Kw::Else) {
            if self.at_kw(Kw::If) {
                Some(ItemElse::If(Box::new(self.item_if()?)))
            } else {
                Some(ItemElse::Items(self.item_block()?))
            }
        } else {
            None
        };
        Ok(ItemIf {
            cond,
            then,
            otherwise,
            span: start.to(self.prev_span()),
        })
    }

    /// `{ items }`, the declarations of a branch of a package-level `if
    /// comptime`.
    fn item_block(&mut self) -> PResult<Vec<Item>> {
        self.expect_p(P::LBrace)?;
        let mut items = Vec::new();
        loop {
            self.skip_newlines();
            match self.peek() {
                Tok::P(P::RBrace) => break,
                Tok::Eof => return self.expected("`}`"),
                _ => {}
            }
            match self.item() {
                Ok(item) => items.push(item),
                Err(Failed) => self.sync_item(),
            }
        }
        self.bump(); // }
        Ok(items)
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
            budget: None,
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
        let generics = if self.at_p(P::LBracket) {
            self.generic_params()?
        } else {
            Vec::new()
        };
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
            generics,
            fields,
            span: start.to(end),
        })
    }

    fn enum_decl(&mut self, is_pub: bool, start: Span) -> PResult<EnumDecl> {
        self.bump(); // enum
        let name = self.ident("an enum name")?;
        let generics = if self.at_p(P::LBracket) {
            self.generic_params()?
        } else {
            Vec::new()
        };
        let tag = if self.eat_p(P::Colon) {
            Some(self.type_expr()?)
        } else {
            None
        };
        self.expect_p(P::LBrace)?;
        let mut variants = Vec::new();
        loop {
            self.skip_newlines();
            if self.at_p(P::RBrace) {
                break;
            }
            let vname = self.ident("a variant name or `}`")?;
            let fields = if self.eat_p(P::LParen) {
                let mut fields = Vec::new();
                loop {
                    self.skip_newlines();
                    if self.eat_p(P::RParen) {
                        break;
                    }
                    let field = self.ident("a payload field name")?;
                    self.expect_p(P::Colon)?;
                    let ty = self.type_expr()?;
                    fields.push(FieldDecl { name: field, ty });
                    self.skip_newlines();
                    if !self.eat_p(P::Comma) {
                        self.skip_newlines();
                        self.expect_p(P::RParen)?;
                        break;
                    }
                }
                Some(fields)
            } else {
                None
            };
            let value = if self.eat_p(P::Eq) {
                Some(self.expr()?)
            } else {
                None
            };
            variants.push(VariantDecl {
                name: vname,
                fields,
                value,
            });
            if !matches!(self.peek(), Tok::Newline | Tok::P(P::Semi | P::RBrace)) {
                return self.expected("a new line after the variant");
            }
        }
        let end = self.bump().span;
        Ok(EnumDecl {
            is_pub,
            name,
            generics,
            tag,
            variants,
            span: start.to(end),
        })
    }

    fn fn_decl(&mut self, is_pub: bool, is_unsafe: bool, start: Span) -> PResult<FnDecl> {
        self.fn_decl_in(is_pub, is_unsafe, start, Member::No)
            .map(|(f, _)| f)
    }

    /// A function declaration, at package level or as a `member` of a
    /// trait or an `impl` (`fn name(self, ...)`, whose `self` is `Self`).
    /// In a trait, the body may be left out: the result says if it's there.
    fn fn_decl_in(
        &mut self,
        is_pub: bool,
        is_unsafe: bool,
        start: Span,
        member: Member,
    ) -> PResult<(FnDecl, bool)> {
        self.bump(); // fn
        let mut name = self.ident("a function name")?;
        let mut generics = if self.at_p(P::LBracket) {
            self.generic_params()?
        } else {
            Vec::new()
        };
        // `fn Type.name` (a method or an associated function), `fn
        // Type[A, B].name` (of a generic type), or `fn pkg.Type.name`,
        // which the checker rejects.
        let mut owner = None;
        let mut owner_generics = Vec::new();
        if member != Member::No && self.at_p(P::Dot) {
            return self.error(
                self.span(),
                format!(
                    "a method in {} is declared without its type: `fn name(self, ...)`",
                    if member == Member::Trait {
                        "a trait"
                    } else {
                        "an `impl`"
                    },
                ),
            );
        }
        let self_ty = TypeExpr::Named(Ident {
            name: "Self".to_owned(),
            span: name.span,
        });
        if member != Member::No {
            owner = Some(self_ty);
        } else if self.eat_p(P::Dot) {
            let member = self.ident("a method name")?;
            if generics.is_empty() && self.eat_p(P::Dot) {
                let method = self.ident("a method name")?;
                owner = Some(TypeExpr::Qualified(name, member));
                name = method;
            } else {
                owner = Some(TypeExpr::Named(name));
                name = member;
            }
            owner_generics = std::mem::take(&mut generics);
            if self.at_p(P::LBracket) {
                generics = self.generic_params()?;
            }
        }
        self.expect_p(P::LParen)?;
        let mut params = Vec::new();
        loop {
            self.skip_newlines();
            if self.eat_p(P::RParen) {
                break;
            }
            let param = self.param(owner.as_ref())?;
            if param.is_self() && !params.is_empty() {
                return self.error(param.name.span, "`self` must be the first parameter");
            }
            params.push(param);
            self.skip_newlines();
            if !self.eat_p(P::Comma) {
                self.skip_newlines();
                self.expect_p(P::RParen)?;
                break;
            }
        }
        let throws = if self.at_kw(Kw::Throws) {
            let start = self.bump().span;
            let ty = if self.eat_p(P::LParen) {
                let ty = self.type_expr()?;
                self.expect_p(P::RParen)?;
                Some(ty)
            } else {
                None
            };
            Some(Throws {
                ty,
                span: start.to(self.prev_span()),
            })
        } else {
            None
        };
        let ret = if self.eat_p(P::Arrow) {
            Some(self.type_expr()?)
        } else {
            None
        };
        if self.at_kw(Kw::Throws) {
            return self.error(
                self.span(),
                "`throws` comes before the return type: `fn f() throws(E) -> T`",
            );
        }
        for kw in [Kw::Uses, Kw::Where] {
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
        // A trait's required method has no body.
        let has_body = member != Member::Trait || self.at_p(P::LBrace);
        let body = if has_body {
            self.block()?
        } else {
            if !matches!(self.peek(), Tok::Newline | Tok::P(P::Semi | P::RBrace)) {
                return self.expected("a body `{ ... }` or a new line after the method");
            }
            Block {
                stmts: Vec::new(),
                span: self.prev_span(),
            }
        };
        Ok((
            FnDecl {
                is_pub,
                is_unsafe,
                owner: if member == Member::No { owner } else { None },
                owner_generics,
                name,
                generics,
                params,
                throws,
                ret,
                span: start.to(body.span),
                body,
            },
            has_body,
        ))
    }

    /// `trait Name: Super + Other { item ... }`: methods (with or without
    /// a body), `type Name: Bounds` and `const NAME: T`, one per line.
    fn trait_decl(&mut self, is_pub: bool, start: Span) -> PResult<TraitDecl> {
        self.bump(); // trait
        let name = self.ident("a trait name")?;
        if self.at_p(P::LBracket) {
            return self.error(
                self.span(),
                "generic traits are not supported by the compiler yet",
            );
        }
        let supers = if self.eat_p(P::Colon) {
            self.bounds()?
        } else {
            Vec::new()
        };
        self.expect_p(P::LBrace)?;
        let (items, end) = self.member_items("a trait", |p, istart| {
            Ok(match p.peek() {
                Tok::Kw(Kw::Fn) => {
                    let (decl, default) = p.fn_decl_in(false, false, istart, Member::Trait)?;
                    TraitItem::Method {
                        decl: Box::new(decl),
                        default,
                    }
                }
                Tok::Kw(Kw::Type) => {
                    p.bump();
                    let name = p.ident("an associated type name")?;
                    let bounds = if p.eat_p(P::Colon) {
                        p.bounds()?
                    } else {
                        Vec::new()
                    };
                    TraitItem::Type { name, bounds }
                }
                Tok::Kw(Kw::Const) => {
                    p.bump();
                    let name = p.ident("an associated constant name")?;
                    p.expect_p(P::Colon)?;
                    let ty = p.type_expr()?;
                    TraitItem::Const { name, ty }
                }
                _ => return p.expected("`fn`, `type`, `const` or `}`"),
            })
        })?;
        Ok(TraitDecl {
            is_pub,
            name,
            supers,
            items,
            span: start.to(end),
        })
    }

    /// `impl[A: Bound] Trait for Type[A] { item ... }`: methods, `type Name
    /// = T` and `const NAME: T = value`, one per line.
    fn impl_decl(&mut self, start: Span) -> PResult<ImplDecl> {
        self.bump(); // impl
        let generics = if self.at_p(P::LBracket) {
            self.generic_params()?
        } else {
            Vec::new()
        };
        let trait_ = self.bound()?;
        if !self.eat_kw(Kw::For) {
            return self.expected("`for` and the type: `impl Trait for Type`");
        }
        let ty = self.type_expr()?;
        self.expect_p(P::LBrace)?;
        let (items, end) = self.member_items("an `impl`", |p, istart| {
            Ok(match p.peek() {
                Tok::Kw(Kw::Fn) => {
                    let (decl, _) = p.fn_decl_in(false, false, istart, Member::Impl)?;
                    ImplItem::Method(decl)
                }
                Tok::Kw(Kw::Type) => {
                    p.bump();
                    let name = p.ident("an associated type name")?;
                    p.expect_p(P::Eq)?;
                    let ty = p.type_expr()?;
                    ImplItem::Type { name, ty }
                }
                Tok::Kw(Kw::Const) => ImplItem::Const(p.const_decl(false, istart)?),
                _ => return p.expected("`fn`, `type`, `const` or `}`"),
            })
        })?;
        Ok(ImplDecl {
            generics,
            trait_,
            ty,
            items,
            span: start.to(end),
        })
    }

    /// The items of a trait or an `impl` (`what`), after its `{`, each
    /// parsed by `one` (given where it starts), one per line, and the span
    /// of the closing `}`. An item in error is skipped to the end of its
    /// line, so the others are still parsed.
    fn member_items<T>(
        &mut self,
        what: &str,
        mut one: impl FnMut(&mut Parser, Span) -> PResult<T>,
    ) -> PResult<(Vec<T>, Span)> {
        let mut items = Vec::new();
        let mut ok = true;
        loop {
            self.skip_newlines();
            if self.at_p(P::RBrace) {
                break;
            }
            if *self.peek() == Tok::Eof {
                return self.expected("`}`");
            }
            let istart = self.span();
            let item = if self.at_kw(Kw::Pub) {
                self.error(
                    istart,
                    format!(
                        "the items of {what} are as visible as the trait: they're not marked `pub`"
                    ),
                )
            } else {
                one(self, istart)
            };
            match item {
                Ok(item) if matches!(self.peek(), Tok::Newline | Tok::P(P::Semi | P::RBrace)) => {
                    items.push(item);
                }
                Ok(_) => {
                    let _: PResult<()> = self.expected("a new line after the item");
                    ok = false;
                    self.sync_member();
                }
                Err(Failed) => {
                    ok = false;
                    self.sync_member();
                }
            }
        }
        let end = self.bump().span;
        if !ok {
            return Err(Failed);
        }
        Ok((items, end))
    }

    /// Skip to the start of the next item of a trait or an `impl`, or to
    /// its closing `}`.
    fn sync_member(&mut self) {
        let mut depth = 0usize;
        loop {
            match self.peek() {
                Tok::Eof => return,
                Tok::P(P::RBrace) if depth == 0 => return,
                Tok::P(P::LBrace | P::LParen | P::LBracket) => depth += 1,
                Tok::P(P::RBrace | P::RParen | P::RBracket) => depth -= 1,
                Tok::Newline if depth == 0 => {
                    self.bump();
                    return;
                }
                _ => {}
            }
            self.bump();
        }
    }

    /// A trait in a bound: `Ordered` or `io.Writer`.
    fn bound(&mut self) -> PResult<Bound> {
        let first = self.ident("a trait")?;
        if self.eat_p(P::Dot) {
            let name = self.ident("a trait name")?;
            return Ok(Bound {
                pkg: Some(first),
                name,
            });
        }
        Ok(Bound {
            pkg: None,
            name: first,
        })
    }

    /// Traits joined with `+`: `Ordered + Copy`.
    fn bounds(&mut self) -> PResult<Vec<Bound>> {
        let mut bounds = Vec::new();
        loop {
            bounds.push(self.bound()?);
            if !self.eat_p(P::Plus) {
                break;
            }
        }
        Ok(bounds)
    }

    /// The type parameters of a generic function: `[T: Ordered + Copy, U]`.
    fn generic_params(&mut self) -> PResult<Vec<GenericParam>> {
        let open = self.bump().span; // [
        let mut params = Vec::new();
        loop {
            self.skip_newlines();
            if self.at_p(P::RBracket) {
                break;
            }
            let name = self.ident("a type parameter name")?;
            let bounds = if self.eat_p(P::Colon) {
                self.bounds()?
            } else {
                Vec::new()
            };
            params.push(GenericParam { name, bounds });
            self.skip_newlines();
            if !self.eat_p(P::Comma) {
                break;
            }
        }
        self.skip_newlines();
        let close = self.expect_p(P::RBracket)?;
        if params.is_empty() {
            return self.error(
                open.to(close),
                "a generic declaration needs a parameter in its brackets",
            );
        }
        Ok(params)
    }

    /// The arguments of a generic type, after its name: `[u8, bool]`,
    /// `[64]`, `[T, N]`. Each is a type when it parses as one followed by
    /// `,` or `]`; otherwise an expression, a value for a value parameter.
    fn type_args(&mut self) -> PResult<(Vec<TypeArg>, Span)> {
        let open = self.bump().span; // [
        let mut items = Vec::new();
        loop {
            self.skip_newlines();
            if self.at_p(P::RBracket) {
                break;
            }
            let (pos, diags) = (self.pos, self.diags.len());
            let item = match self.type_expr() {
                Ok(t) if self.at_p(P::Comma) || self.at_p(P::RBracket) => TypeArg::Type(t),
                _ => {
                    self.pos = pos;
                    self.diags.truncate(diags);
                    TypeArg::Expr(self.nested_expr()?)
                }
            };
            items.push(item);
            self.skip_newlines();
            if !self.eat_p(P::Comma) {
                break;
            }
        }
        self.skip_newlines();
        let close = self.expect_p(P::RBracket)?;
        if items.is_empty() {
            return self.error(open.to(close), "expected the type's arguments in brackets");
        }
        Ok((items, close))
    }

    /// An item in brackets after an expression. It's a type when it starts
    /// with a token only a type starts with (`?`, `??`, `*`), or with a `[`
    /// that parses as a slice or an array type followed by `,` or `]`
    /// (`[]u8`, `[4]u8`); otherwise an expression, which the checker reads
    /// as an index or as a type name.
    fn bracket_item(&mut self) -> PResult<TypeArg> {
        match self.peek() {
            Tok::P(P::Question | P::Coalesce | P::Star) => {
                return Ok(TypeArg::Type(self.type_expr()?));
            }
            Tok::P(P::LBracket) => {
                let (pos, diags) = (self.pos, self.diags.len());
                if let Ok(t) = self.type_expr() {
                    self.skip_newlines();
                    if self.at_p(P::Comma) || self.at_p(P::RBracket) {
                        return Ok(TypeArg::Type(t));
                    }
                }
                self.pos = pos;
                self.diags.truncate(diags);
            }
            _ => {}
        }
        Ok(TypeArg::Expr(self.nested_expr()?))
    }

    /// A parameter. `owner` is the type of a method (`fn Type.name`), whose
    /// first parameter can be `self`, written without a type.
    fn param(&mut self, owner: Option<&TypeExpr>) -> PResult<Param> {
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
        if name.name == "self" {
            let Some(owner) = owner else {
                return self.error(
                    name.span,
                    "only a method has `self`: declare it as `fn Type.name(self, ...)`",
                );
            };
            if self.at_p(P::Colon) {
                return self.error(
                    self.span(),
                    "`self` is written without a type: it's the method's type",
                );
            }
            // `self` has the owner's type; its span is `self`'s.
            let ty = match owner {
                TypeExpr::Named(id) => TypeExpr::Named(Ident {
                    name: id.name.clone(),
                    span: name.span,
                }),
                other => other.clone(),
            };
            return Ok(Param {
                convention,
                name,
                ty,
            });
        }
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
                let base = if self.eat_p(P::Dot) {
                    let member = self.ident("a type name")?;
                    TypeExpr::Qualified(name, member)
                } else {
                    TypeExpr::Named(name)
                };
                if !self.at_p(P::LBracket) {
                    return Ok(base);
                }
                let (args, close) = self.type_args()?;
                let span = base.span().to(close);
                Ok(TypeExpr::Generic(Box::new(base), args, span))
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
            Tok::P(P::Question) => {
                let start = self.bump().span;
                let inner = self.type_expr()?;
                let span = start.to(inner.span());
                Ok(TypeExpr::Optional(Box::new(inner), span))
            }
            // `??T` lexes as one `??` token: an optional of an optional.
            Tok::P(P::Coalesce) => {
                let start = self.bump().span;
                let inner = self.type_expr()?;
                let span = start.to(inner.span());
                let mid = Span {
                    start: start.start + 1,
                    ..span
                };
                Ok(TypeExpr::Optional(
                    Box::new(TypeExpr::Optional(Box::new(inner), mid)),
                    span,
                ))
            }
            _ => self.expected("a type"),
        }
    }

    // --- statements ---------------------------------------------------------

    /// The block after an `if` or `while` condition. A `=` there is most
    /// likely a comparison written as an assignment.
    fn condition_block(&mut self) -> PResult<Block> {
        if self.at_p(P::Eq) {
            let found = self.peek().clone();
            self.diags.push(
                Diagnostic::error(self.span(), format!("expected `{{`, found {found}"))
                    .with_help("use `==` to compare"),
            );
            return Err(Failed);
        }
        self.block()
    }

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
                let otherwise = if init.is_some() && self.eat_kw(Kw::Else) {
                    Some(self.block()?)
                } else {
                    None
                };
                Ok(Stmt::Let {
                    mutable: kw == Kw::Var,
                    name,
                    ty,
                    init,
                    otherwise,
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
                let body = self.condition_block()?;
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
            Tok::Kw(Kw::Match) => self.match_stmt(),
            Tok::Kw(Kw::Throw) => {
                self.bump();
                let value = self.expr()?;
                Ok(Stmt::Throw {
                    span: start.to(value.span),
                    value,
                })
            }
            Tok::Kw(kw @ (Kw::Defer | Kw::Errdefer)) => {
                self.bump();
                let body = self.block_or_stmt()?;
                Ok(Stmt::Defer {
                    span: start.to(body.span),
                    body,
                    on_error: kw == Kw::Errdefer,
                })
            }
            Tok::Kw(kw @ (Kw::Scope | Kw::Comptime)) => self.error(
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
                    Tok::P(P::ShlWrapAssign) => Some(BinOp::ShlWrap),
                    Tok::P(P::AddWrapAssign) => Some(BinOp::AddWrap),
                    Tok::P(P::SubWrapAssign) => Some(BinOp::SubWrap),
                    Tok::P(P::MulWrapAssign) => Some(BinOp::MulWrap),
                    Tok::P(P::AddSatAssign) => Some(BinOp::AddSat),
                    Tok::P(P::SubSatAssign) => Some(BinOp::SubSat),
                    Tok::P(P::MulSatAssign) => Some(BinOp::MulSat),
                    Tok::P(P::AndAssign) => Some(BinOp::BitAnd),
                    Tok::P(P::OrAssign) => Some(BinOp::BitOr),
                    Tok::P(P::XorAssign) => Some(BinOp::BitXor),
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

    /// `match value { pattern => body ... }`, one arm per line. A body is a
    /// block, or a single statement on the arm's line.
    fn match_stmt(&mut self) -> PResult<Stmt> {
        let start = self.bump().span; // match
        let value = self.header_expr()?;
        self.expect_p(P::LBrace)?;
        let mut arms = Vec::new();
        loop {
            self.skip_newlines();
            match self.peek() {
                Tok::P(P::RBrace) => break,
                Tok::Eof => return self.expected("`}`"),
                _ => {}
            }
            match self.arm() {
                Ok(arm) => {
                    arms.push(arm);
                    if !matches!(self.peek(), Tok::Newline | Tok::P(P::Semi | P::RBrace)) {
                        let _ = self.expected::<()>("end of line after the arm");
                        self.sync_statement();
                    }
                }
                Err(Failed) => self.sync_statement(),
            }
        }
        let end = self.bump().span;
        Ok(Stmt::Match {
            value,
            arms,
            span: start.to(end),
        })
    }

    fn arm(&mut self) -> PResult<Arm> {
        let pattern = self.pattern()?;
        self.expect_p(P::FatArrow)?;
        let body = self.block_or_stmt()?;
        Ok(Arm { pattern, body })
    }

    /// A block, or a single statement on the same line (a `match` arm, a
    /// `defer`), as a block of that statement.
    fn block_or_stmt(&mut self) -> PResult<Block> {
        if self.at_p(P::LBrace) {
            return self.block();
        }
        let start = self.span();
        let stmt = self.stmt()?;
        Ok(Block {
            stmts: vec![stmt],
            span: start.to(self.prev_span()),
        })
    }

    /// A pattern, or alternatives `a | b | c`.
    fn pattern(&mut self) -> PResult<Pattern> {
        let first = self.single_pattern()?;
        if !self.at_p(P::Pipe) {
            return Ok(first);
        }
        let mut alts = vec![first];
        while self.eat_p(P::Pipe) {
            alts.push(self.single_pattern()?);
        }
        let span = alts[0].span().to(self.prev_span());
        Ok(Pattern::Or(alts, span))
    }

    /// `_`, a variant `name` or `name(a, _, c)`, a value (`3`, `-1`, `'a'`,
    /// `true`, `pkg.MAX`), or a range of them `lo..=hi`.
    fn single_pattern(&mut self) -> PResult<Pattern> {
        let name = match self.peek().clone() {
            Tok::Ident(n) if n == "_" => return Ok(Pattern::Wildcard(self.bump().span)),
            Tok::Ident(_) if *self.peek_at(1) != Tok::P(P::Dot) => self.ident("a variant name")?,
            // The variants of an optional are `none` and `some`.
            Tok::Kw(Kw::None) => Ident {
                name: "none".to_owned(),
                span: self.bump().span,
            },
            Tok::Int(_)
            | Tok::Char(_)
            | Tok::Ident(_)
            | Tok::Kw(Kw::True | Kw::False)
            | Tok::P(P::Minus | P::LParen) => {
                let value = self.unary()?;
                return self.range_pattern(Pattern::Value(value));
            }
            _ => return self.expected("a pattern: a variant name, a value or `_`"),
        };
        let bindings = if self.eat_p(P::LParen) {
            let mut names = Vec::new();
            loop {
                self.skip_newlines();
                if self.eat_p(P::RParen) {
                    break;
                }
                names.push(self.ident("a name to bind, or `_`")?);
                self.skip_newlines();
                if !self.eat_p(P::Comma) {
                    self.skip_newlines();
                    self.expect_p(P::RParen)?;
                    break;
                }
            }
            Some(names)
        } else {
            None
        };
        let pattern = Pattern::Variant {
            span: name.span.to(self.prev_span()),
            name,
            bindings,
        };
        self.range_pattern(pattern)
    }

    /// `lo..=hi` if a range follows the pattern `lo` (a value, or a name
    /// without bindings), or else `lo` itself.
    fn range_pattern(&mut self, lo: Pattern) -> PResult<Pattern> {
        if self.at_p(P::DotDot) {
            return self.error(
                self.span(),
                "a range pattern includes its end: write `lo..=hi`",
            );
        }
        if !self.at_p(P::DotDotEq) {
            return Ok(lo);
        }
        let lo = match lo {
            Pattern::Value(e) => e,
            Pattern::Variant {
                name,
                bindings: None,
                ..
            } => Expr {
                span: name.span,
                kind: ExprKind::Name(name.name),
            },
            other => return self.error(other.span(), "a range needs a value on each side"),
        };
        self.bump(); // ..=
        let hi = self.unary()?;
        let span = lo.span.to(hi.span);
        Ok(Pattern::Range(lo, hi, span))
    }

    fn if_stmt(&mut self) -> PResult<IfStmt> {
        let start = self.bump().span; // if
        let comptime = self.eat_kw(Kw::Comptime);
        if comptime && self.at_kw(Kw::Let) {
            return self.error(self.span(), "`if comptime` can't bind a value with `let`");
        }
        let binding = if self.eat_kw(Kw::Let) {
            let name = self.ident("a variable name")?;
            self.expect_p(P::Eq)?;
            Some(name)
        } else {
            None
        };
        let cond = self.header_expr()?;
        let then = self.condition_block()?;
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
            comptime,
            binding,
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
        loop {
            // `catch` binds like `??`.
            if self.at_kw(Kw::Catch) && COALESCE >= min_prec {
                lhs = self.catch(lhs)?;
                continue;
            }
            let Some((op, prec)) = binop_info(self.peek()) else {
                break;
            };
            if prec < min_prec {
                break;
            }
            let op_span = self.bump().span;
            let rhs = if op == BinOp::Coalesce {
                self.binary(prec)?
            } else {
                self.binary(prec + 1)?
            };
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

    /// `value catch name { ... }`, `value catch _ { ... }` or
    /// `value catch fallback`.
    fn catch(&mut self, value: Expr) -> PResult<Expr> {
        self.bump(); // catch
        let (binding, handler) = match self.peek().clone() {
            // As after `if`, a `{` after a name starts a block.
            Tok::Ident(name)
                if *self.peek_at(1) == Tok::P(P::LBrace)
                    && matches!(self.peek_at(2), Tok::Ident(_))
                    && *self.peek_at(3) == Tok::P(P::Colon) =>
            {
                return self.error(
                    self.span(),
                    format!(
                        "a struct literal after `catch` goes in parentheses: `catch ({name}{{...}})`"
                    ),
                );
            }
            Tok::Ident(name) if *self.peek_at(1) == Tok::P(P::LBrace) => {
                let id = self.ident("a name for the error")?;
                // Struct literals are allowed in the block, even in a header.
                let saved = std::mem::replace(&mut self.no_struct_lit, false);
                let block = self.block();
                self.no_struct_lit = saved;
                let binding = (name != "_").then_some(id);
                (binding, CatchHandler::Block(block?))
            }
            Tok::P(P::LBrace) => {
                return self.error(
                    self.span(),
                    "name the error before the block (`catch e {`), or ignore it with `catch _ {`",
                );
            }
            _ => (None, CatchHandler::Value(Box::new(self.binary(COALESCE)?))),
        };
        Ok(Expr {
            span: value.span.to(self.prev_span()),
            kind: ExprKind::Catch {
                value: Box::new(value),
                binding,
                handler,
            },
        })
    }

    fn unary(&mut self) -> PResult<Expr> {
        // `try call`, and `throw value` after `??`.
        if let Tok::Kw(kw @ (Kw::Try | Kw::Throw)) = *self.peek() {
            let start = self.bump().span;
            let operand = Box::new(self.unary()?);
            let span = start.to(operand.span);
            let kind = if kw == Kw::Try {
                ExprKind::Try(operand)
            } else {
                ExprKind::Throw(operand)
            };
            return Ok(Expr { kind, span });
        }
        // `&place`: an argument passed `inout` or `set`.
        if self.at_p(P::Amp) {
            let start = self.bump().span;
            let operand = self.unary()?;
            let span = start.to(operand.span);
            return Ok(Expr {
                kind: ExprKind::Ref(Box::new(operand)),
                span,
            });
        }
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
                let start = e.span;
                self.skip_newlines();
                // `a[i]`, generic arguments `f[u32, T]`, or a slice
                // `a[i..j]` with either bound left out.
                let first = if self.at_p(P::DotDot) {
                    None
                } else {
                    Some(self.bracket_item()?)
                };
                self.skip_newlines();
                let kind = if self.at_p(P::DotDot) || self.at_p(P::DotDotEq) {
                    let first = match first {
                        None => None,
                        Some(TypeArg::Expr(x)) => Some(Box::new(x)),
                        Some(TypeArg::Type(t)) => {
                            return self.error(t.span(), "a slice's start must be an integer");
                        }
                    };
                    if self.at_p(P::DotDotEq) {
                        let at = self.span();
                        self.diags.push(
                            Diagnostic::error(
                                at,
                                "a slice's end is exclusive: `a[i..j]` ends before `j`",
                            )
                            .with_help("for an inclusive end, write `a[i..j + 1]`"),
                        );
                        return Err(Failed);
                    }
                    self.bump(); // ..
                    self.skip_newlines();
                    let end = if self.at_p(P::RBracket) {
                        None
                    } else {
                        Some(Box::new(self.nested_expr()?))
                    };
                    ExprKind::Slice(Box::new(e), first, end)
                } else {
                    let mut items = vec![first.expect("an item before `]`")];
                    while self.eat_p(P::Comma) {
                        self.skip_newlines();
                        items.push(self.bracket_item()?);
                        self.skip_newlines();
                    }
                    // One expression is an index (or a generic argument,
                    // which the checker tells from what `e` names).
                    match <[TypeArg; 1]>::try_from(items) {
                        Ok([TypeArg::Expr(index)]) => ExprKind::Index(Box::new(e), Box::new(index)),
                        Ok(items) => ExprKind::TypeArgs(Box::new(e), items.into()),
                        Err(items) => ExprKind::TypeArgs(Box::new(e), items),
                    }
                };
                self.skip_newlines();
                self.expect_p(P::RBracket)?;
                let span = start.to(self.prev_span());
                // `Pair[u8, bool]{...}`: a literal of a generic struct.
                if self.at_struct_lit()
                    && let Some(ty) = generic_type(&kind, span)
                {
                    e = self.struct_literal(ty)?;
                    continue;
                }
                e = Expr { kind, span };
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
            Tok::Kw(Kw::None) => ExprKind::None,
            // `.name`: a variant of the enum the context expects.
            Tok::P(P::Dot) if matches!(self.peek_at(1), Tok::Ident(_)) => {
                self.bump();
                let name = self.ident("a variant name")?;
                return Ok(Expr {
                    span: span.to(name.span),
                    kind: ExprKind::Dot(name),
                });
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

/// The type `kind` names when it's a type's name with arguments
/// (`Pair[u8, bool]`, `geo.Pair[u8]`), before the `{` of a literal.
fn generic_type(kind: &ExprKind, span: Span) -> Option<TypeExpr> {
    let (base, items) = match kind {
        ExprKind::Index(base, index) => (base, vec![TypeArg::Expr((**index).clone())]),
        ExprKind::TypeArgs(base, items) => (base, items.clone()),
        _ => return None,
    };
    let base = match &base.kind {
        ExprKind::Name(n) => TypeExpr::Named(Ident {
            name: n.clone(),
            span: base.span,
        }),
        ExprKind::Field(pkg, name) => match &pkg.kind {
            ExprKind::Name(p) => TypeExpr::Qualified(
                Ident {
                    name: p.clone(),
                    span: pkg.span,
                },
                name.clone(),
            ),
            _ => return None,
        },
        _ => return None,
    };
    Some(TypeExpr::Generic(Box::new(base), items, span))
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
    fn assignment_as_condition() {
        for src in [
            "fn f() {\n\tif n = 3 {\n\t}\n}\n",
            "fn f() {\n\twhile n = 3 {\n\t}\n}\n",
        ] {
            let (toks, _) = lex(src, 0);
            let diags = parse(toks, 0).1;
            assert_eq!(diags.len(), 1, "{diags:?}");
            assert_eq!(diags[0].message, "expected `{`, found `=`");
            assert_eq!(diags[0].help, ["use `==` to compare"]);
        }
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
    fn slicing() {
        let file = parse_ok("fn f() {\n\tg(a[i..j], a[1..], a[..n + 1], a[..], a[i..j][k])\n}\n");
        let Item::Fn(f) = &file.items[0] else {
            panic!()
        };
        let Stmt::Expr(e) = &f.body.stmts[0] else {
            panic!()
        };
        let ExprKind::Call(_, args) = &e.kind else {
            panic!("{e:?}")
        };
        let bounds: Vec<(bool, bool)> = args[..4]
            .iter()
            .map(|a| match &a.kind {
                ExprKind::Slice(_, s, e) => (s.is_some(), e.is_some()),
                other => panic!("{other:?}"),
            })
            .collect();
        assert_eq!(
            bounds,
            [(true, true), (true, false), (false, true), (false, false)]
        );
        assert!(
            matches!(&args[4].kind, ExprKind::Index(base, _) if matches!(base.kind, ExprKind::Slice(..)))
        );

        let (toks, _) = lex("fn f() {\n\tg(a[i..=j])\n}\n", 0);
        let diags = parse(toks, 0).1;
        assert_eq!(
            diags[0].message,
            "a slice's end is exclusive: `a[i..j]` ends before `j`"
        );
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
    fn enums_match_and_optionals() {
        let file = parse_ok(
            "pub enum Shape {\n\tcircle(c: Point, r: u32)\n\tdot\n}\nenum Color: u8 {\n\tred = 1\n}\n\
             fn f(s: Shape, o: ?u8, p: ??u8) {\n\tmatch s {\n\t\tcircle(_, r) => return r\n\
             \t\tdot => {\n\t\t}\n\t\t_ => g()\n\t}\n\tif let v = o {\n\t}\n\
             \tlet w = o else {\n\t\treturn\n\t}\n\tlet x = o ?? p ?? 1 + 2 == 3\n\tlet n: ?u8 = none\n}\n",
        );
        let Item::Enum(e) = &file.items[0] else {
            panic!()
        };
        assert!(e.is_pub && e.tag.is_none() && e.variants.len() == 2);
        assert_eq!(e.variants[0].fields.as_ref().map(Vec::len), Some(2));
        assert!(e.variants[1].fields.is_none());
        let Item::Enum(c) = &file.items[1] else {
            panic!()
        };
        assert!(c.tag.is_some() && c.variants[0].value.is_some());
        let Item::Fn(f) = &file.items[2] else {
            panic!()
        };
        assert!(matches!(&f.params[2].ty, TypeExpr::Optional(inner, _)
            if matches!(**inner, TypeExpr::Optional(..))));
        let Stmt::Match { arms, .. } = &f.body.stmts[0] else {
            panic!()
        };
        assert_eq!(arms.len(), 3);
        assert!(
            matches!(&arms[0].pattern, Pattern::Variant { bindings: Some(b), .. } if b.len() == 2)
        );
        assert!(matches!(arms[2].pattern, Pattern::Wildcard(_)));
        assert!(matches!(&f.body.stmts[1], Stmt::If(i) if i.binding.is_some()));
        assert!(matches!(
            &f.body.stmts[2],
            Stmt::Let {
                otherwise: Some(_),
                ..
            }
        ));
        // `o ?? (p ?? (1 + 2))`, compared with 3.
        let Stmt::Let { init: Some(x), .. } = &f.body.stmts[3] else {
            panic!()
        };
        let ExprKind::Binary(BinOp::Eq, lhs, _) = &x.kind else {
            panic!("{x:?}")
        };
        let ExprKind::Binary(BinOp::Coalesce, _, rest) = &lhs.kind else {
            panic!()
        };
        assert!(
            matches!(&rest.kind, ExprKind::Binary(BinOp::Coalesce, _, sum)
            if matches!(sum.kind, ExprKind::Binary(BinOp::Add, ..)))
        );
    }

    #[test]
    fn errors_and_defer() {
        let file = parse_ok(
            "fn f(s: str) throws(E) -> u32 {\n\tdefer g()\n\terrdefer {\n\t\th()\n\t}\n\
             \tlet a = try p(s) + 1\n\tlet b = p(s) catch e {\n\t\treturn 0\n\t}\n\
             \tp(s) catch _ {}\n\tlet c = p(s) catch 0 == 1\n\tlet d = o ?? throw .bad(1)\n\
             \tthrow .empty\n}\nfn g() throws {\n}\n",
        );
        let Item::Fn(f) = &file.items[0] else {
            panic!()
        };
        assert!(matches!(&f.throws, Some(Throws { ty: Some(_), .. })));
        let s = &f.body.stmts;
        assert!(
            matches!(&s[0], Stmt::Defer { on_error: false, body, .. } if body.stmts.len() == 1)
        );
        assert!(matches!(&s[1], Stmt::Defer { on_error: true, .. }));
        // `try` binds to its operand: `(try p(s)) + 1`.
        let Stmt::Let { init: Some(a), .. } = &s[2] else {
            panic!()
        };
        assert!(
            matches!(&a.kind, ExprKind::Binary(BinOp::Add, l, _) if matches!(l.kind, ExprKind::Try(_)))
        );
        let Stmt::Let { init: Some(b), .. } = &s[3] else {
            panic!()
        };
        assert!(matches!(
            &b.kind,
            ExprKind::Catch {
                binding: Some(_),
                handler: CatchHandler::Block(_),
                ..
            }
        ));
        assert!(matches!(
            &s[4],
            Stmt::Expr(Expr {
                kind: ExprKind::Catch {
                    binding: None,
                    handler: CatchHandler::Block(_),
                    ..
                },
                ..
            })
        ));
        // `catch` binds like `??`: tighter than a comparison.
        let Stmt::Let { init: Some(c), .. } = &s[5] else {
            panic!()
        };
        assert!(
            matches!(&c.kind, ExprKind::Binary(BinOp::Eq, l, _) if matches!(l.kind, ExprKind::Catch { .. }))
        );
        let Stmt::Let { init: Some(d), .. } = &s[6] else {
            panic!()
        };
        let ExprKind::Binary(BinOp::Coalesce, _, rhs) = &d.kind else {
            panic!("{d:?}")
        };
        let ExprKind::Throw(value) = &rhs.kind else {
            panic!()
        };
        assert!(
            matches!(&value.kind, ExprKind::Call(callee, _) if matches!(callee.kind, ExprKind::Dot(_)))
        );
        assert!(
            matches!(&s[7], Stmt::Throw { value, .. } if matches!(value.kind, ExprKind::Dot(_)))
        );
        let Item::Fn(g) = &file.items[1] else {
            panic!()
        };
        assert!(matches!(&g.throws, Some(Throws { ty: None, .. })));
        let errs = parse_errors(
            "fn f() -> u32 throws(E) {\n}\nfn g() {\n\tf() catch {\n\t}\n\
             \tlet p = f() catch P{x: 1}\n\tlet q = f() catch (P{x: 1})\n}\n",
        );
        assert_eq!(errs.len(), 3, "{errs:?}");
        assert!(errs[0].contains("before the return type"));
        assert!(errs[1].contains("name the error"));
        assert!(errs[2].contains("in parentheses"));
    }

    #[test]
    fn methods_conventions_and_refs() {
        let file = parse_ok(
            "fn Point.scale(inout self, k: u32) {\n}\nfn Point.origin() -> Point {\n}\n\
             fn geo.Point.f(self) {\n}\nfn g(set a: u8, sink b: u8) {\n\tswap(&a[i], &p.x)\n\tlet c = x & y\n}\n",
        );
        let Item::Fn(scale) = &file.items[0] else {
            panic!()
        };
        assert!(matches!(&scale.owner, Some(TypeExpr::Named(t)) if t.name == "Point"));
        assert_eq!(scale.name.name, "scale");
        assert!(scale.params[0].is_self() && scale.params[0].convention == Convention::Inout);
        assert!(matches!(&scale.params[0].ty, TypeExpr::Named(t) if t.name == "Point"));
        let Item::Fn(origin) = &file.items[1] else {
            panic!()
        };
        assert!(origin.owner.is_some() && origin.params.is_empty());
        let Item::Fn(f) = &file.items[2] else {
            panic!()
        };
        assert!(
            matches!(&f.owner, Some(TypeExpr::Qualified(p, t)) if p.name == "geo" && t.name == "Point")
        );
        let Item::Fn(g) = &file.items[3] else {
            panic!()
        };
        assert_eq!(g.params[0].convention, Convention::Set);
        assert_eq!(g.params[1].convention, Convention::Sink);
        let Stmt::Expr(Expr {
            kind: ExprKind::Call(_, args),
            ..
        }) = &g.body.stmts[0]
        else {
            panic!()
        };
        assert!(args.iter().all(|a| matches!(a.kind, ExprKind::Ref(_))));
        // `&` between operands is still a bitwise and.
        let Stmt::Let { init: Some(c), .. } = &g.body.stmts[1] else {
            panic!()
        };
        assert!(matches!(c.kind, ExprKind::Binary(BinOp::BitAnd, ..)));

        let errs = parse_errors(
            "fn length(self) -> u32 {\n}\nfn Point.typed(self: Point) {\n}\n\
             fn Point.late(k: u32, self) {\n}\n",
        );
        assert_eq!(errs.len(), 3, "{errs:?}");
        assert!(errs[0].contains("only a method has `self`"));
        assert!(errs[1].contains("without a type"));
        assert!(errs[2].contains("must be the first parameter"));
    }

    #[test]
    fn value_patterns() {
        let file = parse_ok(
            "fn f(k: u8) {\n\tmatch k {\n\t\t0 => g()\n\t\t-1 | 'a' | MAX => g()\n\
             \t\t1..=9 | LO..=pkg.HI => g()\n\t\tadd | sub => g()\n\t\t_ => g()\n\t}\n}\n",
        );
        let Item::Fn(f) = &file.items[0] else {
            panic!()
        };
        let Stmt::Match { arms, .. } = &f.body.stmts[0] else {
            panic!()
        };
        assert!(matches!(arms[0].pattern, Pattern::Value(_)));
        let Pattern::Or(alts, _) = &arms[1].pattern else {
            panic!("{:?}", arms[1].pattern)
        };
        assert!(matches!(alts[0], Pattern::Value(_)));
        assert!(matches!(alts[2], Pattern::Variant { .. }));
        assert!(
            arms[2]
                .pattern
                .alternatives()
                .iter()
                .all(|p| matches!(p, Pattern::Range(..)))
        );
        assert_eq!(arms[3].pattern.alternatives().len(), 2);
        let errs = parse_errors("fn f(k: u8) {\n\tmatch k {\n\t\t0..9 => g()\n\t}\n}\n");
        assert_eq!(errs.len(), 1, "{errs:?}");
        assert!(errs[0].contains("includes its end"));
    }

    #[test]
    fn else_on_next_line_and_multiline_args() {
        parse_ok("fn f() {\n\tif a {\n\t\tg(1,\n\t\t\t2)\n\t}\n\telse {\n\t}\n}\n");
    }

    #[test]
    fn generics() {
        let file = parse_ok(
            "fn max[T: Ordered + Copy, U](a: T) -> T {\n\treturn f[u32, ?u8, []T, [4]u8](xs[i])\n}\n\
             fn g() {\n\tlet a = h[u32](1)\n\tlet b = s[i..]\n\tlet c = s[[2]u8]\n}\n",
        );
        let Item::Fn(max) = &file.items[0] else {
            panic!()
        };
        let names: Vec<&str> = max.generics.iter().map(|g| g.name.name.as_str()).collect();
        assert_eq!(names, ["T", "U"]);
        let bounds: Vec<&str> = max.generics[0]
            .bounds
            .iter()
            .map(|b| b.name.name.as_str())
            .collect();
        assert_eq!(bounds, ["Ordered", "Copy"]);
        assert!(max.generics[1].bounds.is_empty());
        let Stmt::Return {
            value: Some(ret), ..
        } = &max.body.stmts[0]
        else {
            panic!()
        };
        let ExprKind::Call(callee, args) = &ret.kind else {
            panic!()
        };
        // Several items, some only a type can be: generic arguments.
        let ExprKind::TypeArgs(_, items) = &callee.kind else {
            panic!("{callee:?}")
        };
        assert!(matches!(items[0], TypeArg::Expr(_)));
        assert!(items[1..].iter().all(|i| matches!(i, TypeArg::Type(_))));
        // One expression: an index, which the checker may read as a type.
        assert!(matches!(args[0].kind, ExprKind::Index(..)));
        let g = |k: usize| {
            let Item::Fn(g) = &file.items[1] else {
                panic!()
            };
            let Stmt::Let { init: Some(e), .. } = &g.body.stmts[k] else {
                panic!()
            };
            e.kind.clone()
        };
        assert!(matches!(g(0), ExprKind::Call(c, _) if matches!(c.kind, ExprKind::Index(..))));
        assert!(matches!(g(1), ExprKind::Slice(..)));
        assert!(matches!(g(2), ExprKind::TypeArgs(_, items) if items.len() == 1));

        let errs = parse_errors("fn f[]() {\n}\nstruct S[] {\n}\n");
        assert_eq!(errs.len(), 2, "{errs:?}");
        assert!(errs[0].contains("needs a parameter"));
    }

    #[test]
    fn generic_types_and_methods() {
        let file = parse_ok(
            "struct Pair[A, B: Ordered] {\n\tfirst: A\n\tsecond: B\n}\n\
             enum Either[L, R] {\n\tleft(v: L)\n\tright(v: R)\n}\n\
             fn Pair[X, Y: Copy].swap[U](self, b: geo.Box[u8, 4], c: S[N]) -> Pair[Y, X] {\n\
             \treturn Pair[Y, X]{first: self.second, second: S[2 + 2]{}}\n}\n",
        );
        let Item::Struct(pair) = &file.items[0] else {
            panic!()
        };
        assert_eq!(pair.generics.len(), 2);
        assert!(matches!(&file.items[1], Item::Enum(e) if e.generics.len() == 2));
        let Item::Fn(swap) = &file.items[2] else {
            panic!()
        };
        assert!(matches!(&swap.owner, Some(TypeExpr::Named(n)) if n.name == "Pair"));
        let names: Vec<&str> = swap
            .owner_generics
            .iter()
            .map(|g| g.name.name.as_str())
            .collect();
        assert_eq!(names, ["X", "Y"]);
        assert_eq!(swap.generics.len(), 1);
        let TypeExpr::Generic(base, args, _) = &swap.params[1].ty else {
            panic!("{:?}", swap.params[1].ty)
        };
        assert!(matches!(**base, TypeExpr::Qualified(..)));
        assert!(matches!(args[..], [TypeArg::Type(_), TypeArg::Expr(_)]));
        // `S[N]`: a name, read by the checker as a type or a value.
        assert!(
            matches!(&swap.params[2].ty, TypeExpr::Generic(_, a, _) if matches!(a[..], [TypeArg::Type(_)]))
        );
        let Stmt::Return {
            value: Some(ret), ..
        } = &swap.body.stmts[0]
        else {
            panic!()
        };
        let ExprKind::StructLit(TypeExpr::Generic(_, args, _), fields) = &ret.kind else {
            panic!("{ret:?}")
        };
        assert_eq!((args.len(), fields.len()), (2, 2));
        assert!(matches!(
            &fields[1].value.kind,
            ExprKind::StructLit(TypeExpr::Generic(_, a, _), _) if matches!(a[..], [TypeArg::Expr(_)])
        ));
    }

    #[test]
    fn traits_and_impls() {
        let file = parse_ok(
            "pub trait Shape: Eq + geo.Named {\n\ttype Unit: Copy\n\tconst MAX: usize\n\
             \tfn area(self) -> u32\n\tfn zero() -> Self\n\n\tfn name(self) -> str {\n\
             \t\treturn \"s\"\n\t}\n}\n\
             impl[A: Ordered, N] Shape for Pair[A, N] {\n\ttype Unit = u8\n\
             \tconst MAX: usize = 4\n\tfn area(self) -> u32 {\n\t\treturn 1\n\t}\n}\n\
             fn f[T: io.Writer + Shape](w: T) {\n}\n",
        );
        let Item::Trait(t) = &file.items[0] else {
            panic!()
        };
        assert!(t.is_pub && t.supers.len() == 2 && t.supers[1].pkg.is_some());
        let kinds: Vec<&str> = t
            .items
            .iter()
            .map(|i| match i {
                TraitItem::Type { .. } => "type",
                TraitItem::Const { .. } => "const",
                TraitItem::Method { default: false, .. } => "fn",
                TraitItem::Method { default: true, .. } => "default",
            })
            .collect();
        assert_eq!(kinds, ["type", "const", "fn", "fn", "default"]);
        let TraitItem::Method { decl, .. } = &t.items[2] else {
            panic!()
        };
        assert!(decl.params[0].is_self() && decl.owner.is_none());
        let Item::Impl(i) = &file.items[1] else {
            panic!()
        };
        assert_eq!((i.generics.len(), i.items.len()), (2, 3));
        assert_eq!(i.trait_.text(), "Shape");
        assert!(matches!(&i.ty, TypeExpr::Generic(..)));
        let Item::Fn(f) = &file.items[2] else {
            panic!()
        };
        let bounds: Vec<String> = f.generics[0].bounds.iter().map(Bound::text).collect();
        assert_eq!(bounds, ["io.Writer", "Shape"]);

        let errs = parse_errors(
            "trait T {\n\tfn Point.f(self)\n}\npub impl T for P {\n}\nimpl T P {\n}\n\
             trait U[X] {\n}\nimpl T for P {\n\tfn f(self)\n}\n",
        );
        assert_eq!(errs.len(), 5, "{errs:?}");
        assert!(errs[0].contains("without its type"));
        assert!(errs[1].contains("is not marked `pub`"));
        assert!(errs[2].contains("`for`"));
        assert!(errs[3].contains("generic traits"));
        assert!(errs[4].contains("expected `{`"));
    }

    #[test]
    fn comptime() {
        let file = parse_ok(
            "if comptime target.os == .linux {\n\tconst A = 1\n\tfn f() {\n\t}\n} else if comptime false {\n\
             \tcompile_error(\"x\")\n}\nelse {\n\tif comptime true {\n\t}\n}\n\
             @comptime_budget(10)\npub const B: u32 = g()\nfn h() {\n\tif comptime A == 1 {\n\t} else {\n\t}\n}\n",
        );
        assert_eq!(file.items.len(), 3);
        let Item::If(i) = &file.items[0] else {
            panic!()
        };
        assert_eq!(i.then.len(), 2);
        let Some(ItemElse::If(inner)) = &i.otherwise else {
            panic!()
        };
        assert!(matches!(inner.then[..], [Item::CompileError(_)]));
        assert!(
            matches!(&inner.otherwise, Some(ItemElse::Items(items)) if matches!(items[..], [Item::If(_)]))
        );
        let Item::Const(c) = &file.items[1] else {
            panic!()
        };
        assert!(c.is_pub && c.budget.is_some());
        let Item::Fn(h) = &file.items[2] else {
            panic!()
        };
        assert!(matches!(&h.body.stmts[0], Stmt::If(i) if i.comptime && i.otherwise.is_some()));

        let errs = parse_errors(
            "if target.os == .linux {\n}\n@inline(1)\nconst A = 1\nfn f() {\n\tif comptime let x = y {\n\t}\n}\n\
             @comptime_budget(1)\nfn g() {\n}\n",
        );
        assert_eq!(errs.len(), 4, "{errs:?}");
        assert!(errs[0].contains("only be in an `if comptime`"));
        assert!(errs[1].contains("unknown attribute `@inline`"));
        assert!(errs[2].contains("can't bind a value"));
        assert!(errs[3].contains("applies to a `const`"));
    }

    #[test]
    fn reports_and_recovers() {
        let errs = parse_errors("fn f() {\n\tlet = 1\n\treturn 1 < 2 < 3\n}\ntype S = u8\n");
        assert_eq!(errs.len(), 3, "{errs:?}");
        assert!(errs[1].contains("chained"));
        assert!(errs[2].contains("not supported"));
    }
}
