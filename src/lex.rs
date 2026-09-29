//! The lexer.
//!
//! Statements end at a newline (docs/syntax.md). As in Go, the lexer inserts a
//! [`Tok::Newline`] only after a token that can end a statement (an identifier,
//! a literal, `return`/`break`/`continue`, or a closing bracket), so a line
//! ending in an operator, `,` or `(` continues on the next line.

use std::fmt;

use crate::diag::Diagnostic;
use crate::source::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tok {
    Ident(String),
    /// An integer literal (always non-negative; `-` is a separate token).
    Int(u128),
    /// A character literal, as its Unicode scalar value.
    Char(u32),
    /// A string literal, as bytes (escapes may produce any byte).
    Str(Vec<u8>),
    Kw(Kw),
    P(P),
    Newline,
    Eof,
}

macro_rules! keywords {
    ($($variant:ident = $text:literal,)*) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum Kw { $($variant,)* }

        impl Kw {
            fn from_str(s: &str) -> Option<Kw> {
                match s { $($text => Some(Kw::$variant),)* _ => None }
            }

            pub fn as_str(self) -> &'static str {
                match self { $(Kw::$variant => $text,)* }
            }
        }
    };
}

keywords! {
    Alias = "alias",
    As = "as",
    Break = "break",
    Catch = "catch",
    Comptime = "comptime",
    Const = "const",
    Continue = "continue",
    Defer = "defer",
    Else = "else",
    Enum = "enum",
    Errdefer = "errdefer",
    False = "false",
    Fn = "fn",
    For = "for",
    If = "if",
    Impl = "impl",
    Import = "import",
    In = "in",
    Inout = "inout",
    Let = "let",
    Loop = "loop",
    Match = "match",
    None = "none",
    Package = "package",
    Pub = "pub",
    Return = "return",
    Scope = "scope",
    Set = "set",
    Sink = "sink",
    Static = "static",
    Struct = "struct",
    Throw = "throw",
    Throws = "throws",
    Trait = "trait",
    True = "true",
    Try = "try",
    Type = "type",
    Unsafe = "unsafe",
    Uses = "uses",
    Var = "var",
    Where = "where",
    While = "while",
}

macro_rules! puncts {
    ($($variant:ident = $text:literal,)*) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum P { $($variant,)* }

        impl P {
            pub fn as_str(self) -> &'static str {
                match self { $(P::$variant => $text,)* }
            }
        }

        /// Every punctuation token, longest first so the lexer can match greedily.
        const PUNCTS: &[(&str, P)] = &[$(($text, P::$variant),)*];
    };
}

puncts! {
    ShlWrap = "<<%",
    ShlAssign = "<<=",
    ShrAssign = ">>=",
    AddWrap = "+%",
    SubWrap = "-%",
    MulWrap = "*%",
    AddSat = "+|",
    SubSat = "-|",
    MulSat = "*|",
    AddAssign = "+=",
    SubAssign = "-=",
    MulAssign = "*=",
    DivAssign = "/=",
    RemAssign = "%=",
    Arrow = "->",
    FatArrow = "=>",
    DotDot = "..",
    EqEq = "==",
    NotEq = "!=",
    Le = "<=",
    Ge = ">=",
    Shl = "<<",
    Shr = ">>",
    AndAnd = "&&",
    OrOr = "||",
    Coalesce = "??",
    LParen = "(",
    RParen = ")",
    LBrace = "{",
    RBrace = "}",
    LBracket = "[",
    RBracket = "]",
    Comma = ",",
    Dot = ".",
    Colon = ":",
    Semi = ";",
    Eq = "=",
    Lt = "<",
    Gt = ">",
    Plus = "+",
    Minus = "-",
    Star = "*",
    Slash = "/",
    Percent = "%",
    Amp = "&",
    Pipe = "|",
    Caret = "^",
    Tilde = "~",
    Bang = "!",
    Question = "?",
    At = "@",
}

impl fmt::Display for Tok {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Tok::Ident(name) => write!(f, "`{name}`"),
            Tok::Int(v) => write!(f, "`{v}`"),
            Tok::Char(_) => f.write_str("character literal"),
            Tok::Str(_) => f.write_str("string literal"),
            Tok::Kw(k) => write!(f, "`{}`", k.as_str()),
            Tok::P(p) => write!(f, "`{}`", p.as_str()),
            Tok::Newline => f.write_str("end of line"),
            Tok::Eof => f.write_str("end of file"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token {
    pub tok: Tok,
    pub span: Span,
}

/// Split `src` into tokens. Lexing continues after an error so that several
/// problems can be reported at once; the token stream always ends with `Eof`.
pub fn lex(src: &str) -> (Vec<Token>, Vec<Diagnostic>) {
    let mut lx = Lexer {
        src,
        bytes: src.as_bytes(),
        pos: 0,
        toks: Vec::new(),
        diags: Vec::new(),
    };
    lx.run();
    (lx.toks, lx.diags)
}

struct Lexer<'a> {
    src: &'a str,
    bytes: &'a [u8],
    pos: usize,
    toks: Vec<Token>,
    diags: Vec<Diagnostic>,
}

impl Lexer<'_> {
    fn run(&mut self) {
        while self.pos < self.bytes.len() {
            let start = self.pos;
            let c = self.bytes[self.pos];
            match c {
                b'\n' => {
                    self.pos += 1;
                    self.newline(start);
                }
                b' ' | b'\t' | b'\r' => self.pos += 1,
                b'/' if self.peek(1) == Some(b'/') => {
                    // Line comment (including `///` doc comments, kept for later).
                    while self.pos < self.bytes.len() && self.bytes[self.pos] != b'\n' {
                        self.pos += 1;
                    }
                }
                b'0'..=b'9' => self.number(),
                b'"' => self.string(),
                b'\'' => self.char_lit(),
                c if c == b'_' || c.is_ascii_alphabetic() => self.ident(),
                c if c >= 0x80 => {
                    let ch = self.src[self.pos..].chars().next().expect("in bounds");
                    self.pos += ch.len_utf8();
                    self.error(start, format!("unexpected character `{ch}`"));
                }
                _ => self.punct(),
            }
        }
        let end = self.bytes.len();
        self.newline(end);
        self.toks.push(Token {
            tok: Tok::Eof,
            span: Span::new(end, end),
        });
    }

    fn peek(&self, ahead: usize) -> Option<u8> {
        self.bytes.get(self.pos + ahead).copied()
    }

    fn push(&mut self, tok: Tok, start: usize) {
        self.toks.push(Token {
            tok,
            span: Span::new(start, self.pos),
        });
    }

    fn error(&mut self, start: usize, msg: impl Into<String>) {
        self.diags.push(Diagnostic::error(
            Span::new(start, self.pos.max(start + 1)),
            msg,
        ));
    }

    /// Insert a statement terminator if the previous token can end a statement.
    fn newline(&mut self, at: usize) {
        let ends_statement = match self.toks.last().map(|t| &t.tok) {
            Some(Tok::Ident(_) | Tok::Int(_) | Tok::Char(_) | Tok::Str(_)) => true,
            Some(Tok::Kw(k)) => matches!(
                k,
                Kw::Return | Kw::Break | Kw::Continue | Kw::True | Kw::False | Kw::None
            ),
            Some(Tok::P(p)) => matches!(p, P::RParen | P::RBracket | P::RBrace | P::Question),
            _ => false,
        };
        if ends_statement {
            self.toks.push(Token {
                tok: Tok::Newline,
                span: Span::new(at, at),
            });
        }
    }

    fn ident(&mut self) {
        let start = self.pos;
        while self.pos < self.bytes.len()
            && (self.bytes[self.pos] == b'_' || self.bytes[self.pos].is_ascii_alphanumeric())
        {
            self.pos += 1;
        }
        let text = &self.src[start..self.pos];
        let tok = match Kw::from_str(text) {
            Some(kw) => Tok::Kw(kw),
            None => Tok::Ident(text.to_owned()),
        };
        self.push(tok, start);
    }

    fn number(&mut self) {
        let start = self.pos;
        let radix = match (self.bytes[self.pos], self.peek(1)) {
            (b'0', Some(b'x')) => 16,
            (b'0', Some(b'o')) => 8,
            (b'0', Some(b'b')) => 2,
            _ => 10,
        };
        if radix != 10 {
            self.pos += 2;
        }
        let digits_start = self.pos;
        while self.pos < self.bytes.len()
            && (self.bytes[self.pos] == b'_' || self.bytes[self.pos].is_ascii_alphanumeric())
        {
            self.pos += 1;
        }
        let digits: String = self.src[digits_start..self.pos]
            .chars()
            .filter(|&c| c != '_')
            .collect();
        if digits.is_empty() {
            self.error(start, "missing digits after the number prefix");
            self.push(Tok::Int(0), start);
            return;
        }
        match u128::from_str_radix(&digits, radix) {
            Ok(v) => self.push(Tok::Int(v), start),
            Err(e) => {
                let msg = match e.kind() {
                    std::num::IntErrorKind::PosOverflow => {
                        "integer literal is too large".to_owned()
                    }
                    _ => format!("invalid digit in base-{radix} integer literal"),
                };
                self.error(start, msg);
                self.push(Tok::Int(0), start);
            }
        }
    }

    /// Read one (possibly escaped) character inside a string or char literal.
    /// Returns bytes to append, or `None` at the end of the line/file.
    fn literal_char(&mut self) -> Option<Vec<u8>> {
        let c = *self.bytes.get(self.pos)?;
        if c == b'\n' {
            return None;
        }
        if c != b'\\' {
            let ch = self.src[self.pos..].chars().next().expect("in bounds");
            self.pos += ch.len_utf8();
            return Some(ch.to_string().into_bytes());
        }
        let esc_start = self.pos;
        self.pos += 1;
        let e = self.peek(0)?;
        self.pos += 1;
        let out = match e {
            b'n' => vec![b'\n'],
            b't' => vec![b'\t'],
            b'r' => vec![b'\r'],
            b'0' => vec![0],
            b'\\' => vec![b'\\'],
            b'\'' => vec![b'\''],
            b'"' => vec![b'"'],
            b'x' => {
                let hex = self.src.get(self.pos..self.pos + 2).unwrap_or("");
                match u8::from_str_radix(hex, 16) {
                    Ok(v) if hex.len() == 2 => {
                        self.pos += 2;
                        vec![v]
                    }
                    _ => {
                        self.error(esc_start, "`\\x` needs two hex digits");
                        vec![]
                    }
                }
            }
            b'u' => {
                let rest = &self.src[self.pos..];
                let parsed = rest
                    .strip_prefix('{')
                    .and_then(|r| r.split_once('}'))
                    .and_then(|(hex, _)| {
                        u32::from_str_radix(hex, 16)
                            .ok()
                            .map(|v| (v, hex.len() + 2))
                    })
                    .and_then(|(v, len)| char::from_u32(v).map(|c| (c, len)));
                match parsed {
                    Some((c, len)) => {
                        self.pos += len;
                        c.to_string().into_bytes()
                    }
                    None => {
                        self.error(
                            esc_start,
                            "`\\u` needs a Unicode scalar value, like `\\u{e9}`",
                        );
                        vec![]
                    }
                }
            }
            _ => {
                self.error(esc_start, format!("unknown escape `\\{}`", e as char));
                vec![]
            }
        };
        Some(out)
    }

    fn string(&mut self) {
        let start = self.pos;
        self.pos += 1;
        let mut bytes = Vec::new();
        loop {
            if self.peek(0) == Some(b'"') {
                self.pos += 1;
                break;
            }
            match self.literal_char() {
                Some(b) => bytes.extend(b),
                None => {
                    self.error(start, "unterminated string literal");
                    break;
                }
            }
        }
        self.push(Tok::Str(bytes), start);
    }

    fn char_lit(&mut self) {
        let start = self.pos;
        self.pos += 1;
        let value = match self.literal_char() {
            Some(bytes) => std::str::from_utf8(&bytes)
                .ok()
                .and_then(|s| s.chars().next())
                .map_or_else(|| bytes.first().copied().map_or(0, u32::from), u32::from),
            None => 0,
        };
        if self.peek(0) == Some(b'\'') {
            self.pos += 1;
        } else {
            self.error(
                start,
                "character literal must contain exactly one character",
            );
            while self.pos < self.bytes.len() && !matches!(self.bytes[self.pos], b'\'' | b'\n') {
                self.pos += 1;
            }
            if self.peek(0) == Some(b'\'') {
                self.pos += 1;
            }
        }
        self.push(Tok::Char(value), start);
    }

    fn punct(&mut self) {
        let start = self.pos;
        let rest = &self.src[self.pos..];
        for &(text, p) in PUNCTS {
            if rest.starts_with(text) {
                self.pos += text.len();
                self.push(Tok::P(p), start);
                return;
            }
        }
        let ch = rest.chars().next().expect("in bounds");
        self.pos += ch.len_utf8();
        self.error(start, format!("unexpected character `{ch}`"));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn toks(src: &str) -> Vec<Tok> {
        let (toks, diags) = lex(src);
        assert!(diags.is_empty(), "{diags:?}");
        toks.into_iter().map(|t| t.tok).collect()
    }

    #[test]
    fn newline_ends_statement_only_after_value() {
        use Tok::*;
        assert_eq!(
            toks("let x = a +\n\tb\n"),
            vec![
                Kw(super::Kw::Let),
                Ident("x".into()),
                P(super::P::Eq),
                Ident("a".into()),
                P(super::P::Plus),
                Ident("b".into()),
                Newline,
                Eof
            ]
        );
    }

    #[test]
    fn operators_match_longest() {
        use super::P::*;
        let t = toks("a +% b +| c <<% d");
        assert!(t.contains(&Tok::P(AddWrap)));
        assert!(t.contains(&Tok::P(AddSat)));
        assert!(t.contains(&Tok::P(ShlWrap)));
    }

    #[test]
    fn literals() {
        assert_eq!(
            toks("0x7f 1_000 0b101")[..3],
            [Tok::Int(127), Tok::Int(1000), Tok::Int(5)]
        );
        assert_eq!(toks("'0'")[0], Tok::Char('0' as u32));
        assert_eq!(toks(r#""a\n""#)[0], Tok::Str(b"a\n".to_vec()));
    }

    #[test]
    fn reports_bad_input() {
        let (_, diags) = lex("\"open\n0x");
        assert_eq!(diags.len(), 2);
    }
}
