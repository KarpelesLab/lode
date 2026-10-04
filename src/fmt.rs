//! `lode fmt`: the canonical source format (docs/syntax.md, "Formatting").
//!
//! # Design
//!
//! The formatter works on the token stream, not on the AST. It keeps the
//! author's line structure (which line each token is on, and blank lines
//! between them) and recomputes everything else: indentation from bracket
//! depth, spacing from the kinds of neighboring tokens, and the few places
//! where lines are split or joined. This is a simplified gofmt.
//!
//! An AST printer was rejected for three reasons:
//!
//! - **Comments.** The AST has no place for them. A token formatter keeps
//!   every comment where it was, between the same two tokens.
//! - **New syntax.** Most new constructs (`for`, arrays, `match`, ...) are made
//!   of tokens and brackets the formatter already knows, so they format
//!   correctly without changes here. An AST printer needs a case for every
//!   node and silently drops anything it doesn't print.
//! - **Safety.** Since the formatter only moves whitespace, it can check its
//!   own output: the result is lexed again and its tokens compared with the
//!   input's (see [`same_program`]). If they differ, the file is left alone.
//!
//! The input must still lex and parse without errors, so the formatter never
//! touches a file the compiler wouldn't accept syntactically.
//!
//! # The canonical form
//!
//! - One tab per indentation level: one per open `{`, and one per line
//!   continuing a statement or opening a `(` or `[` that stays open (but not
//!   both for the same line: `if a && (b ||` continues with one more tab).
//!   A block is one level deeper than the line starting its header, even
//!   when the header spans several lines; its `}` aligns with that line.
//! - One space between tokens, except: none inside `()`/`[]`, before `,`, `:`,
//!   `;`, `.` and after `.`; none around `..` and `..=`; none after a unary
//!   operator; none before a call's `(` or an index's `[`; none inside a type
//!   prefix like `[4]u8` or `[]*u8`.
//! - `;` between statements becomes a line break. A block written on one line
//!   (`if a { return 1 }`) is split so each statement has its own line.
//!   A `{` glued to a name (`Point{x: 1}`) is a literal, not a block, and
//!   keeps its lines, unless it follows `if`, `while`, `fn` and the like at the
//!   same bracket depth: as in Go, that `{` always starts a block.
//! - `else` joins the `}` before it: `} else {`.
//! - At most one blank line in a row; none at the start or end of a block or
//!   file. One blank line after `package` and after the imports.
//! - Comments keep their text and line. A run of trailing comments on
//!   consecutive lines at the same indentation is aligned with spaces.
//! - No trailing whitespace; the file ends with exactly one newline.

use crate::diag::Diagnostic;
use crate::lex::{Kw, P, Tok, Token, lex, lex_with_comments};
use crate::parse::parse;
use crate::source::{FileId, Span};

/// Format the text of source file `file`. Returns the canonical text, or the
/// errors that prevent formatting (the file must lex and parse).
pub fn format(src: &str, file: FileId) -> Result<String, Vec<Diagnostic>> {
    let (toks, comments, diags) = lex_with_comments(src, file);
    if diags.iter().any(Diagnostic::is_error) {
        return Err(diags);
    }
    let (_, diags) = parse(toks.clone(), file);
    if diags.iter().any(Diagnostic::is_error) {
        return Err(diags);
    }
    format_tokens(src, &toks, &comments).map_err(|msg| {
        vec![Diagnostic::error(
            Span::new(file, 0, 0),
            format!("internal formatter error, the file is left unchanged: {msg}"),
        )]
    })
}

/// Format already-lexed source, then check the result is the same program.
fn format_tokens(src: &str, toks: &[Token], comments: &[Span]) -> Result<String, String> {
    let items = items(src, toks, comments);
    let items = restructure(items)?;
    let out = render(&items)?;
    if !same_program(src, &out) {
        return Err("the output's tokens differ from the input's".to_owned());
    }
    Ok(out)
}

// --- items ---------------------------------------------------------------------

#[derive(Clone, Debug)]
struct TokInfo<'a> {
    tok: Tok,
    text: &'a str,
    /// No whitespace or comment between this token and the previous one.
    glued: bool,
    /// The lexer ended a statement after this token (or a `;` follows it).
    ends_stmt: bool,
    /// For `{` and `}`: the braces of a literal, not a block.
    literal: bool,
}

#[derive(Clone, Debug)]
enum Item<'a> {
    Tok(TokInfo<'a>),
    /// A `//` comment, without trailing whitespace.
    Comment(&'a str),
    /// Line breaks: 1 ends the line, 2 also leaves one blank line.
    Break(usize),
}

fn is_p(item: Option<&Item<'_>>, p: P) -> bool {
    matches!(item, Some(Item::Tok(t)) if t.tok == Tok::P(p))
}

fn is_opener(tok: &Tok) -> bool {
    matches!(tok, Tok::P(P::LBrace | P::LParen | P::LBracket))
}

fn is_closer(tok: &Tok) -> bool {
    matches!(tok, Tok::P(P::RBrace | P::RParen | P::RBracket))
}

/// The tokens and comments of `src` in order, with the line breaks between
/// them. Newline tokens become the `ends_stmt` flag of the token before.
fn items<'a>(src: &'a str, toks: &[Token], comments: &[Span]) -> Vec<Item<'a>> {
    let mut spans: Vec<(Span, Option<&Token>)> = comments.iter().map(|&s| (s, None)).collect();
    spans.extend(toks.iter().map(|t| (t.span, Some(t))));
    spans.sort_by_key(|(s, t)| (s.start, t.is_some()));
    let mut items = Vec::new();
    let mut last_tok: Option<usize> = None;
    let mut prev_end: Option<usize> = None;
    for (span, tok) in spans {
        let (start, end) = (span.start as usize, span.end as usize);
        match tok.map(|t| &t.tok) {
            Some(Tok::Newline) => {
                if let Some(Item::Tok(t)) = last_tok.and_then(|i| items.get_mut(i)) {
                    t.ends_stmt = true;
                }
                continue;
            }
            Some(Tok::Eof) => continue,
            _ => {}
        }
        if let Some(prev) = prev_end {
            let breaks = src[prev..start].matches('\n').count();
            if breaks > 0 {
                items.push(Item::Break(breaks));
            }
        }
        let text = &src[start..end];
        match tok {
            Some(t) => {
                last_tok = Some(items.len());
                items.push(Item::Tok(TokInfo {
                    tok: t.tok.clone(),
                    text,
                    glued: prev_end == Some(start),
                    ends_stmt: false,
                    literal: false,
                }));
            }
            None => items.push(Item::Comment(text.trim_end())),
        }
        prev_end = Some(end);
    }
    items
}

fn push_break(out: &mut Vec<Item<'_>>, n: usize) {
    match out.last_mut() {
        None => {}
        Some(Item::Break(m)) => *m = (*m).max(n),
        Some(_) => out.push(Item::Break(n)),
    }
}

/// Decide where lines start and end: split `;`-separated statements and
/// one-line blocks, join `} else`, and limit blank lines.
fn restructure(items: Vec<Item<'_>>) -> Result<Vec<Item<'_>>, String> {
    let mut out: Vec<Item<'_>> = Vec::with_capacity(items.len());
    // Open brackets: (bracket, literal).
    let mut stack: Vec<(P, bool)> = Vec::new();
    // Bracket depths of the keywords whose `{` starts a block (as in Go, a
    // `{` there is never a literal: `if x == p {`).
    let mut headers: Vec<usize> = Vec::new();
    for i in 0..items.len() {
        let next = items.get(i + 1);
        if let Item::Tok(t) = &items[i] {
            match t.tok {
                Tok::Kw(
                    Kw::If
                    | Kw::Else
                    | Kw::While
                    | Kw::For
                    | Kw::Loop
                    | Kw::Match
                    | Kw::Unsafe
                    | Kw::Fn
                    | Kw::Struct
                    | Kw::Enum
                    | Kw::Trait
                    | Kw::Impl
                    | Kw::Catch
                    | Kw::Defer
                    | Kw::Errdefer,
                ) => headers.push(stack.len()),
                Tok::P(P::RBrace | P::RParen | P::RBracket) => {
                    headers.retain(|&d| d < stack.len());
                }
                _ => {}
            }
        }
        match &items[i] {
            Item::Tok(t)
                if t.tok == Tok::P(P::Semi) && stack.last().is_none_or(|b| b.0 == P::LBrace) =>
            {
                // A statement separator: the next statement goes on its own line.
                if let Some(Item::Tok(prev)) = out.last_mut() {
                    prev.ends_stmt = true;
                }
                if matches!(next, Some(Item::Tok(_))) {
                    push_break(&mut out, 1);
                }
            }
            Item::Tok(t) if t.tok == Tok::P(P::LBrace) => {
                let followed_by_tok = matches!(next, Some(Item::Tok(_)));
                // `Point{x: 1}` or `[2]u8{1, 2}`: glued to a type name.
                let after_type = matches!(out.last(),
                    Some(Item::Tok(p)) if matches!(p.tok, Tok::Ident(_) | Tok::P(P::RBracket)));
                let header = headers.last() == Some(&stack.len());
                while headers.last() == Some(&stack.len()) {
                    headers.pop(); // `else if`
                }
                let literal = !header && t.glued && after_type;
                stack.push((P::LBrace, literal));
                out.push(Item::Tok(TokInfo {
                    literal,
                    ..t.clone()
                }));
                if !literal && followed_by_tok && !is_p(next, P::RBrace) {
                    push_break(&mut out, 1);
                }
            }
            Item::Tok(t) if is_opener(&t.tok) => {
                let Tok::P(p) = t.tok else { unreachable!() };
                stack.push((p, false));
                out.push(items[i].clone());
            }
            Item::Tok(t) if is_closer(&t.tok) => {
                let Tok::P(close) = t.tok else { unreachable!() };
                let (open, literal) = stack.pop().ok_or("unbalanced brackets")?;
                let want = match open {
                    P::LBrace => P::RBrace,
                    P::LParen => P::RParen,
                    _ => P::RBracket,
                };
                if close != want {
                    return Err("unbalanced brackets".to_owned());
                }
                if close == P::RBrace && !literal && !is_p(out.last(), P::LBrace) {
                    // A block's `}` is on its own line.
                    push_break(&mut out, 1);
                }
                out.push(Item::Tok(TokInfo {
                    literal,
                    ..t.clone()
                }));
            }
            Item::Break(n) => {
                let after_opener = matches!(out.last(), Some(Item::Tok(t)) if is_opener(&t.tok));
                let before_closer = matches!(next, Some(Item::Tok(t)) if is_closer(&t.tok));
                let before_else = matches!(next, Some(Item::Tok(t)) if t.tok == Tok::Kw(Kw::Else));
                if before_else && is_p(out.last(), P::RBrace) {
                    continue; // `} else`
                }
                let n = if after_opener || before_closer {
                    1
                } else {
                    (*n).min(2)
                };
                push_break(&mut out, n);
            }
            item => out.push(item.clone()),
        }
        if let Item::Tok(t) = &items[i]
            && t.ends_stmt
        {
            // A header that never reached its `{`, like a `fn` type.
            headers.retain(|&d| d < stack.len());
        }
    }
    if !stack.is_empty() {
        return Err("unbalanced brackets".to_owned());
    }
    while matches!(out.last(), Some(Item::Break(_))) {
        out.pop();
    }
    separate_header(&mut out);
    Ok(out)
}

/// Leave one blank line after the `package` line and after the last import.
fn separate_header(items: &mut [Item<'_>]) {
    let mut depth = 0usize;
    let mut first_on_line: Option<Tok> = None;
    for i in 0..items.len() {
        match &items[i] {
            Item::Tok(t) => {
                if first_on_line.is_none() && depth == 0 {
                    first_on_line = Some(t.tok.clone());
                }
                if is_opener(&t.tok) {
                    depth += 1;
                } else if is_closer(&t.tok) {
                    depth = depth.saturating_sub(1);
                }
            }
            Item::Comment(_) => {}
            Item::Break(_) => {
                let next_tok = items[i + 1..].iter().find_map(|it| match it {
                    Item::Tok(t) => Some(&t.tok),
                    _ => None,
                });
                let blank = match first_on_line.take() {
                    Some(Tok::Kw(Kw::Package)) => true,
                    Some(Tok::Kw(Kw::Import)) => {
                        next_tok.is_some_and(|t| *t != Tok::Kw(Kw::Import))
                    }
                    _ => false,
                };
                if blank && let Item::Break(n) = &mut items[i] {
                    *n = 2;
                }
            }
        }
    }
}

// --- rendering -----------------------------------------------------------------

#[derive(Debug, Default)]
struct Line {
    indent: usize,
    code: String,
    comment: Option<String>,
    blank: bool,
}

/// An open bracket while rendering.
struct Frame {
    /// Indentation of the lines inside the brackets.
    content: usize,
    /// Indentation of a line starting with the closing bracket.
    close: usize,
    /// A `[` in prefix position (an array type or literal, not an index).
    prefix: bool,
    /// A line has started inside the brackets. Until then, the brackets'
    /// own indentation already marks a line continuing the first element
    /// (`if a && (b ||` then `c) {`), so it gets no extra tab.
    lined: bool,
}

/// The previous token on the current line.
struct Prev {
    tok: Tok,
    text: String,
    /// It can end an operand, so a following `-` or `*` is binary.
    operand_end: bool,
    /// Nothing may follow it with a space (a unary operator, `(`, `.`, ...).
    glue_after: bool,
    /// A `]` closing a prefix `[`, as in `[4]u8`.
    prefix_close: bool,
    /// The statement ends after it.
    ends_stmt: bool,
}

fn render(items: &[Item<'_>]) -> Result<String, String> {
    let mut lines: Vec<Line> = Vec::new();
    let mut stack: Vec<Frame> = Vec::new();
    let mut line: Option<Line> = None;
    // The indentation of the current line, without continuation.
    let mut line_base = 0;
    // For each bracket depth (the top level, then one per open bracket): the
    // indentation of the line that started the current statement or element
    // at that depth. A block's lines are one level deeper than the line that
    // starts its header, however many lines the header takes.
    let mut bases: Vec<usize> = vec![0];
    let mut prev: Option<Prev> = None;
    // The last token line ended in the middle of a statement.
    let mut continuing = false;

    for item in items {
        match item {
            Item::Tok(t) => {
                let l = line.get_or_insert_with(|| {
                    let content = stack.last().map_or(0, |f| f.content);
                    let lined = stack.last().is_none_or(|f| f.lined);
                    let indent = if is_closer(&t.tok) {
                        stack.last().map_or(0, |f| f.close)
                    } else if continuing && lined {
                        content + 1
                    } else {
                        content
                    };
                    if !is_closer(&t.tok) {
                        if let Some(f) = stack.last_mut() {
                            f.lined = true;
                        }
                        if !continuing && let Some(b) = bases.last_mut() {
                            *b = content;
                        }
                    }
                    line_base = if is_closer(&t.tok) { indent } else { content };
                    Line {
                        indent,
                        ..Line::default()
                    }
                });
                let unary = match &t.tok {
                    // `??` in a type, as in `??u8`, is two prefix `?`, and
                    // a `.` that doesn't follow an operand starts a
                    // variant: `throw .empty`.
                    Tok::P(
                        P::Minus
                        | P::Bang
                        | P::Tilde
                        | P::Star
                        | P::Amp
                        | P::Question
                        | P::Coalesce,
                    ) => prev
                        .as_ref()
                        .is_none_or(|p| !p.operand_end || (p.prefix_close && t.glued)),
                    Tok::P(P::Dot) => prev.as_ref().is_none_or(|p| !p.operand_end),
                    _ => false,
                };
                if let Some(p) = &prev
                    && space_before(p, t, unary)
                {
                    l.code.push(' ');
                } else if let Some(p) = &prev
                    && would_merge(&p.text, t.text)
                {
                    l.code.push(' ');
                }
                l.code.push_str(t.text);

                let mut prefix_close = false;
                if is_opener(&t.tok) {
                    let base = *bases.last().ok_or("unbalanced brackets")?;
                    let (content, close) = if t.tok != Tok::P(P::LBrace) {
                        (l.indent + 1, l.indent)
                    } else if t.literal {
                        (line_base + 1, line_base)
                    } else {
                        (base + 1, base)
                    };
                    bases.push(base);
                    stack.push(Frame {
                        content,
                        close,
                        prefix: prev
                            .as_ref()
                            .is_none_or(|p| !p.operand_end || p.prefix_close),
                        lined: false,
                    });
                } else if is_closer(&t.tok) {
                    let frame = stack.pop().ok_or("unbalanced brackets")?;
                    bases.pop();
                    prefix_close = t.tok == Tok::P(P::RBracket) && frame.prefix;
                }
                let postfix_q = t.tok == Tok::P(P::Question) && !unary;
                prev = Some(Prev {
                    operand_end: postfix_q
                        || matches!(
                            t.tok,
                            Tok::Ident(_)
                                | Tok::Int(_)
                                | Tok::Char(_)
                                | Tok::Str(_)
                                | Tok::Kw(Kw::True | Kw::False | Kw::None)
                                | Tok::P(P::RParen | P::RBracket)
                        )
                        || (t.tok == Tok::P(P::RBrace) && t.literal),
                    glue_after: unary
                        || (t.tok == Tok::P(P::LBrace) && t.literal)
                        || matches!(
                            t.tok,
                            Tok::P(
                                P::LParen | P::LBracket | P::Dot | P::DotDot | P::DotDotEq | P::At
                            )
                        ),
                    prefix_close,
                    ends_stmt: t.ends_stmt,
                    tok: t.tok.clone(),
                    text: t.text.to_owned(),
                });
            }
            Item::Comment(text) => match &mut line {
                Some(l) => l.comment = Some((*text).to_owned()),
                None => {
                    let content = stack.last().map_or(0, |f| f.content);
                    let lined = stack.last().is_none_or(|f| f.lined);
                    lines.push(Line {
                        indent: content + usize::from(continuing && lined),
                        comment: Some((*text).to_owned()),
                        ..Line::default()
                    });
                }
            },
            Item::Break(n) => {
                if let Some(l) = line.take() {
                    lines.push(l);
                }
                if let Some(p) = prev.take() {
                    continuing = !p.ends_stmt && !is_opener(&p.tok) && p.tok != Tok::P(P::Comma);
                }
                if *n > 1 {
                    lines.push(Line {
                        blank: true,
                        ..Line::default()
                    });
                }
            }
        }
    }
    if let Some(l) = line.take() {
        lines.push(l);
    }
    align_comments(&mut lines);

    let mut out = String::new();
    for l in &lines {
        if !l.blank {
            out.extend(std::iter::repeat_n('\t', l.indent));
            out.push_str(&l.code);
            if let Some(c) = &l.comment {
                if !l.code.is_empty() {
                    out.push(' ');
                }
                out.push_str(c);
            }
        }
        out.push('\n');
    }
    Ok(out)
}

/// Whether `cur` is separated from the previous token on its line by a space.
fn space_before(prev: &Prev, cur: &TokInfo<'_>, cur_unary: bool) -> bool {
    if prev.glue_after {
        return false;
    }
    match &cur.tok {
        Tok::P(
            P::Comma
            | P::Semi
            | P::RParen
            | P::RBracket
            | P::RBrace
            | P::DotDot
            | P::DotDotEq
            | P::Colon,
        ) => {
            return false;
        }
        Tok::P(P::Dot) if !cur_unary => return false,
        Tok::P(P::Question) if !cur_unary => return false,
        Tok::P(P::LParen) => {
            return !matches!(
                prev.tok,
                Tok::Ident(_) | Tok::Kw(Kw::Fn | Kw::Throws) | Tok::P(P::RParen | P::RBracket)
            );
        }
        Tok::P(P::LBracket) => {
            return !matches!(
                prev.tok,
                Tok::Ident(_) | Tok::Str(_) | Tok::P(P::RParen | P::RBracket)
            );
        }
        Tok::P(P::LBrace) => return !cur.literal,
        _ => {}
    }
    if prev.prefix_close
        && cur.glued
        && matches!(
            cur.tok,
            Tok::Ident(_)
                | Tok::Kw(Kw::Fn)
                | Tok::P(P::Star | P::Question | P::Coalesce | P::LBracket)
        )
    {
        return false;
    }
    true
}

/// Whether two tokens written without a space between them would lex as
/// something else (like `/` `/` or `-` `>`).
fn would_merge(a: &str, b: &str) -> bool {
    let joined = format!("{a}{b}");
    let (toks, diags) = lex(&joined, 0);
    let toks: Vec<&Token> = toks
        .iter()
        .filter(|t| !matches!(t.tok, Tok::Newline | Tok::Eof))
        .collect();
    !diags.is_empty() || toks.len() != 2 || toks[0].span.end as usize != a.len()
}

/// Align the trailing comments of consecutive lines at the same indentation.
fn align_comments(lines: &mut [Line]) {
    let has_trailing = |l: &Line| !l.blank && !l.code.is_empty() && l.comment.is_some();
    let mut i = 0;
    while i < lines.len() {
        if !has_trailing(&lines[i]) {
            i += 1;
            continue;
        }
        let mut j = i + 1;
        while j < lines.len() && has_trailing(&lines[j]) && lines[j].indent == lines[i].indent {
            j += 1;
        }
        let width = lines[i..j]
            .iter()
            .map(|l| l.code.chars().count())
            .max()
            .unwrap_or(0);
        for l in &mut lines[i..j] {
            let pad = width - l.code.chars().count();
            l.code.extend(std::iter::repeat_n(' ', pad));
        }
        i = j;
    }
}

// --- checking ------------------------------------------------------------------

/// The tokens (with their text) and comments of a program, with the differences the formatter
/// may introduce normalized away: a `;` between statements is a line end,
/// and line ends after `{`, before `}` or `else`, or repeated, don't count.
fn normalized(src: &str) -> Option<Normalized<'_>> {
    let (toks, comments, diags) = lex_with_comments(src, 0);
    if !diags.is_empty() {
        return None;
    }
    let mut stack = Vec::new();
    let mut out: Vec<(Tok, &str)> = Vec::new();
    for t in &toks {
        let text = &src[t.span.start as usize..t.span.end as usize];
        let tok = match &t.tok {
            Tok::P(P::Semi) if stack.last().is_none_or(|&p| p == P::LBrace) => Tok::Newline,
            Tok::P(p @ (P::LBrace | P::LParen | P::LBracket)) => {
                stack.push(*p);
                t.tok.clone()
            }
            Tok::P(P::RBrace | P::RParen | P::RBracket) => {
                stack.pop();
                t.tok.clone()
            }
            Tok::Eof => continue,
            other => other.clone(),
        };
        if tok == Tok::Newline {
            if matches!(
                out.last(),
                None | Some((Tok::Newline | Tok::P(P::LBrace), _))
            ) {
                continue;
            }
            out.push((Tok::Newline, ""));
            continue;
        }
        let n = out.len();
        let drop_newline = match tok {
            Tok::P(P::RBrace) => true,
            Tok::Kw(Kw::Else) => n >= 2 && out[n - 2].0 == Tok::P(P::RBrace),
            _ => false,
        };
        if drop_newline && matches!(out.last(), Some((Tok::Newline, _))) {
            out.pop();
        }
        out.push((tok, text));
    }
    let comments = comments
        .iter()
        .map(|s| src[s.start as usize..s.end as usize].trim_end())
        .collect();
    Some(Normalized {
        toks: out,
        comments,
    })
}

#[derive(PartialEq)]
struct Normalized<'a> {
    toks: Vec<(Tok, &'a str)>,
    comments: Vec<&'a str>,
}

/// Whether `formatted` has the same tokens and comments as `src`.
fn same_program(src: &str, formatted: &str) -> bool {
    match (normalized(src), normalized(formatted)) {
        (Some(a), Some(b)) => a == b,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Format `src`, which must parse, and check the result is stable.
    fn fmt(src: &str) -> String {
        let out = format(src, 0).unwrap_or_else(|d| panic!("{d:?}"));
        assert_eq!(
            format(&out, 0).expect("formats again"),
            out,
            "not idempotent"
        );
        out
    }

    /// Format `src` without requiring the parser to accept it, for syntax the
    /// compiler doesn't support yet.
    fn fmt_tokens(src: &str) -> String {
        let (toks, comments, diags) = lex_with_comments(src, 0);
        assert!(diags.is_empty(), "{diags:?}");
        let out = format_tokens(src, &toks, &comments).expect("formats");
        let (toks, comments, _) = lex_with_comments(&out, 0);
        assert_eq!(
            format_tokens(&out, &toks, &comments).unwrap(),
            out,
            "not idempotent"
        );
        out
    }

    /// The tokens of `src` with their text, without line ends and `;`.
    fn tokens(src: &str) -> Vec<(Tok, String)> {
        let (toks, _) = lex(src, 0);
        toks.iter()
            .filter(|t| !matches!(t.tok, Tok::Newline | Tok::P(P::Semi)))
            .map(|t| {
                let text = &src[t.span.start as usize..t.span.end as usize];
                (t.tok.clone(), text.to_owned())
            })
            .collect()
    }

    #[test]
    fn spacing_and_signatures() {
        assert_eq!(
            fmt("package main\nfn  add( a:u32,b : *u8 )->u32{\n  return a+%b*2\n}\n"),
            "package main\n\nfn add(a: u32, b: *u8) -> u32 {\n\treturn a +% b * 2\n}\n"
        );
        assert_eq!(
            fmt("fn f(x: i32) -> bool {\n\treturn -x<0&&!g( x ) ||x  ==  -1\n}\n"),
            "fn f(x: i32) -> bool {\n\treturn -x < 0 && !g(x) || x == -1\n}\n"
        );
        assert_eq!(
            fmt("fn f() {\n\tx  +=  u8( a )-1\n\tp = p+done\n}\n"),
            "fn f() {\n\tx += u8(a) - 1\n\tp = p + done\n}\n"
        );
        assert_eq!(
            fmt("fn f() {\n\tmatch k {\n\t\t1 ..= 9|-1=>g()\n\t\tadd|sub => g()\n\t}\n}\n"),
            "fn f() {\n\tmatch k {\n\t\t1..=9 | -1 => g()\n\t\tadd | sub => g()\n\t}\n}\n"
        );
        assert_eq!(
            fmt("fn f() {\n\tx+%=1\n\ty|=2\n\tz<<%=3\n\ta.b[i]*|=c\n\tk^=-1\n}\n"),
            "fn f() {\n\tx +%= 1\n\ty |= 2\n\tz <<%= 3\n\ta.b[i] *|= c\n\tk ^= -1\n}\n"
        );
        // `??` is a prefix in a type and a binary operator in an expression.
        assert_eq!(
            fmt("fn f(o: ?? u8, p: [2]?u8) -> u8 {\n\treturn o??p[0]?? 1\n}\n"),
            "fn f(o: ??u8, p: [2]?u8) -> u8 {\n\treturn o ?? p[0] ?? 1\n}\n"
        );
    }

    #[test]
    fn errors_and_variants() {
        assert_eq!(
            fmt(
                "fn f() throws ( E ) -> u32 {\n\tlet x = try g( )\n\tlet y = g() catch e{\n\
                 return 0\n}\n\tthrow . bad\n\tdefer{h()}\n\tg() catch _ {}\n\
                 \tlet s: S = .a(1,.b)\n\tlet n = [1, 2].len\n\treturn o ?? throw .c\n}\n"
            ),
            "fn f() throws(E) -> u32 {\n\tlet x = try g()\n\tlet y = g() catch e {\n\
             \t\treturn 0\n\t}\n\tthrow .bad\n\tdefer {\n\t\th()\n\t}\n\tg() catch _ {}\n\
             \tlet s: S = .a(1, .b)\n\tlet n = [1, 2].len\n\treturn o ?? throw .c\n}\n"
        );
    }

    #[test]
    fn header_groups() {
        assert_eq!(
            fmt("\n\npackage main\nimport \"std/io\"\nimport os \"std/os\"\nconst X = 1\n\n\n"),
            "package main\n\nimport \"std/io\"\nimport os \"std/os\"\n\nconst X = 1\n"
        );
        // Comments before `package` stay first, attached to it.
        assert_eq!(
            fmt("// exit: 0\n/// The package.\npackage main\n// About io.\nimport \"std/io\"\n"),
            "// exit: 0\n/// The package.\npackage main\n\n// About io.\nimport \"std/io\"\n"
        );
    }

    #[test]
    fn const_items() {
        assert_eq!(
            fmt("const  A=1\npub const B:isize = -A\nconst C: u8 = (1+2)*3\n"),
            "const A = 1\npub const B: isize = -A\nconst C: u8 = (1 + 2) * 3\n"
        );
    }

    #[test]
    fn comments_are_kept() {
        let src = "\
/// Doc comment.
///
/// More.
pub fn f()  {   // trailing on the opener
    // own line
  let x = 1 // first
        let longer_name = 2   // second

    return // after return
  // before the brace
}
// at the end   \n";
        assert_eq!(
            fmt(src),
            "\
/// Doc comment.
///
/// More.
pub fn f() { // trailing on the opener
\t// own line
\tlet x = 1           // first
\tlet longer_name = 2 // second

\treturn // after return
\t// before the brace
}
// at the end
"
        );
    }

    #[test]
    fn blank_lines() {
        assert_eq!(
            fmt("fn a() {\n\n\tlet x = 1\n\n\n\n\tlet y = 2\n\n}\n\n\n\nfn b() {\n}\nfn c() {}"),
            "fn a() {\n\tlet x = 1\n\n\tlet y = 2\n}\n\nfn b() {\n}\nfn c() {}\n"
        );
        assert_eq!(fmt(""), "");
        assert_eq!(fmt("\n\n// only\n\n"), "// only\n");
    }

    #[test]
    fn nested_blocks_and_unsafe() {
        assert_eq!(
            fmt("fn f() {\nunsafe {\nvar p = s.ptr\nwhile left>0 {\nloop {\nbreak\n}\n}\n}\n}\n"),
            "fn f() {\n\tunsafe {\n\t\tvar p = s.ptr\n\t\twhile left > 0 {\n\t\t\tloop {\n\
             \t\t\t\tbreak\n\t\t\t}\n\t\t}\n\t}\n}\n"
        );
        assert_eq!(
            fmt("unsafe fn raw() {\n}\nfn f() {\n\tunsafe { syscall(60, 0) }\n}\n"),
            "unsafe fn raw() {\n}\nfn f() {\n\tunsafe {\n\t\tsyscall(60, 0)\n\t}\n}\n"
        );
    }

    #[test]
    fn one_statement_per_line() {
        assert_eq!(
            fmt("fn f() {\n\tlet x = 1; let y = 2;\n\tif x<y{return 1}\n\tloop { break }\n}\n"),
            "fn f() {\n\tlet x = 1\n\tlet y = 2\n\tif x < y {\n\t\treturn 1\n\t}\n\tloop {\n\
             \t\tbreak\n\t}\n}\n"
        );
    }

    #[test]
    fn if_else_chains() {
        assert_eq!(
            fmt("fn f() {\n\tif a {\n\t\tx()\n\t}\n\telse if b {\n\t\ty()\n\t}   else{z()}\n}\n"),
            "fn f() {\n\tif a {\n\t\tx()\n\t} else if b {\n\t\ty()\n\t} else {\n\t\tz()\n\t}\n}\n"
        );
        assert_eq!(
            fmt("fn f() {\n\tif a { x() } else { y() }\n}\n"),
            "fn f() {\n\tif a {\n\t\tx()\n\t} else {\n\t\ty()\n\t}\n}\n"
        );
        // A comment between `}` and `else` keeps them on separate lines.
        let src = "fn f() {\n\tif a {\n\t\tx()\n\t}\n\t// otherwise\n\telse {\n\t\ty()\n\t}\n}\n";
        assert_eq!(fmt(src), src);
    }

    #[test]
    fn multi_line_arguments_and_continuations() {
        assert_eq!(
            fmt("fn f() {\nio.print(\"x\",\n        g(1,\n2))\nh(\na,\nb,\n)\n}\n"),
            "fn f() {\n\tio.print(\"x\",\n\t\tg(1,\n\t\t\t2))\n\th(\n\t\ta,\n\t\tb,\n\t)\n}\n"
        );
        assert_eq!(
            fmt(
                "fn f() -> bool {\nlet x = a +\n      b +\n  c\nif x > 1 &&\ny < 2 {\n\
                 return true\n}\nreturn false\n}\n"
            ),
            "fn f() -> bool {\n\tlet x = a +\n\t\tb +\n\t\tc\n\tif x > 1 &&\n\t\ty < 2 {\n\
             \t\treturn true\n\t}\n\treturn false\n}\n"
        );
        assert_eq!(
            fmt("fn f(\na: u32,\n  b: u32,\n) -> u32 {\nreturn a\n}\n"),
            "fn f(\n\ta: u32,\n\tb: u32,\n) -> u32 {\n\treturn a\n}\n"
        );
    }

    /// A block after a header spanning several lines is indented one level
    /// from the line starting the header, and each continuation line of the
    /// header gets exactly one extra tab (as in gofmt).
    #[test]
    fn multi_line_headers() {
        let canonical = [
            // A signature broken after a `,`.
            "fn add3(a: u32,\n\tb: u32) -> u32 {\n\treturn a +% b\n}\n",
            // A condition broken after an operator, without brackets.
            "fn f() -> u8 {\n\tif g(1) == 3 &&\n\t\tg(2) == 4 {\n\t\treturn 0\n\t}\n\treturn 1\n}\n",
            // A condition broken inside a `(` opened on the header's line.
            "fn f(a: u8) -> u8 {\n\tif a == 1 && (a == 2 ||\n\t\ta == 1) {\n\t\treturn 0\n\t}\n\
             \treturn 1\n}\n",
            "fn f(a: u8) {\n\twhile a < 9 && (a == 2 ||\n\t\ta == 1) &&\n\t\ta > 0 {\n\
             \t\ta += 1\n\t}\n}\n",
            // Inside a `(` opened at the end of a line, continuation adds one.
            "fn f() {\n\tg(\n\t\ta +\n\t\t\tb,\n\t\tc)\n}\n",
            "fn f() {\n\tg(a +\n\t\tb,\n\t\tc +\n\t\t\td)\n}\n",
            // Nested: multi-line headers inside a block with a multi-line header.
            "fn f(a: u32,\n\tb: u32) {\n\twhile a < b &&\n\t\tb > 0 {\n\
             \t\tif (a == 1 ||\n\t\t\ta == 2) {\n\t\t\tg(a,\n\t\t\t\tb)\n\t\t} else if a == 3 ||\n\
             \t\t\ta == 4 {\n\t\t\tbreak\n\t\t}\n\t}\n}\n",
        ];
        for src in canonical {
            assert_eq!(fmt(src), src);
        }
        // Over-indented input, as the formatter used to produce it.
        assert_eq!(
            fmt("fn add3(a: u32,\n\tb: u32) -> u32 {\n\t\treturn a +% b\n\t}\n"),
            canonical[0]
        );
        assert_eq!(
            fmt(
                "fn f(a: u8) -> u8 {\n\tif a == 1 && (a == 2 ||\n\t\t\ta == 1) {\n\t\t\treturn 0\n\
                 \t\t}\n\treturn 1\n}\n"
            ),
            canonical[2]
        );
        // Unindented input.
        assert_eq!(
            fmt(
                "fn f(a: u32,\nb: u32) {\nwhile a < b &&\nb > 0 {\nif (a == 1 ||\na == 2) {\n\
                 g(a,\nb)\n} else if a == 3 ||\na == 4 {\nbreak\n}\n}\n}\n"
            ),
            canonical[6]
        );
    }

    #[test]
    fn syntax_the_parser_does_not_have_yet() {
        assert_eq!(
            fmt_tokens(
                "fn f(xs: []u8, m: [ 4 ][4]*u8) {\n\tvar a: [16]u8 = [0 ; 16]\n\
                 \tlet b = [1,2, 3]\n\tfor i in 0 .. n { a[ i ] = xs[i]*2 }\n\
                 \tlet p = Point{x: 1, y: 2}\n\tlet q: ?u8 = g()?\n\tmatch s {\n\
                 \t\tcircle(_, r) => return r\n\t}\n}\nstruct Point {\n\tx: f32\n}\n\
                 fn max[T: Ordered](a: T) -> T {\n}\n"
            ),
            "fn f(xs: []u8, m: [4][4]*u8) {\n\tvar a: [16]u8 = [0; 16]\n\
             \tlet b = [1, 2, 3]\n\tfor i in 0..n {\n\t\ta[i] = xs[i] * 2\n\t}\n\
             \tlet p = Point{x: 1, y: 2}\n\tlet q: ?u8 = g()?\n\tmatch s {\n\
             \t\tcircle(_, r) => return r\n\t}\n}\nstruct Point {\n\tx: f32\n}\n\
             fn max[T: Ordered](a: T) -> T {\n}\n"
        );
        // Literals keep their lines; header braces are always blocks.
        assert_eq!(
            fmt_tokens(
                "fn f(cb: fn(u8)){\n\tif a{x()}else if b{y()}\n\tlet p = Point{\n\
                 x: 1,\n\t\t\ty: [2]u8{3, 4},\n}\n\tlet g: fn() = h\n\tq = Q{}\n}\n"
            ),
            "fn f(cb: fn(u8)) {\n\tif a {\n\t\tx()\n\t} else if b {\n\t\ty()\n\t}\n\
             \tlet p = Point{\n\t\tx: 1,\n\t\ty: [2]u8{3, 4},\n\t}\n\tlet g: fn() = h\n\
             \tq = Q{}\n}\n"
        );
    }

    #[test]
    fn refuses_files_that_do_not_parse() {
        assert!(format("fn f() {\n\tlet = 1\n}\n", 0).is_err());
        assert!(format("fn f() {\n", 0).is_err());
        assert!(format("fn f() {\n\tx = \"open\n}\n", 0).is_err());
    }

    #[test]
    fn never_glues_tokens_into_others() {
        assert!(would_merge("/", "/"));
        assert!(would_merge("-", ">"));
        assert!(would_merge("+", "%"));
        assert!(!would_merge("-", "x"));
        assert_eq!(fmt("fn f() {\n\tx = - -y\n}\n"), "fn f() {\n\tx = --y\n}\n");
    }

    #[test]
    fn output_has_the_same_tokens() {
        let src = "// h\npackage main\nimport \"std/io\"\nconst  K:u8=0x7f\n\
                   fn f(a:u32)->u32{\n  let x=a+% 1;let y = x // c\n  if x<2{return 1}\n\
                   \x20 else{return 1_000}\n}\n";
        let out = fmt(src);
        assert_eq!(tokens(src), tokens(&out));
        assert!(same_program(src, &out));
        assert!(!same_program(src, &out.replace("+%", "+")));
        assert!(!same_program(src, &out.replace("// c", "// d")));
    }

    /// The standard library and the test programs are in canonical form.
    #[test]
    fn repository_sources_are_canonical() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
        let mut files = Vec::new();
        let mut dirs = vec![root.join("std"), root.join("tests/programs")];
        while let Some(dir) = dirs.pop() {
            for entry in std::fs::read_dir(&dir).expect("read dir") {
                let path = entry.expect("dir entry").path();
                if path.is_dir() {
                    dirs.push(path);
                } else if path.extension().is_some_and(|e| e == "lode") {
                    files.push(path);
                }
            }
        }
        assert!(files.len() > 10);
        let mut bad = Vec::new();
        for path in files {
            let src = std::fs::read_to_string(&path).expect("read");
            // Some test programs use syntax the parser rejects on purpose.
            let out = format(&src, 0).unwrap_or_else(|_| fmt_tokens(&src));
            if out != src {
                bad.push(path.display().to_string());
            }
        }
        assert!(bad.is_empty(), "not canonical (run `lode fmt`): {bad:?}");
    }
}
