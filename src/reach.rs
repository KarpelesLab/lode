//! Which functions a program reaches: a walk of the call graph from `main`.
//!
//! Lowering emits only these, and only the string literals and array
//! constants they use, so code nothing calls costs nothing in the executable.
//! Every function is still checked: an error in code nothing calls fails the
//! build like any other.
//!
//! A call (`TExprKind::Call`) is the only way to refer to a function today;
//! a method call is one too, with the receiver as its first argument. The
//! walk goes through every expression, including the places passed with `&`
//! (`TExprKind::Ref`), whose indexes can call functions.

use crate::sema::{FuncId, Handler, Program, TExpr, TExprKind, TStmt, stmt_exprs, subexprs};

/// The functions reachable from a root.
#[derive(Debug)]
pub struct Reach {
    /// `reached[f]`: whether function `f` is the root or is called, directly
    /// or not, from it.
    pub reached: Vec<bool>,
    /// `strings[i]`: whether a reached function uses string literal `i`.
    pub strings: Vec<bool>,
    /// `tables[i]`: whether a reached function uses array constant `i`.
    pub tables: Vec<bool>,
    /// Whether a reached function calls the root (the root is recursive).
    pub root_called: bool,
}

impl Reach {
    /// The functions reachable from `root`.
    pub fn from(program: &Program, root: FuncId) -> Reach {
        let mut reached = vec![false; program.funcs.len()];
        let mut strings = vec![false; program.strings.len()];
        let mut tables = vec![false; program.tables.len()];
        let mut root_called = false;
        reached[root] = true;
        let mut work = vec![root];
        let mut uses = Uses::default();
        while let Some(f) = work.pop() {
            for s in &program.funcs[f].body {
                uses.stmt(s);
            }
            for s in uses.strings.drain(..) {
                strings[s] = true;
            }
            for t in uses.tables.drain(..) {
                tables[t] = true;
            }
            for callee in uses.calls.drain(..) {
                root_called |= callee == root;
                if !reached[callee] {
                    reached[callee] = true;
                    work.push(callee);
                }
            }
        }
        Reach {
            reached,
            strings,
            tables,
            root_called,
        }
    }

    /// Every function, for a program without a root (a library: `--emit=ir`
    /// shows all of its code).
    pub fn all(program: &Program) -> Reach {
        Reach {
            reached: vec![true; program.funcs.len()],
            strings: vec![true; program.strings.len()],
            tables: vec![true; program.tables.len()],
            root_called: false,
        }
    }
}

/// The functions, string literals and array constants a function body uses.
#[derive(Default)]
struct Uses {
    calls: Vec<FuncId>,
    strings: Vec<usize>,
    tables: Vec<usize>,
}

impl Uses {
    fn stmt(&mut self, s: &TStmt) {
        for e in stmt_exprs(s) {
            self.expr(e);
        }
        let nested: Vec<&[TStmt]> = match s {
            TStmt::If(_, then, otherwise) => vec![then, otherwise],
            TStmt::While(_, body)
            | TStmt::For { body, .. }
            | TStmt::Loop(body)
            | TStmt::Block(body)
            | TStmt::Defer { body, .. } => vec![body],
            TStmt::Match { arms, .. } => arms.iter().map(|a| &a.body[..]).collect(),
            TStmt::Init(..)
            | TStmt::Assign(..)
            | TStmt::Store(..)
            | TStmt::Expr(_)
            | TStmt::Return(_)
            | TStmt::Throw(_)
            | TStmt::Break
            | TStmt::Continue => Vec::new(),
        };
        for s in nested.into_iter().flatten() {
            self.stmt(s);
        }
    }

    fn expr(&mut self, e: &TExpr) {
        match &e.kind {
            TExprKind::Call(f, _) => self.calls.push(*f),
            TExprKind::Str(id) => self.strings.push(*id),
            TExprKind::Table(id) => self.tables.push(*id),
            TExprKind::Catch {
                handler: Handler::Block(body),
                ..
            } => {
                for s in body {
                    self.stmt(s);
                }
            }
            _ => {}
        }
        for sub in subexprs(e) {
            self.expr(sub);
        }
    }
}
