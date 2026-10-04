//! Which functions a program reaches: a walk of the call graph from `main`.
//!
//! Lowering emits only these, and only the string literals they use, so code
//! nothing calls costs nothing in the executable. Every function is still
//! checked: an error in code nothing calls fails the build like any other.
//!
//! A call (`TExprKind::Call`) is the only way to refer to a function today.

use crate::sema::{FuncId, Program, TExpr, TExprKind, TStmt};

/// The functions reachable from a root.
#[derive(Debug)]
pub struct Reach {
    /// `reached[f]`: whether function `f` is the root or is called, directly
    /// or not, from it.
    pub reached: Vec<bool>,
    /// `strings[i]`: whether a reached function uses string literal `i`.
    pub strings: Vec<bool>,
    /// Whether a reached function calls the root (the root is recursive).
    pub root_called: bool,
}

impl Reach {
    /// The functions reachable from `root`.
    pub fn from(program: &Program, root: FuncId) -> Reach {
        let mut reached = vec![false; program.funcs.len()];
        let mut strings = vec![false; program.strings.len()];
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
            root_called,
        }
    }

    /// Every function, for a program without a root (a library: `--emit=ir`
    /// shows all of its code).
    pub fn all(program: &Program) -> Reach {
        Reach {
            reached: vec![true; program.funcs.len()],
            strings: vec![true; program.strings.len()],
            root_called: false,
        }
    }
}

/// The functions and string literals a function body uses.
#[derive(Default)]
struct Uses {
    calls: Vec<FuncId>,
    strings: Vec<usize>,
}

impl Uses {
    fn stmt(&mut self, s: &TStmt) {
        match s {
            TStmt::Init(_, e) | TStmt::Assign(_, e) | TStmt::Expr(e) => self.expr(e),
            TStmt::Store(place, e) => {
                self.expr(place);
                self.expr(e);
            }
            TStmt::Return(e) => {
                if let Some(e) = e {
                    self.expr(e);
                }
            }
            TStmt::If(cond, then, otherwise) => {
                self.expr(cond);
                for s in then.iter().chain(otherwise) {
                    self.stmt(s);
                }
            }
            TStmt::While(cond, body) => {
                self.expr(cond);
                for s in body {
                    self.stmt(s);
                }
            }
            TStmt::For {
                start, end, body, ..
            } => {
                self.expr(start);
                self.expr(end);
                for s in body {
                    self.stmt(s);
                }
            }
            TStmt::Loop(body) | TStmt::Block(body) => {
                for s in body {
                    self.stmt(s);
                }
            }
            TStmt::Break | TStmt::Continue => {}
        }
    }

    fn expr(&mut self, e: &TExpr) {
        match &e.kind {
            TExprKind::Call(f, args) => {
                self.calls.push(*f);
                for a in args {
                    self.expr(a);
                }
            }
            TExprKind::ArrayLit(items) | TExprKind::Syscall(items) => {
                for a in items {
                    self.expr(a);
                }
            }
            TExprKind::Binary(_, l, r)
            | TExprKind::And(l, r)
            | TExprKind::Or(l, r)
            | TExprKind::Index(l, r)
            | TExprKind::PtrAdd(l, r) => {
                self.expr(l);
                self.expr(r);
            }
            TExprKind::Unary(_, inner)
            | TExprKind::Convert(inner)
            | TExprKind::ViewLen(inner)
            | TExprKind::ArrayLen(inner)
            | TExprKind::ArrayRepeat(inner, _)
            | TExprKind::ToSlice(inner)
            | TExprKind::StrPtr(inner) => self.expr(inner),
            TExprKind::Str(id) => self.strings.push(*id),
            TExprKind::Int(_) | TExprKind::Bool(_) | TExprKind::Local(_) => {}
        }
    }
}
