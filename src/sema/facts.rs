//! The facts the proof checker knows at a point in a function.
//!
//! Two kinds of fact, both decidable and cheap (docs/safety.md):
//!
//! - **ranges**: a term's value lies in `lo..=hi`;
//! - **relations**: for two terms `a` and `b`, `a - b <= c`.
//!
//! A [`Term`] is an integer local, or the length of a view local (a slice or a
//! `str`), so `i < xs.len` relates `i` to the length of `xs`.
//!
//! Facts come from literals and constants, from assignments, from the
//! conditions of `if` and `while` (narrowing), and from `for` loops. They flow
//! forward through a function: past an `if` whose branch always leaves the
//! block, both branches' facts are joined, and at the head of a loop every
//! variable the loop assigns is forgotten.

use std::collections::HashMap;

use super::tree::{CmpOp, LocalId};
use crate::types::Range;

/// Something the checker knows facts about.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    /// The value of an integer local.
    Local(LocalId),
    /// The length of a view local (`xs.len` of a slice or `str`).
    Len(LocalId),
}

impl Term {
    /// The local the term is about.
    fn local(self) -> LocalId {
        match self {
            Term::Local(l) | Term::Len(l) => l,
        }
    }
}

/// A value the checker can name: a term plus a constant, like `i`, `i + 1`
/// or `xs.len - 1`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Linear {
    pub term: Term,
    pub offset: i128,
}

impl Linear {
    pub fn of(term: Term) -> Linear {
        Linear { term, offset: 0 }
    }

    /// `self + k`, if it fits.
    pub fn plus(self, k: i128) -> Option<Linear> {
        Some(Linear {
            offset: self.offset.checked_add(k)?,
            ..self
        })
    }
}

/// `a - b <= c` for two terms.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Rel {
    a: Term,
    b: Term,
    c: i128,
}

/// Facts at one program point.
#[derive(Clone, Debug, Default)]
pub struct Env {
    /// Known ranges; a term without an entry can be anything its type allows.
    ranges: HashMap<Term, Range>,
    rels: Vec<Rel>,
    /// The facts contradict each other: this point can't be reached.
    pub dead: bool,
}

/// One fact learned from a condition.
#[derive(Clone, Debug)]
pub enum Fact {
    /// `term` lies in `bound`; `full` is its type's range.
    Narrow {
        term: Term,
        bound: Range,
        full: Range,
    },
    /// `a - b <= c`.
    Rel { a: Term, b: Term, c: i128 },
}

/// The facts a condition gives when it's true and when it's false.
#[derive(Clone, Debug, Default)]
pub struct CondFacts {
    pub when_true: Vec<Fact>,
    pub when_false: Vec<Fact>,
}

/// One side of a comparison, as far as the checker knows it.
#[derive(Clone, Copy, Debug)]
pub struct Side {
    /// The term (plus a constant) this side reads, if any.
    pub term: Option<Linear>,
    pub range: Range,
    /// The range of the side's type.
    pub full: Range,
}

const ANY: Range = Range {
    lo: i128::MIN,
    hi: i128::MAX,
};

/// Facts from `x - y <= c`.
fn le(x: Side, y: Side, c: i128) -> Vec<Fact> {
    let mut facts = Vec::new();
    if let Some(a) = x.term {
        // x = a + ka <= y + c <= y.hi + c
        facts.push(Fact::Narrow {
            term: a.term,
            bound: Range {
                lo: ANY.lo,
                hi: y.range.hi.saturating_add(c).saturating_sub(a.offset),
            },
            full: x.full,
        });
    }
    if let Some(b) = y.term {
        // y = b + kb >= x - c >= x.lo - c
        facts.push(Fact::Narrow {
            term: b.term,
            bound: Range {
                lo: x.range.lo.saturating_sub(c).saturating_sub(b.offset),
                hi: ANY.hi,
            },
            full: y.full,
        });
    }
    if let (Some(a), Some(b)) = (x.term, y.term)
        && a.term != b.term
    {
        // (a + ka) - (b + kb) <= c
        facts.push(Fact::Rel {
            a: a.term,
            b: b.term,
            c: c.saturating_sub(a.offset).saturating_add(b.offset),
        });
    }
    facts
}

/// Facts from `x != y`: only useful when one side is a single value at an end
/// of the other side's range.
fn ne(x: Side, y: Side) -> Vec<Fact> {
    let mut facts = Vec::new();
    for (s, k) in [(x, y), (y, x)] {
        if let (Some(lin), true) = (s.term, k.range.lo == k.range.hi) {
            let v = k.range.lo;
            // s = term + offset, so the bound on the term is shifted.
            let bound = if s.range.lo == v {
                Range {
                    lo: (v + 1).saturating_sub(lin.offset),
                    hi: ANY.hi,
                }
            } else if s.range.hi == v {
                Range {
                    lo: ANY.lo,
                    hi: (v - 1).saturating_sub(lin.offset),
                }
            } else {
                continue;
            };
            facts.push(Fact::Narrow {
                term: lin.term,
                bound,
                full: s.full,
            });
        }
    }
    facts
}

/// Facts from `l op r` being true.
fn holds(op: CmpOp, l: Side, r: Side) -> Vec<Fact> {
    match op {
        CmpOp::Lt => le(l, r, -1),
        CmpOp::Le => le(l, r, 0),
        CmpOp::Gt => le(r, l, -1),
        CmpOp::Ge => le(r, l, 0),
        CmpOp::Eq => {
            let mut f = le(l, r, 0);
            f.extend(le(r, l, 0));
            f
        }
        CmpOp::Ne => ne(l, r),
    }
}

fn negate(op: CmpOp) -> CmpOp {
    match op {
        CmpOp::Lt => CmpOp::Ge,
        CmpOp::Le => CmpOp::Gt,
        CmpOp::Gt => CmpOp::Le,
        CmpOp::Ge => CmpOp::Lt,
        CmpOp::Eq => CmpOp::Ne,
        CmpOp::Ne => CmpOp::Eq,
    }
}

/// The facts of an integer comparison.
pub fn comparison(op: CmpOp, l: Side, r: Side) -> CondFacts {
    CondFacts {
        when_true: holds(op, l, r),
        when_false: holds(negate(op), l, r),
    }
}

impl CondFacts {
    pub fn negated(self) -> CondFacts {
        CondFacts {
            when_true: self.when_false,
            when_false: self.when_true,
        }
    }

    /// `l && r`: both hold when true; nothing is known when false.
    pub fn and(l: CondFacts, r: CondFacts) -> CondFacts {
        let mut when_true = l.when_true;
        when_true.extend(r.when_true);
        CondFacts {
            when_true,
            when_false: Vec::new(),
        }
    }

    /// `l || r`: both fail when false; nothing is known when true.
    pub fn or(l: CondFacts, r: CondFacts) -> CondFacts {
        let mut when_false = l.when_false;
        when_false.extend(r.when_false);
        CondFacts {
            when_true: Vec::new(),
            when_false,
        }
    }
}

impl Env {
    /// The facts at a point no path reaches.
    pub fn unreachable() -> Env {
        Env {
            dead: true,
            ..Env::default()
        }
    }

    /// The known range of `term`, if narrower than its type.
    pub fn range(&self, term: Term) -> Option<Range> {
        self.ranges.get(&term).copied()
    }

    /// The tightest known `c` with `a - b <= c`.
    pub fn rel(&self, a: Term, b: Term) -> Option<i128> {
        self.rels
            .iter()
            .filter(|r| r.a == a && r.b == b)
            .map(|r| r.c)
            .min()
    }

    /// The tightest `c` with `a - b <= c` from a known relation, or from two
    /// relations chained through one other term (`a - m <= c1` and
    /// `m - b <= c2` give `a - b <= c1 + c2`). One step keeps this cheap and
    /// predictable, and covers `let n = xs.len` followed by `i < n`.
    pub fn rel_through(&self, a: Term, b: Term) -> Option<i128> {
        let chained = self
            .rels
            .iter()
            .filter(|r1| r1.a == a && r1.b != b)
            .filter_map(|r1| self.rel(r1.b, b).map(|c2| r1.c.saturating_add(c2)))
            .min();
        match (self.rel(a, b), chained) {
            (Some(x), Some(y)) => Some(x.min(y)),
            (x, y) => x.or(y),
        }
    }

    /// An upper bound on `x - y` from the relations (see [`Env::rel_through`]).
    pub fn diff_bound(&self, x: Linear, y: Linear) -> Option<i128> {
        let terms = if x.term == y.term {
            0
        } else {
            self.rel_through(x.term, y.term)?
        };
        terms
            .checked_add(x.offset)
            .and_then(|c| c.checked_sub(y.offset))
    }

    /// `local` was assigned a value: an integer in `range` (`None`: anything
    /// its type allows), or a view whose length is unknown. Every relation
    /// involving the local or its length is forgotten.
    pub fn assign(&mut self, local: LocalId, range: Option<Range>) {
        match range {
            Some(r) => {
                self.ranges.insert(Term::Local(local), r);
            }
            None => {
                self.ranges.remove(&Term::Local(local));
            }
        }
        self.ranges.remove(&Term::Len(local));
        self.rels
            .retain(|r| r.a.local() != local && r.b.local() != local);
    }

    /// Forget everything about `local` (at the head of a loop that assigns it).
    pub fn forget(&mut self, local: LocalId) {
        self.assign(local, None);
    }

    pub fn apply(&mut self, facts: &[Fact]) {
        for fact in facts {
            match *fact {
                Fact::Narrow { term, bound, full } => {
                    let current = self.range(term).unwrap_or(full);
                    match current.intersect(bound) {
                        Some(r) => {
                            self.ranges.insert(term, r);
                        }
                        None => self.dead = true,
                    }
                }
                Fact::Rel { a, b, c } => {
                    if self.rel(a, b).is_none_or(|old| c < old) {
                        self.rels.retain(|r| !(r.a == a && r.b == b));
                        self.rels.push(Rel { a, b, c });
                    }
                }
            }
        }
    }

    /// The facts that hold after either of two paths: ranges are widened to
    /// cover both, and only relations both paths know are kept (at the weaker
    /// bound). A path that can't be reached contributes nothing.
    pub fn join(a: Env, b: Env) -> Env {
        if a.dead {
            return b;
        }
        if b.dead {
            return a;
        }
        let ranges = a
            .ranges
            .iter()
            .filter_map(|(term, ra)| b.ranges.get(term).map(|rb| (*term, ra.hull(*rb))))
            .collect();
        let rels = a
            .rels
            .iter()
            .filter_map(|ra| {
                b.rel(ra.a, ra.b).map(|cb| Rel {
                    c: ra.c.max(cb),
                    ..*ra
                })
            })
            .collect();
        Env {
            ranges,
            rels,
            dead: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const U32: Range = Range {
        lo: 0,
        hi: u32::MAX as i128,
    };

    fn side(term: Term) -> Side {
        Side {
            term: Some(Linear::of(term)),
            range: U32,
            full: U32,
        }
    }

    /// `term + k`, for a term in `0..=u32::MAX - k`.
    fn plus(term: Term, k: i128) -> Side {
        Side {
            term: Some(Linear { term, offset: k }),
            range: Range { lo: k, hi: U32.hi },
            full: U32,
        }
    }

    fn var(local: LocalId) -> Side {
        side(Term::Local(local))
    }

    fn konst(v: i128) -> Side {
        Side {
            term: None,
            range: Range::exact(v),
            full: U32,
        }
    }

    #[test]
    fn narrowing_on_less_than() {
        let f = comparison(CmpOp::Lt, var(0), konst(10));
        let mut env = Env::default();
        env.apply(&f.when_true);
        assert_eq!(env.range(Term::Local(0)), Some(Range { lo: 0, hi: 9 }));
        let mut env = Env::default();
        env.apply(&f.when_false);
        assert_eq!(
            env.range(Term::Local(0)),
            Some(Range { lo: 10, hi: U32.hi })
        );
    }

    #[test]
    fn relations_between_locals() {
        // done > left is false: done - left <= 0.
        let f = comparison(CmpOp::Gt, var(0), var(1));
        let mut env = Env::default();
        env.apply(&f.when_false);
        assert_eq!(env.rel(Term::Local(0), Term::Local(1)), Some(0));
        env.assign(1, None);
        assert_eq!(env.rel(Term::Local(0), Term::Local(1)), None);
    }

    #[test]
    fn lengths_are_terms() {
        // i < xs.len: i - len(xs) <= -1, and len(xs) >= 1.
        let f = comparison(CmpOp::Lt, var(0), side(Term::Len(1)));
        let mut env = Env::default();
        env.apply(&f.when_true);
        assert_eq!(env.rel(Term::Local(0), Term::Len(1)), Some(-1));
        assert_eq!(env.range(Term::Len(1)).map(|r| r.lo), Some(1));
        // Facts about the length of one view don't touch another local.
        env.assign(2, None);
        assert_eq!(env.rel(Term::Local(0), Term::Len(1)), Some(-1));
        // Assigning the view forgets its length's facts.
        env.assign(1, None);
        assert_eq!(env.rel(Term::Local(0), Term::Len(1)), None);
        assert_eq!(env.range(Term::Len(1)), None);
    }

    #[test]
    fn relations_chain_once() {
        // n == len(xs) (from `let n = xs.len`), then i < n.
        let mut env = Env::default();
        env.apply(&comparison(CmpOp::Eq, var(1), side(Term::Len(2))).when_true);
        env.apply(&comparison(CmpOp::Lt, var(0), var(1)).when_true);
        assert_eq!(env.rel(Term::Local(0), Term::Len(2)), None);
        assert_eq!(env.rel_through(Term::Local(0), Term::Len(2)), Some(-1));
        // Only one step: i < n, n <= m, m <= len(xs) proves nothing about xs.
        let mut env = Env::default();
        env.apply(&comparison(CmpOp::Lt, var(0), var(1)).when_true);
        env.apply(&comparison(CmpOp::Le, var(1), var(3)).when_true);
        env.apply(&comparison(CmpOp::Le, var(3), side(Term::Len(2))).when_true);
        assert_eq!(env.rel_through(Term::Local(0), Term::Local(3)), Some(-1));
        assert_eq!(env.rel_through(Term::Local(0), Term::Len(2)), None);
    }

    #[test]
    fn offsets_shift_relations() {
        // i + 1 < xs.len: i - len(xs) <= -2.
        let mut env = Env::default();
        env.apply(&comparison(CmpOp::Lt, plus(Term::Local(0), 1), side(Term::Len(1))).when_true);
        assert_eq!(env.rel(Term::Local(0), Term::Len(1)), Some(-2));
        assert_eq!(env.range(Term::Local(0)).map(|r| r.hi), Some(U32.hi - 2));
        // So (i + 1) - len(xs) <= -1, and xs.len - 1 - len(xs) is exactly -1.
        let i1 = Linear {
            term: Term::Local(0),
            offset: 1,
        };
        let len = Linear::of(Term::Len(1));
        assert_eq!(env.diff_bound(i1, len), Some(-1));
        let last = Linear {
            term: Term::Len(1),
            offset: -1,
        };
        assert_eq!(Env::default().diff_bound(last, len), Some(-1));
    }

    #[test]
    fn join_keeps_common_facts() {
        let mut a = Env::default();
        a.apply(&comparison(CmpOp::Lt, var(0), konst(5)).when_true);
        let mut b = Env::default();
        b.apply(&comparison(CmpOp::Eq, var(0), konst(7)).when_true);
        let j = Env::join(a, b);
        assert_eq!(j.range(Term::Local(0)), Some(Range { lo: 0, hi: 7 }));
    }

    #[test]
    fn contradiction_is_dead() {
        let mut env = Env::default();
        env.apply(&comparison(CmpOp::Lt, var(0), konst(0)).when_true);
        assert!(env.dead);
    }
}
