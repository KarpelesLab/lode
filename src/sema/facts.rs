//! The facts the proof checker knows at a point in a function.
//!
//! Two kinds of fact, both decidable and cheap (docs/safety.md):
//!
//! - **ranges**: an integer local's value lies in `lo..=hi`;
//! - **relations**: for two integer locals `a` and `b`, `a - b <= c`.
//!
//! Facts come from literals and constants, from assignments, and from the
//! conditions of `if` and `while` (narrowing). They flow forward through a
//! function: past an `if` whose branch always leaves the block, both branches'
//! facts are joined, and at the head of a loop every variable the loop assigns
//! is forgotten.

use std::collections::HashMap;

use super::tree::{CmpOp, LocalId};
use crate::types::Range;

/// `a - b <= c` for two locals.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Rel {
    a: LocalId,
    b: LocalId,
    c: i128,
}

/// Facts at one program point.
#[derive(Clone, Debug, Default)]
pub struct Env {
    /// Known ranges; a local without an entry can be anything its type allows.
    ranges: HashMap<LocalId, Range>,
    rels: Vec<Rel>,
    /// The facts contradict each other: this point can't be reached.
    pub dead: bool,
}

/// One fact learned from a condition.
#[derive(Clone, Debug)]
pub enum Fact {
    /// `local` lies in `bound`; `full` is its type's range.
    Narrow {
        local: LocalId,
        bound: Range,
        full: Range,
    },
    /// `a - b <= c`.
    Rel { a: LocalId, b: LocalId, c: i128 },
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
    /// The local this side reads, if it's (a lossless conversion of) one.
    pub term: Option<LocalId>,
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
        // x <= y + c <= y.hi + c
        facts.push(Fact::Narrow {
            local: a,
            bound: Range {
                lo: ANY.lo,
                hi: y.range.hi.saturating_add(c),
            },
            full: x.full,
        });
    }
    if let Some(b) = y.term {
        // y >= x - c >= x.lo - c
        facts.push(Fact::Narrow {
            local: b,
            bound: Range {
                lo: x.range.lo.saturating_sub(c),
                hi: ANY.hi,
            },
            full: y.full,
        });
    }
    if let (Some(a), Some(b)) = (x.term, y.term) {
        facts.push(Fact::Rel { a, b, c });
    }
    facts
}

/// Facts from `x != y`: only useful when one side is a single value at an end
/// of the other side's range.
fn ne(x: Side, y: Side) -> Vec<Fact> {
    let mut facts = Vec::new();
    for (s, k) in [(x, y), (y, x)] {
        if let (Some(local), true) = (s.term, k.range.lo == k.range.hi) {
            let v = k.range.lo;
            let bound = if s.range.lo == v {
                Range {
                    lo: v + 1,
                    hi: ANY.hi,
                }
            } else if s.range.hi == v {
                Range {
                    lo: ANY.lo,
                    hi: v - 1,
                }
            } else {
                continue;
            };
            facts.push(Fact::Narrow {
                local,
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

    /// The known range of `local`, if narrower than its type.
    pub fn range(&self, local: LocalId) -> Option<Range> {
        self.ranges.get(&local).copied()
    }

    /// The tightest known `c` with `a - b <= c`.
    pub fn rel(&self, a: LocalId, b: LocalId) -> Option<i128> {
        self.rels
            .iter()
            .filter(|r| r.a == a && r.b == b)
            .map(|r| r.c)
            .min()
    }

    /// `local` was assigned a value in `range` (`None`: anything its type allows).
    /// Every relation involving it is forgotten.
    pub fn assign(&mut self, local: LocalId, range: Option<Range>) {
        match range {
            Some(r) => {
                self.ranges.insert(local, r);
            }
            None => {
                self.ranges.remove(&local);
            }
        }
        self.rels.retain(|r| r.a != local && r.b != local);
    }

    /// Forget everything about `local` (at the head of a loop that assigns it).
    pub fn forget(&mut self, local: LocalId) {
        self.assign(local, None);
    }

    pub fn apply(&mut self, facts: &[Fact]) {
        for fact in facts {
            match *fact {
                Fact::Narrow { local, bound, full } => {
                    let current = self.range(local).unwrap_or(full);
                    match current.intersect(bound) {
                        Some(r) => {
                            self.ranges.insert(local, r);
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
            .filter_map(|(local, ra)| b.ranges.get(local).map(|rb| (*local, ra.hull(*rb))))
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

    fn var(local: LocalId) -> Side {
        Side {
            term: Some(local),
            range: U32,
            full: U32,
        }
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
        assert_eq!(env.range(0), Some(Range { lo: 0, hi: 9 }));
        let mut env = Env::default();
        env.apply(&f.when_false);
        assert_eq!(env.range(0), Some(Range { lo: 10, hi: U32.hi }));
    }

    #[test]
    fn relations_between_locals() {
        // done > left is false: done - left <= 0.
        let f = comparison(CmpOp::Gt, var(0), var(1));
        let mut env = Env::default();
        env.apply(&f.when_false);
        assert_eq!(env.rel(0, 1), Some(0));
        env.assign(1, None);
        assert_eq!(env.rel(0, 1), None);
    }

    #[test]
    fn join_keeps_common_facts() {
        let mut a = Env::default();
        a.apply(&comparison(CmpOp::Lt, var(0), konst(5)).when_true);
        let mut b = Env::default();
        b.apply(&comparison(CmpOp::Eq, var(0), konst(7)).when_true);
        let j = Env::join(a, b);
        assert_eq!(j.range(0), Some(Range { lo: 0, hi: 7 }));
    }

    #[test]
    fn contradiction_is_dead() {
        let mut env = Env::default();
        env.apply(&comparison(CmpOp::Lt, var(0), konst(0)).when_true);
        assert!(env.dead);
    }
}
