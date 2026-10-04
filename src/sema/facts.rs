//! The facts the proof checker knows at a point in a function.
//!
//! Four kinds of fact, all decidable and cheap (docs/safety.md):
//!
//! - **ranges**: a term's value lies in `lo..=hi`;
//! - **holes**: a term isn't some value inside its range (`b != 0`);
//! - **relations**: for two terms `a` and `b`, `a - b <= c`;
//! - **sums**: for two terms, `p*a + q*b <= c`, with other coefficients
//!   than a relation's (`a + b <= c`, `10*v + d <= c`).
//!
//! A [`Term`] is an integer local, the length of a view local (a slice or a
//! `str`), so `i < xs.len` relates `i` to the length of `xs`, or an integer
//! field of a struct local (`p.x`, `p.a.b`).
//!
//! Facts come from literals and constants, from assignments, from the
//! conditions of `if` and `while` (narrowing), and from `for` loops. They flow
//! forward through a function: after an `if`, both branches' facts are joined
//! (a branch that always leaves the block contributes nothing), and at the
//! head of a loop, facts about the variables the loop assigns are kept as far
//! as every iteration keeps them ([`Env::loosen`], [`Env::holds_in`]; the
//! rule is in `super::Checker::loop_body` and docs/safety.md).

use std::collections::{BTreeSet, HashMap};

use super::tree::{CmpOp, LocalId};
use crate::types::Range;

/// Something the checker knows facts about. The order only puts the two
/// terms of a sum in a fixed order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Term {
    /// The value of an integer local.
    Local(LocalId),
    /// The length of a view local (`xs.len` of a slice or `str`).
    Len(LocalId),
    /// An integer field of a struct local, reached through fields only
    /// (`p.x`, `p.a.b`, not `p.a[i].b`). The number tells the fields of the
    /// local's struct apart: it's the field's position when the struct and
    /// the structs in it are flattened, each non-struct field counting one.
    Field(LocalId, u32),
}

impl Term {
    /// The local the term is about.
    pub fn local(self) -> LocalId {
        match self {
            Term::Local(l) | Term::Len(l) | Term::Field(l, _) => l,
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

/// A value the checker can relate to at most two terms: a constant plus
/// each term times a coefficient other than 0, like `9 - d`, `a + b` or
/// `10 * v + d`. A term plus a constant ([`Linear`]) is one too.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Form {
    terms: [Option<(Term, i128)>; 2],
    pub k: i128,
}

impl Form {
    pub fn constant(k: i128) -> Form {
        Form {
            terms: [None, None],
            k,
        }
    }

    pub fn of(x: Linear) -> Form {
        Form {
            terms: [Some((x.term, 1)), None],
            k: x.offset,
        }
    }

    /// Its terms, with their coefficients.
    pub fn terms(&self) -> impl Iterator<Item = (Term, i128)> + '_ {
        self.terms.iter().flatten().copied()
    }

    /// The number of terms.
    pub fn term_count(&self) -> usize {
        self.terms().count()
    }

    /// `self + other`, if it has at most two terms and fits.
    pub fn plus(self, other: Form) -> Option<Form> {
        let mut out = Form::constant(self.k.checked_add(other.k)?);
        let mut n = 0;
        for (t, m) in self.terms().chain(other.terms()) {
            if let Some(slot) = out.terms[..n].iter_mut().flatten().find(|s| s.0 == t) {
                slot.1 = slot.1.checked_add(m)?;
                continue;
            }
            if n == 2 {
                // A third term: perhaps one of the first two cancels out.
                out = out.compact();
                n = out.term_count();
                if n == 2 {
                    return None;
                }
            }
            out.terms[n] = Some((t, m));
            n += 1;
        }
        Some(out.compact())
    }

    /// Without the terms whose coefficient is 0.
    fn compact(self) -> Form {
        let mut out = Form::constant(self.k);
        let mut n = 0;
        for (t, m) in self.terms() {
            if m != 0 {
                out.terms[n] = Some((t, m));
                n += 1;
            }
        }
        out
    }

    /// `self * m`, if it fits.
    pub fn scale(self, m: i128) -> Option<Form> {
        let mut out = Form::constant(self.k.checked_mul(m)?);
        for (slot, term) in out.terms.iter_mut().zip(self.terms) {
            *slot = match term {
                Some((t, c)) => Some((t, c.checked_mul(m)?)),
                None => None,
            };
        }
        Some(out.compact())
    }

    /// `self - other`, if it has at most two terms and fits.
    pub fn minus(self, other: Form) -> Option<Form> {
        self.plus(other.scale(-1)?)
    }

    /// The facts from `self <= c`: for one term, a range; for two, a
    /// relation (coefficients 1 and -1, in either order) or a sum. Both
    /// sides of a sum are divided by the largest number that divides both
    /// coefficients (`2*a + 2*b <= 5` is `a + b <= 2`). `full` is the
    /// type's range, for a range.
    pub fn le(self, c: i128, full: Range) -> Vec<Fact> {
        let Some(c) = c.checked_sub(self.k) else {
            return Vec::new();
        };
        match self.terms {
            [Some((t, m)), None] | [None, Some((t, m))] => {
                // m * t <= c
                let bound = if m > 0 {
                    Range {
                        lo: ANY.lo,
                        hi: c.div_euclid(m),
                    }
                } else {
                    // t >= c / m, rounded up.
                    Range {
                        lo: -(c.div_euclid(-m)),
                        hi: ANY.hi,
                    }
                };
                vec![Fact::Narrow {
                    term: t,
                    bound,
                    full,
                }]
            }
            [Some((a, p)), Some((b, q))] => vec![sum_fact(a, p, b, q, c)],
            _ => Vec::new(),
        }
    }
}

/// The greatest common divisor of two numbers other than 0, positive.
fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.unsigned_abs(), b.unsigned_abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    i128::try_from(a).unwrap_or(1)
}

/// `p*a + q*b <= c`, divided by the gcd of `p` and `q`, with the terms in
/// order: a relation if the coefficients are 1 and -1, a sum otherwise.
fn sum_fact(a: Term, p: i128, b: Term, q: i128, c: i128) -> Fact {
    let g = gcd(p, q);
    let (p, q, c) = (p / g, q / g, c.div_euclid(g));
    match (p, q) {
        (1, -1) => Fact::Rel { a, b, c },
        (-1, 1) => Fact::Rel { a: b, b: a, c },
        _ if a <= b => Fact::Sum { a, p, b, q, c },
        _ => Fact::Sum {
            a: b,
            p: q,
            b: a,
            q: p,
            c,
        },
    }
}

/// `p*a + q*b <= c` for two terms, `a < b`, with coefficients whose gcd is
/// 1, other than 1 and -1 (that's a [`Rel`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Sum {
    a: Term,
    p: i128,
    b: Term,
    q: i128,
    c: i128,
}

impl Sum {
    fn fact(self) -> Fact {
        Fact::Sum {
            a: self.a,
            p: self.p,
            b: self.b,
            q: self.q,
            c: self.c,
        }
    }
}

/// Facts at one program point.
#[derive(Clone, Debug, Default)]
pub struct Env {
    /// Known ranges; a term without an entry can be anything its type allows.
    ranges: HashMap<Term, Range>,
    rels: Vec<Rel>,
    sums: Vec<Sum>,
    /// The locals that may not be assigned yet on some path to this point
    /// (a `var` declared without a value, a `set` parameter).
    uninit: BTreeSet<LocalId>,
    /// Values terms are known not to have (`b != 0`), inside their ranges.
    holes: Vec<(Term, i128)>,
    /// The facts contradict each other: this point can't be reached.
    pub dead: bool,
}

/// How [`Env::loosen`] weakens a fact that doesn't hold at a loop's
/// back-edge.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Loosen {
    /// Forget it (for a range, the end that doesn't hold).
    Drop,
    /// Weaken it just enough to hold at every back-edge: a range grows to
    /// cover theirs, a relation takes the weakest bound (and is forgotten if
    /// a back-edge doesn't know it).
    Cover,
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
    /// `p*a + q*b <= c`, `a < b`, normalized as for [`Sum`].
    Sum {
        a: Term,
        p: i128,
        b: Term,
        q: i128,
        c: i128,
    },
    /// `term != value`.
    Hole { term: Term, value: i128 },
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
    /// The side as a [`Form`], if it is one (a term plus a constant, a
    /// constant, or a sum like `9 - d`).
    pub form: Option<Form>,
    /// The side as `F / m` (rounded down) of a form `F` that can't be
    /// negative, and a constant `m >= 1`.
    pub quot: Option<(Form, i128)>,
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
    // Between forms, `x - y <= c` is a form too, if it has at most two
    // terms: a relation (`(a + ka) - (b + kb) <= c`) or a sum
    // (`a - (k - b) <= c`). With `y = F / m` (rounded down, `F >= 0`),
    // `x <= y + c` is `m*x - F <= m*c`; with `x = F / m`, `x <= y + c` is
    // `F - m*y <= m*c + m - 1`. A form of one term gives a range (for a
    // side that's a term plus a constant, the same as above).
    let diff = match (x.form, y.form, x.quot, y.quot) {
        (Some(fx), Some(fy), _, _) => fx.minus(fy).map(|d| (d, c)),
        (Some(fx), None, _, Some((f, m))) => {
            fx.scale(m).and_then(|mx| mx.minus(f)).zip(m.checked_mul(c))
        }
        (None, Some(fy), Some((f, m)), _) => fy
            .scale(m)
            .and_then(|my| f.minus(my))
            .zip(m.checked_mul(c).and_then(|mc| mc.checked_add(m - 1))),
        _ => None,
    };
    if let Some((d, c)) = diff {
        facts.extend(d.le(c, x.full));
    }
    facts
}

/// Facts from `x != y`, when one side is a single value: at an end of the
/// other side's range, the range narrows; inside it, the term has a hole.
fn ne(x: Side, y: Side) -> Vec<Fact> {
    let mut facts = Vec::new();
    for (s, k) in [(x, y), (y, x)] {
        if let (Some(lin), true) = (s.term, k.range.lo == k.range.hi) {
            let v = k.range.lo;
            if s.range.lo < v && v < s.range.hi {
                if let Some(value) = v.checked_sub(lin.offset) {
                    facts.push(Fact::Hole {
                        term: lin.term,
                        value,
                    });
                }
                continue;
            }
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

    /// Whether `term` is known not to be `value`: it's outside its range,
    /// or a hole in it.
    pub fn excludes(&self, term: Term, value: i128) -> bool {
        self.range(term).is_some_and(|r| !r.contains(value)) || self.holes.contains(&(term, value))
    }

    /// Whether `x` (a term plus a constant, or none) in `range` is known not
    /// to be `value`.
    pub fn excludes_value(&self, x: Option<Linear>, range: Range, value: i128) -> bool {
        !range.contains(value)
            || x.is_some_and(|x| {
                value
                    .checked_sub(x.offset)
                    .is_some_and(|v| self.excludes(x.term, v))
            })
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

    /// The tightest `c` with `a - b <= c` this point gives: from the
    /// relations (see [`Env::rel_through`]), or from known ranges of both
    /// (`a.hi - b.lo`).
    pub fn diff(&self, a: Term, b: Term) -> Option<i128> {
        let by_ranges = match (self.range(a), self.range(b)) {
            (Some(ra), Some(rb)) => ra.hi.checked_sub(rb.lo),
            _ => None,
        };
        match (self.rel_through(a, b), by_ranges) {
            (Some(x), Some(y)) => Some(x.min(y)),
            (x, y) => x.or(y),
        }
    }

    /// The range of `term` (its known range, or `full` gives its type's),
    /// narrowed by each relation with another term and that term's range:
    /// `term - b <= c` gives `term <= b.hi + c`, and `b - term <= c` gives
    /// `term >= b.lo - c`. One step: the other term's range isn't narrowed
    /// in turn. `None` if nothing is known.
    pub fn range_via(&self, term: Term, full: impl Fn(Term) -> Range) -> Option<Range> {
        let own = self.range(term);
        let mut r = own.unwrap_or_else(|| full(term));
        let mut narrowed = false;
        for rel in &self.rels {
            if rel.a == term && rel.b != term {
                let other = self.range(rel.b).unwrap_or_else(|| full(rel.b));
                let hi = other.hi.saturating_add(rel.c);
                if hi < r.hi {
                    r.hi = hi;
                    narrowed = true;
                }
            } else if rel.b == term && rel.a != term {
                let other = self.range(rel.a).unwrap_or_else(|| full(rel.a));
                let lo = other.lo.saturating_sub(rel.c);
                if lo > r.lo {
                    r.lo = lo;
                    narrowed = true;
                }
            }
        }
        if r.lo > r.hi {
            // Contradictory facts: this point can't be reached.
            return own;
        }
        if narrowed { Some(r) } else { own }
    }

    /// The tightest known `c` with `p*a + q*b <= c` for a sum (`a < b`,
    /// normalized as for [`Sum`]), directly.
    fn sum(&self, a: Term, p: i128, b: Term, q: i128) -> Option<i128> {
        self.sums
            .iter()
            .filter(|s| s.a == a && s.p == p && s.b == b && s.q == q)
            .map(|s| s.c)
            .min()
    }

    /// The tightest `c` with `p*a + q*b <= c` this point gives for the
    /// two-term form `p*a + q*b` (normalized: [`sum_fact`] with `c = 0`):
    /// from a relation (directly or through one other term) or a sum, and
    /// from known ranges of both terms (`full` gives a term's type's range
    /// when it has none; `None` uses only known ranges).
    fn gives(&self, form: &Fact, full: Option<&dyn Fn(Term) -> Range>) -> Option<i128> {
        let (a, p, b, q, known) = match *form {
            Fact::Rel { a, b, .. } => (a, 1, b, -1, self.rel_through(a, b)),
            Fact::Sum { a, p, b, q, .. } => (a, p, b, q, self.sum(a, p, b, q)),
            _ => return None,
        };
        let range = |t: Term| self.range(t).or_else(|| full.map(|f| f(t)));
        let end = |r: Range, m: i128| {
            if m > 0 {
                m.checked_mul(r.hi)
            } else {
                m.checked_mul(r.lo)
            }
        };
        let by_ranges = match (range(a), range(b)) {
            (Some(ra), Some(rb)) => end(ra, p)
                .zip(end(rb, q))
                .and_then(|(x, y)| x.checked_add(y)),
            _ => None,
        };
        match (known, by_ranges) {
            (Some(x), Some(y)) => Some(x.min(y)),
            (x, y) => x.or(y),
        }
    }

    /// The bounds the relations and sums give on a form of two terms, as
    /// `(lo, hi)` (for a constant, itself): `p*a + q*b + k <= c*g + k` from a relation or a sum
    /// for `p*a + q*b` divided by `g`, the gcd of `p` and `q` (directly, or
    /// for a relation through one other term), and the same for `-p*a -
    /// q*b` below. Ranges aren't used: the caller has them.
    pub fn form_bounds(&self, f: Form) -> (Option<i128>, Option<i128>) {
        if f.term_count() == 0 {
            return (Some(f.k), Some(f.k));
        }
        let [Some((a, p)), Some((b, q))] = f.terms else {
            return (None, None);
        };
        let g = gcd(p, q);
        let bound = |sign: i128| -> Option<i128> {
            let form = sum_fact(a, sign * p, b, sign * q, 0);
            let c = match form {
                Fact::Rel { a, b, .. } => self.rel_through(a, b)?,
                Fact::Sum { a, p, b, q, .. } => self.sum(a, p, b, q)?,
                _ => return None,
            };
            c.checked_mul(g)
        };
        let hi = bound(1).and_then(|c| c.checked_add(f.k));
        let lo = bound(-1).and_then(|c| f.k.checked_sub(c));
        (lo, hi)
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
    /// its type allows), a view whose length is unknown, or a struct whose
    /// fields are unknown. Every relation involving the local, its length or
    /// its fields is forgotten.
    pub fn assign(&mut self, local: LocalId, range: Option<Range>) {
        self.uninit.remove(&local);
        self.forget_value(local, range);
    }

    /// Forget every fact about `local`, and know `range` for it.
    fn forget_value(&mut self, local: LocalId, range: Option<Range>) {
        match range {
            Some(r) => {
                self.ranges.insert(Term::Local(local), r);
            }
            None => {
                self.ranges.remove(&Term::Local(local));
            }
        }
        self.ranges.remove(&Term::Len(local));
        self.ranges
            .retain(|t, _| !matches!(t, Term::Field(l, _) if *l == local));
        self.rels
            .retain(|r| r.a.local() != local && r.b.local() != local);
        self.sums
            .retain(|s| s.a.local() != local && s.b.local() != local);
        self.holes.retain(|(t, _)| t.local() != local);
    }

    /// Forget everything about the fields of the struct local `local`
    /// numbered `fields` (a field, or the fields of a struct in it, was
    /// assigned).
    pub fn forget_fields(&mut self, local: LocalId, fields: std::ops::Range<u32>) {
        let hit = |t: &Term| matches!(*t, Term::Field(l, k) if l == local && fields.contains(&k));
        self.ranges.retain(|t, _| !hit(t));
        self.rels.retain(|r| !hit(&r.a) && !hit(&r.b));
        self.sums.retain(|s| !hit(&s.a) && !hit(&s.b));
        self.holes.retain(|(t, _)| !hit(t));
    }

    /// The integer local `local` was assigned its own value plus `k` (as in
    /// `i = i - 1`), now in `range`: its relations shift by `k` instead of
    /// being forgotten (`i - b <= c` becomes `i - b <= c + k`).
    pub fn shift(&mut self, local: LocalId, range: Option<Range>, k: i128) {
        let me = Term::Local(local);
        let shifted: Vec<Rel> = self
            .rels
            .iter()
            .filter_map(|r| {
                let c = if r.a == me {
                    r.c.checked_add(k)?
                } else if r.b == me {
                    r.c.checked_sub(k)?
                } else {
                    return None;
                };
                Some(Rel { c, ..*r })
            })
            .collect();
        // p*i + q*b <= c, with i = i' - k: p*i' + q*b <= c + p*k.
        let sums: Vec<Sum> = self
            .sums
            .iter()
            .filter_map(|s| {
                let m = if s.a == me {
                    s.p
                } else if s.b == me {
                    s.q
                } else {
                    return None;
                };
                Some(Sum {
                    c: s.c.checked_add(m.checked_mul(k)?)?,
                    ..*s
                })
            })
            .collect();
        let holes: Vec<(Term, i128)> = self
            .holes
            .iter()
            .filter(|(t, _)| *t == me)
            .filter_map(|&(t, v)| Some((t, v.checked_add(k)?)))
            .collect();
        self.forget_value(local, range);
        self.rels.extend(shifted);
        self.sums.extend(sums);
        for (term, value) in holes {
            self.apply(&[Fact::Hole { term, value }]);
        }
    }

    /// `to` was given the value of `from` plus `offset`: it has `from`'s
    /// holes, moved by `offset`.
    pub fn copy_holes(&mut self, from: Term, to: Term, offset: i128) {
        let holes: Vec<Fact> = self
            .holes
            .iter()
            .filter(|h| h.0 == from)
            .filter_map(|&(_, v)| {
                Some(Fact::Hole {
                    term: to,
                    value: v.checked_add(offset)?,
                })
            })
            .collect();
        self.apply(&holes);
    }

    /// Forget every fact about `local` (at the head of a loop that assigns
    /// it, or after a call that may change it). Whether it's assigned yet
    /// doesn't change.
    pub fn forget(&mut self, local: LocalId) {
        self.forget_value(local, None);
    }

    /// `local` is declared without a value: it must be assigned before it's
    /// read.
    pub fn declare_uninit(&mut self, local: LocalId) {
        self.forget_value(local, None);
        self.uninit.insert(local);
    }

    /// Whether `local` may not be assigned yet on some path to here.
    pub fn is_uninit(&self, local: LocalId) -> bool {
        !self.dead && self.uninit.contains(&local)
    }

    /// The locals that may not be assigned on some path to here.
    pub fn uninit_locals(&self) -> impl Iterator<Item = LocalId> + '_ {
        self.uninit.iter().copied()
    }

    /// Whether every fact of `self` about the locals `about` picks out also
    /// holds in `other` (a range end if `other`'s range, or its type's range
    /// `full` when `other` has none, is within it; a relation if
    /// [`Env::rel_through`] in `other` gives the same bound or a tighter
    /// one). Nothing needs to hold at a point no path reaches.
    pub fn holds_in(
        &self,
        about: impl Fn(LocalId) -> bool,
        full: impl Fn(Term) -> Range,
        other: &Env,
    ) -> bool {
        // Loosening against no edges only normalizes (a range as wide as its
        // type is the same as none).
        let kept = self.loosen(&about, &full, std::slice::from_ref(other), Loosen::Drop);
        kept.same(&self.loosen(&about, &full, &[], Loosen::Drop))
    }

    /// `self` with every fact about the locals `about` picks out weakened to
    /// hold at each of `edges` (the facts at a loop's back-edges): either
    /// [`Loosen::Drop`]ped when it doesn't hold at some edge, or loosened
    /// just enough to [`Loosen::Cover`] all of them. The two ends of a range
    /// are separate facts; a dropped end goes to the type's limit (`full`).
    /// Other facts are kept as they are.
    pub fn loosen(
        &self,
        about: impl Fn(LocalId) -> bool,
        full: impl Fn(Term) -> Range,
        edges: &[Env],
        how: Loosen,
    ) -> Env {
        let live: Vec<&Env> = edges.iter().filter(|e| !e.dead).collect();
        let mut out = Env {
            uninit: self.uninit.clone(),
            dead: self.dead,
            ..Env::default()
        };
        for (&term, &r) in &self.ranges {
            if !about(term.local()) {
                out.ranges.insert(term, r);
                continue;
            }
            let f = full(term);
            let (mut lo, mut hi) = (r.lo, r.hi);
            for e in &live {
                let er = e.range(term).unwrap_or(f);
                match how {
                    Loosen::Drop => {
                        if er.lo < r.lo {
                            lo = f.lo;
                        }
                        if er.hi > r.hi {
                            hi = f.hi;
                        }
                    }
                    Loosen::Cover => {
                        lo = lo.min(er.lo);
                        hi = hi.max(er.hi);
                    }
                }
            }
            let r = Range { lo, hi };
            if r != f {
                out.ranges.insert(term, r);
            }
        }
        for rel in &self.rels {
            if !about(rel.a.local()) && !about(rel.b.local()) {
                out.rels.push(*rel);
                continue;
            }
            // What the types alone give: a relation that weak is no fact.
            let (fa, fb) = (full(rel.a), full(rel.b));
            let by_types = fa.hi.checked_sub(fb.lo);
            let mut c = Some(rel.c);
            for e in &live {
                // As for ranges, a term with no known range has its type's.
                let ea = e.range(rel.a).unwrap_or(fa);
                let eb = e.range(rel.b).unwrap_or(fb);
                let ec = match (e.rel_through(rel.a, rel.b), ea.hi.checked_sub(eb.lo)) {
                    (Some(x), Some(y)) => Some(x.min(y)),
                    (x, y) => x.or(y),
                };
                c = match (how, c, ec) {
                    (Loosen::Drop, Some(c), Some(ec)) if ec <= c => Some(c),
                    (Loosen::Cover, Some(c), Some(ec)) => Some(c.max(ec)),
                    _ => None,
                };
            }
            if let Some(c) = c
                && by_types.is_none_or(|t| c < t)
            {
                out.rels.push(Rel { c, ..*rel });
            }
        }
        // A sum, as a relation: what each edge gives, a term with no known
        // range having its type's.
        for sum in &self.sums {
            if !about(sum.a.local()) && !about(sum.b.local()) {
                out.sums.push(*sum);
                continue;
            }
            let form = sum.fact();
            let by_types = Env::default().gives(&form, Some(&full));
            let mut c = Some(sum.c);
            for e in &live {
                let ec = e.gives(&form, Some(&full));
                c = match (how, c, ec) {
                    (Loosen::Drop, Some(c), Some(ec)) if ec <= c => Some(c),
                    (Loosen::Cover, Some(c), Some(ec)) => Some(c.max(ec)),
                    _ => None,
                };
            }
            if let Some(c) = c
                && by_types.is_none_or(|t| c < t)
            {
                out.sums.push(Sum { c, ..*sum });
            }
        }
        // A hole can't be loosened: it's kept if every edge has it.
        for &(term, value) in &self.holes {
            if !about(term.local()) || live.iter().all(|e| e.excludes(term, value)) {
                out.holes.push((term, value));
            }
        }
        out
    }

    /// `self` (a candidate head, `N`) with the range ends of the terms
    /// `about` picks out moved in to their thresholds: for each `(term, k)`
    /// of `thresholds`, the largest `k` at least `entry`'s upper end (the
    /// facts before the loop; the type's limit `full` if none) becomes the
    /// upper end if it's below it, and the smallest `k` at most `entry`'s
    /// lower end the lower end if it's above it.
    pub fn to_thresholds(
        &self,
        entry: &Env,
        about: impl Fn(LocalId) -> bool,
        full: impl Fn(Term) -> Range,
        thresholds: &[(Term, i128)],
    ) -> Env {
        let mut out = self.clone();
        let mut terms: Vec<Term> = Vec::new();
        for &(term, _) in thresholds {
            if !terms.contains(&term) {
                terms.push(term);
            }
        }
        for term in terms {
            if !about(term.local()) {
                continue;
            }
            let f = full(term);
            let e = entry.range(term).unwrap_or(f);
            let mut r = self.range(term).unwrap_or(f);
            let ks = thresholds.iter().filter(|t| t.0 == term).map(|t| t.1);
            if let Some(k) = ks.clone().filter(|&k| k >= e.hi).max()
                && k < r.hi
            {
                r.hi = k;
            }
            if let Some(k) = ks.filter(|&k| k <= e.lo).min()
                && k > r.lo
            {
                r.lo = k;
            }
            if r != f && r.lo <= r.hi {
                out.ranges.insert(term, r);
            }
        }
        out
    }

    /// Whether two sets of facts are the same.
    pub fn same(&self, other: &Env) -> bool {
        self.dead == other.dead
            && self.uninit == other.uninit
            && self.ranges == other.ranges
            && self.rels.len() == other.rels.len()
            && self.rels.iter().all(|r| other.rels.contains(r))
            && self.sums.len() == other.sums.len()
            && self.sums.iter().all(|r| other.sums.contains(r))
            && self.holes.len() == other.holes.len()
            && self.holes.iter().all(|h| other.holes.contains(h))
    }

    pub fn apply(&mut self, facts: &[Fact]) {
        for fact in facts {
            match *fact {
                Fact::Narrow { term, bound, full } => {
                    let current = self.range(term).unwrap_or(full);
                    match current.intersect(bound) {
                        Some(r) => {
                            self.ranges.insert(term, r);
                            self.settle(term);
                        }
                        None => self.dead = true,
                    }
                }
                Fact::Hole { term, value } => {
                    if !self.excludes(term, value) {
                        self.holes.push((term, value));
                        self.settle(term);
                    }
                }
                Fact::Rel { a, b, c } => {
                    if self.rel(a, b).is_none_or(|old| c < old) {
                        self.rels.retain(|r| !(r.a == a && r.b == b));
                        self.rels.push(Rel { a, b, c });
                    }
                }
                Fact::Sum { a, p, b, q, c } => {
                    if self.sum(a, p, b, q).is_none_or(|old| c < old) {
                        self.sums
                            .retain(|s| !(s.a == a && s.p == p && s.b == b && s.q == q));
                        self.sums.push(Sum { a, p, b, q, c });
                    }
                }
            }
        }
    }

    /// Keep `term`'s holes inside its known range: a hole at an end moves
    /// the end past it (a range that's only a hole can't be reached).
    fn settle(&mut self, term: Term) {
        let Some(mut r) = self.range(term) else {
            return;
        };
        loop {
            if self.holes.contains(&(term, r.lo)) && r.lo < r.hi {
                r.lo += 1;
            } else if self.holes.contains(&(term, r.hi)) && r.lo < r.hi {
                r.hi -= 1;
            } else {
                break;
            }
        }
        if r.lo == r.hi && self.holes.contains(&(term, r.lo)) {
            self.dead = true;
        }
        self.ranges.insert(term, r);
        self.holes
            .retain(|&(t, v)| t != term || (r.lo < v && v < r.hi));
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
        // A relation either side knows directly, if both give it somehow.
        let mut rels: Vec<Rel> = Vec::new();
        for r in a.rels.iter().chain(&b.rels) {
            if rels.iter().any(|k| k.a == r.a && k.b == r.b) {
                continue;
            }
            if let (Some(ca), Some(cb)) = (a.diff(r.a, r.b), b.diff(r.a, r.b)) {
                rels.push(Rel {
                    c: ca.max(cb),
                    ..*r
                });
            }
        }
        // A sum either side knows, if both give it (directly or by ranges).
        let mut sums: Vec<Sum> = Vec::new();
        for s in a.sums.iter().chain(&b.sums) {
            if sums
                .iter()
                .any(|k| k.a == s.a && k.p == s.p && k.b == s.b && k.q == s.q)
            {
                continue;
            }
            let form = s.fact();
            if let (Some(ca), Some(cb)) = (a.gives(&form, None), b.gives(&form, None)) {
                sums.push(Sum {
                    c: ca.max(cb),
                    ..*s
                });
            }
        }
        // A local is assigned after the join only if it is on both paths.
        let uninit = a.uninit.union(&b.uninit).copied().collect();
        let mut holes: Vec<(Term, i128)> = Vec::new();
        for &h in a.holes.iter().chain(&b.holes) {
            if a.excludes(h.0, h.1) && b.excludes(h.0, h.1) && !holes.contains(&h) {
                holes.push(h);
            }
        }
        let mut out = Env {
            ranges,
            rels,
            sums,
            uninit,
            holes,
            dead: false,
        };
        let terms: Vec<Term> = out.holes.iter().map(|h| h.0).collect();
        for term in terms {
            out.settle(term);
        }
        out
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
            form: Some(Form::of(Linear::of(term))),
            quot: None,
            range: U32,
            full: U32,
        }
    }

    /// `term + k`, for a term in `0..=u32::MAX - k`.
    fn plus(term: Term, k: i128) -> Side {
        let lin = Linear { term, offset: k };
        Side {
            term: Some(lin),
            form: Some(Form::of(lin)),
            quot: None,
            range: Range { lo: k, hi: U32.hi },
            full: U32,
        }
    }

    /// `k - term`, for a term in `0..=k`.
    fn minus(k: i128, term: Term) -> Side {
        let form = Form::constant(k).minus(Form::of(Linear::of(term)));
        Side {
            term: None,
            form,
            quot: None,
            range: Range { lo: 0, hi: k },
            full: U32,
        }
    }

    fn var(local: LocalId) -> Side {
        side(Term::Local(local))
    }

    fn konst(v: i128) -> Side {
        Side {
            term: None,
            form: Some(Form::constant(v)),
            quot: None,
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
    fn shifting_keeps_relations() {
        // i == len(xs) (from `var i = xs.len`), then `i = i - 1`.
        let mut env = Env::default();
        env.apply(&comparison(CmpOp::Eq, var(0), side(Term::Len(1))).when_true);
        env.shift(0, Some(Range { lo: 0, hi: 9 }), -1);
        assert_eq!(env.rel(Term::Local(0), Term::Len(1)), Some(-1));
        assert_eq!(env.rel(Term::Len(1), Term::Local(0)), Some(1));
        assert_eq!(env.range(Term::Local(0)), Some(Range { lo: 0, hi: 9 }));
    }

    fn full(_: Term) -> Range {
        U32
    }

    fn exact(local: LocalId, v: i128) -> Env {
        let mut env = Env::default();
        env.apply(&comparison(CmpOp::Eq, var(local), konst(v)).when_true);
        env
    }

    #[test]
    fn loosening_drops_or_covers() {
        // Before a loop: i == 21 and j == 3; the loop assigns only i.
        let mut entry = exact(0, 21);
        entry.apply(&comparison(CmpOp::Eq, var(1), konst(3)).when_true);
        let about = |l: LocalId| l == 0;
        let edges = [exact(0, 20), Env::unreachable()];
        let dropped = entry.loosen(about, full, &edges, Loosen::Drop);
        assert_eq!(dropped.range(Term::Local(0)), Some(Range { lo: 0, hi: 21 }));
        assert_eq!(dropped.range(Term::Local(1)), Some(Range::exact(3)));
        let covered = entry.loosen(about, full, &edges, Loosen::Cover);
        assert_eq!(
            covered.range(Term::Local(0)),
            Some(Range { lo: 20, hi: 21 })
        );
        // A range as wide as the type is no fact.
        let wide = [exact(0, 30), exact(0, 0)];
        let gone = entry.loosen(about, full, &wide, Loosen::Drop);
        assert_eq!(gone.range(Term::Local(0)), None);
        // A relation stays only if every edge knows it (here, through len).
        let mut rel = Env::default();
        rel.apply(&comparison(CmpOp::Le, var(0), side(Term::Len(1))).when_true);
        let mut edge = Env::default();
        edge.apply(&comparison(CmpOp::Lt, var(0), var(2)).when_true);
        edge.apply(&comparison(CmpOp::Le, var(2), side(Term::Len(1))).when_true);
        let kept = rel.loosen(about, full, std::slice::from_ref(&edge), Loosen::Drop);
        assert_eq!(kept.rel(Term::Local(0), Term::Len(1)), Some(0));
        let lost = rel.loosen(about, full, &[Env::default()], Loosen::Cover);
        assert_eq!(lost.rel(Term::Local(0), Term::Len(1)), None);
    }

    #[test]
    fn holding_at_a_back_edge() {
        let mut head = Env::default();
        head.apply(&comparison(CmpOp::Le, var(0), konst(21)).when_true);
        let about = |l: LocalId| l == 0;
        assert!(head.holds_in(about, full, &exact(0, 20)));
        assert!(!head.holds_in(about, full, &exact(0, 22)));
        assert!(!head.holds_in(about, full, &Env::default()));
        assert!(head.holds_in(about, full, &Env::unreachable()));
        // Facts about other locals don't need to hold.
        assert!(exact(1, 5).holds_in(about, full, &Env::default()));
        assert!(head.same(&head.clone()));
        assert!(!head.same(&exact(0, 21)));
    }

    const I32: Range = Range {
        lo: i32::MIN as i128,
        hi: i32::MAX as i128,
    };

    fn signed(local: LocalId) -> Side {
        let lin = Linear::of(Term::Local(local));
        Side {
            term: Some(lin),
            form: Some(Form::of(lin)),
            quot: None,
            range: I32,
            full: I32,
        }
    }

    #[test]
    fn holes() {
        // b == 0 is false: a hole at 0.
        let t = Term::Local(0);
        let mut env = Env::default();
        env.apply(&comparison(CmpOp::Eq, signed(0), konst(0)).when_false);
        assert!(env.excludes(t, 0));
        assert!(!env.excludes(t, 1));
        assert_eq!(env.range(t), None);
        // Narrowing to the hole moves past it: b >= 0 gives 1..
        let mut pos = env.clone();
        pos.apply(&comparison(CmpOp::Ge, signed(0), konst(0)).when_true);
        assert_eq!(pos.range(t), Some(Range { lo: 1, hi: I32.hi }));
        // Shifting moves holes, assigning forgets them.
        let mut moved = env.clone();
        moved.shift(0, None, 1);
        assert!(moved.excludes(t, 1) && !moved.excludes(t, 0));
        moved.assign(0, None);
        assert!(!moved.excludes(t, 1));
        // A join keeps a hole both sides exclude, by a hole or a range.
        let joined = Env::join(env.clone(), exact(0, 5));
        assert!(joined.excludes(t, 0));
        let joined = Env::join(env.clone(), Env::default());
        assert!(!joined.excludes(t, 0));
        // At a loop head, a hole holds where an edge excludes the value.
        let about = |l: LocalId| l == 0;
        assert!(env.holds_in(about, full, &exact(0, 3)));
        assert!(!env.holds_in(about, full, &Env::default()));
        // A range that's only a hole can't be reached.
        let mut dead = exact(0, 0);
        dead.apply(&[Fact::Hole { term: t, value: 0 }]);
        assert!(dead.dead);
    }

    #[test]
    fn join_keeps_relations_given_through_a_term() {
        // One branch: start == i directly. The other: start == pos, i == pos.
        let (i, start, pos) = (0, 1, 2);
        let mut a = Env::default();
        a.apply(&comparison(CmpOp::Eq, var(start), var(i)).when_true);
        let mut b = Env::default();
        b.apply(&comparison(CmpOp::Eq, var(start), var(pos)).when_true);
        b.apply(&comparison(CmpOp::Eq, var(i), var(pos)).when_true);
        let j = Env::join(a, b);
        assert_eq!(j.rel(Term::Local(start), Term::Local(i)), Some(0));
        assert_eq!(j.rel(Term::Local(i), Term::Local(start)), Some(0));
        // Known ranges give a bound too: 0..=3 and 5..=9 give a - b <= -2.
        let mut r = exact(0, 3);
        r.apply(&comparison(CmpOp::Ge, var(1), konst(5)).when_true);
        r.apply(&comparison(CmpOp::Le, var(1), konst(9)).when_true);
        assert_eq!(r.diff(Term::Local(0), Term::Local(1)), Some(-2));
        assert_eq!(Env::default().diff(Term::Local(0), Term::Local(1)), None);
    }

    #[test]
    fn reading_through_relations() {
        // n - i <= 0 and i in 0..=9: n reads as 0..=9.
        let (n, i) = (0, 1);
        let mut env = Env::default();
        env.apply(&comparison(CmpOp::Le, var(n), var(i)).when_true);
        env.apply(&comparison(CmpOp::Lt, var(i), konst(10)).when_true);
        assert_eq!(
            env.range_via(Term::Local(n), full),
            Some(Range { lo: 0, hi: 9 })
        );
        // Only one step: m <= n doesn't go through n's narrowed range.
        env.apply(&comparison(CmpOp::Le, var(2), var(n)).when_true);
        assert_eq!(
            env.range_via(Term::Local(2), full),
            Some(Range { lo: 0, hi: U32.hi })
        );
        assert_eq!(Env::default().range_via(Term::Local(n), full), None);
    }

    #[test]
    fn thresholds_tighten_ends() {
        // E: sp == 0; N: sp in 0..=MAX-1; thresholds 2 and 16 (and 0).
        let sp = Term::Local(0);
        let entry = exact(0, 0);
        let mut n = Env::default();
        n.apply(&comparison(CmpOp::Lt, var(0), konst(U32.hi)).when_true);
        let about = |l: LocalId| l == 0;
        let ks = [(sp, 2), (sp, 16), (sp, 0), (Term::Local(1), 5)];
        let t = n.to_thresholds(&entry, about, full, &ks);
        assert_eq!(t.range(sp), Some(Range { lo: 0, hi: 16 }));
        assert_eq!(t.range(Term::Local(1)), None);
        // No threshold at least E's upper end: nothing changes.
        let t = n.to_thresholds(&exact(0, 20), about, full, &ks);
        assert!(t.same(&n));
    }

    #[test]
    fn forms() {
        let (a, b) = (Term::Local(0), Term::Local(1));
        let fa = Form::of(Linear::of(a));
        let fb = Form::of(Linear::of(b));
        // a + b - a is b; a third term doesn't fit.
        assert_eq!(fa.plus(fb).and_then(|f| f.minus(fa)), Some(fb));
        assert_eq!(fa.plus(fb).and_then(|f| f.plus(side_form(2))), None);
        assert_eq!(fa.minus(fa).map(|f| f.term_count()), Some(0));
        assert_eq!(
            fa.scale(10)
                .and_then(|f| f.plus(fb))
                .map(|f| f.term_count()),
            Some(2)
        );
    }

    #[test]
    fn one_term_forms_narrow() {
        // -100 < b: b >= -99. 10 - b >= 3: b <= 7. -10 * b <= -25: b >= 3.
        let b = Term::Local(1);
        let mut env = Env::default();
        env.apply(&comparison(CmpOp::Lt, konst(-100), signed(1)).when_true);
        assert_eq!(env.range(b).map(|r| r.lo), Some(-99));
        let mut env = Env::default();
        env.apply(&comparison(CmpOp::Ge, minus(10, b), konst(3)).when_true);
        assert_eq!(env.range(b), Some(Range { lo: 0, hi: 7 }));
        let mut env = Env::default();
        let f = side_form(1).scale(-10).expect("fits");
        env.apply(&f.le(-25, I32));
        assert_eq!(env.range(b).map(|r| r.lo), Some(3));
        env.apply(&f.le(25, I32));
        assert_eq!(env.range(b).map(|r| r.lo), Some(3));
    }

    fn side_form(local: LocalId) -> Form {
        Form::of(Linear::of(Term::Local(local)))
    }

    #[test]
    fn sums_from_comparisons() {
        // a > MAX - b is false: a + b <= MAX.
        let (a, b) = (Term::Local(0), Term::Local(1));
        let max = U32.hi;
        let f = comparison(CmpOp::Gt, var(0), minus(max, b));
        let mut env = Env::default();
        env.apply(&f.when_false);
        let sum = fa_plus_fb(a, 1, b, 1, 0);
        assert_eq!(env.form_bounds(sum), (None, Some(max)));
        // With a constant: a + b + 3 <= MAX + 3, and 2a + 2b <= 2 * MAX.
        assert_eq!(env.form_bounds(fa_plus_fb(a, 1, b, 1, 3)).1, Some(max + 3));
        assert_eq!(env.form_bounds(fa_plus_fb(a, 2, b, 2, 0)).1, Some(2 * max));
        // a - b isn't bounded by it.
        assert_eq!(env.form_bounds(fa_plus_fb(a, 1, b, -1, 0)), (None, None));
        // When true, a + b >= MAX + 1.
        let mut env = Env::default();
        env.apply(&f.when_true);
        assert_eq!(env.form_bounds(sum), (Some(max + 1), None));
        // Assigning a forgets it; shifting a moves it.
        let mut env = Env::default();
        env.apply(&f.when_false);
        env.shift(0, None, 2);
        assert_eq!(env.form_bounds(sum).1, Some(max + 2));
        env.assign(1, None);
        assert_eq!(env.form_bounds(sum).1, None);
    }

    fn fa_plus_fb(a: Term, p: i128, b: Term, q: i128, k: i128) -> Form {
        Form::of(Linear::of(a))
            .scale(p)
            .and_then(|x| x.plus(Form::of(Linear::of(b)).scale(q)?))
            .and_then(|x| x.plus(Form::constant(k)))
            .expect("fits")
    }

    #[test]
    fn sums_from_quotients() {
        // v <= (MAX - d) / 10: 10v + d <= MAX.
        let (v, d) = (Term::Local(0), Term::Local(1));
        let max = u64::MAX as i128;
        let f = Form::constant(max)
            .minus(Form::of(Linear::of(d)))
            .expect("fits");
        let q = Side {
            term: None,
            form: None,
            quot: Some((f, 10)),
            range: Range {
                lo: (max - 9) / 10,
                hi: max / 10,
            },
            full: Range { lo: 0, hi: max },
        };
        let x = Side {
            full: Range { lo: 0, hi: max },
            range: Range { lo: 0, hi: max },
            ..var(0)
        };
        let mut env = Env::default();
        env.apply(&comparison(CmpOp::Le, x, q).when_true);
        assert_eq!(env.form_bounds(fa_plus_fb(v, 10, d, 1, 0)).1, Some(max));
        // v > (MAX - d) / 10: 10v + d >= MAX + 1 (floor(F / 10) < v means
        // F < 10v).
        let mut env = Env::default();
        env.apply(&comparison(CmpOp::Le, x, q).when_false);
        assert_eq!(env.form_bounds(fa_plus_fb(v, 10, d, 1, 0)).0, Some(max + 1));
    }

    #[test]
    fn joining_sums() {
        let (a, b) = (Term::Local(0), Term::Local(1));
        let sum = fa_plus_fb(a, 1, b, 1, 0);
        let mut x = Env::default();
        x.apply(&comparison(CmpOp::Le, var(0), minus(10, b)).when_true);
        // The other side knows a + b <= 12 by ranges.
        let mut y = exact(0, 5);
        y.apply(&comparison(CmpOp::Le, var(1), konst(7)).when_true);
        let j = Env::join(x.clone(), y);
        assert_eq!(j.form_bounds(sum).1, Some(12));
        // Without ranges on one side, it's gone.
        let j = Env::join(x.clone(), Env::default());
        assert_eq!(j.form_bounds(sum).1, None);
        // At a loop head: kept if the back-edge gives it.
        let about = |l: LocalId| l == 0;
        assert!(x.holds_in(about, full, &x.clone()));
        assert!(!x.holds_in(about, full, &Env::default()));
    }

    #[test]
    fn contradiction_is_dead() {
        let mut env = Env::default();
        env.apply(&comparison(CmpOp::Lt, var(0), konst(0)).when_true);
        assert!(env.dead);
    }
}
