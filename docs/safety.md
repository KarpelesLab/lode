# Safety

This is the central guarantee of the language. Most other design decisions
follow from it.

## The guarantee

**Status:** Proposed

> In safe code, a program has **no undefined behavior**, and it has **no
> implicit crash paths**. Every way an operation can fail is visible in its
> type, and the caller must deal with it.

"No implicit crash paths" means that indexing, arithmetic, conversions and
unwrapping never insert a hidden panic or abort. An operation either:

1. is **proven** to succeed at compile time,
2. returns a value that encodes failure (`?T`, or an error through `throws`), or
3. has a **defined** alternative behavior that the programmer chose explicitly
   (wrapping, saturating and so on).

## What can still terminate a program

Some failures cannot be ruled out by a compiler. We name them rather than
pretend otherwise:

| Cause | Handling |
| --- | --- |
| Infinite loop, deadlock | Not prevented (halting problem). Out of scope. |
| Stack overflow | See [Stack bounds](#stack-bounds). Where no bound is proven, overflow hits a guard and gives a *defined* abort, never memory corruption. |
| Out of memory | Allocation is fallible. A project can choose an abort-on-OOM policy (see [memory.md](memory.md#out-of-memory)). |
| Hardware faults, killed by the OS | Outside the program's control. |
| Explicit `abort()` | Allowed, but visible in the source and easy to find. |
| A bug inside `unsafe` code | The trusted boundary. See below. |

## Failure sources in detail

| Source | Rule | Doc |
| --- | --- | --- |
| Null | There is no null. Absence is `?T`. | [types.md](types.md#optional) |
| Array or slice index | `a[i]` needs a proof that `i < a.len`. Otherwise use `a.get(i)`, which returns `?T`. | [Proof obligations](#proof-obligations) |
| Slice | `a[i..j]` needs a proof that `0 <= i <= j <= a.len`. | [Proof obligations](#proof-obligations) |
| Integer overflow | `+ - *` need a proof that the result fits. Otherwise use a wrapping, saturating or checked operator. | [types.md](types.md#arithmetic) |
| Division by zero | `/` and `%` need a proof that the divisor is non-zero (and for signed types, not `MIN / -1`). | [types.md](types.md#arithmetic) |
| Narrowing conversion | `u8(x)` needs a proof that `x` fits. Otherwise use `.wrap()`, `.saturate()` or `.try()`. | [types.md](types.md#conversions) |
| Float to int | Always defined: saturating, and NaN gives 0. No proof needed. | [types.md](types.md#floats) |
| Use after free, double free, dangling reference | Ruled out by the memory model. | [memory.md](memory.md) |
| Data race | Ruled out by exclusivity and `Send`-like rules. | [concurrency.md](concurrency.md) |
| Uninitialized read | Every variable is definitely assigned before use (flow analysis, as in Go and Rust). An `@uninit` field is the one exception, inside `unsafe`. | [memory.md](memory.md#uninitialized-buffers) |
| Unhandled error | A `throws` call must be handled with `try`, `catch` or `match`. | [errors.md](errors.md) |
| Non-exhaustive match | Compile error. | [types.md](types.md#enums-sum-types) |

## Proof obligations

**Status:** Proposed

Some operations (`a[i]`, `a + b`, `a / b`, `u8(x)`) produce a **proof
obligation**. The compiler discharges it from facts it knows at that point in
the program:

- conditions that dominate the operation (`if i < a.len { ... a[i] ... }`)
- loop induction (`for i in 0..a.len` gives `0 <= i < a.len`)
- value ranges of types and constants (`x: u8` gives `0 <= x <= 255`)
- lengths of arrays and slices, including fixed `[N]T` sizes
- refinements in the function's signature (see
  [Refinements in types](#refinements-in-types))

```
fn sum(values: []u32) throws(Overflow) -> u32 {
	var total: u32 = 0
	for v in values {
		total = try total.checked_add(v)    // no proof possible here: explicit
	}
	return total
}

fn first_or_zero(values: []u32) -> u32 {
	if values.len > 0 {
		return values[0]                     // proven by the condition
	}
	return 0
}
```

When the obligation cannot be discharged, the compiler gives an error that
names the missing fact and lists the explicit alternatives.

Code that only runs while compiling (a constant's value, an `if comptime`
condition) never runs in the program, so it has no crash path to rule out:
its obligations are discharged by running it, and one that fails is an
error at the operation ([generics.md](generics.md#proof-obligations-in-compile-time-code);
implemented in M7d). The functions it calls are proven like any other.

### The checker must be predictable

**Status:** Proposed, important

Whether a program compiles **must not** depend on the optimization level, on
solver timeouts or on the compiler version's heuristics. Otherwise a compiler
upgrade could reject code that used to compile.

So:

- The acceptance check is a **specified, decidable analysis**: flow-sensitive
  ranges over the facts listed above. It is written down in the language spec,
  and every compiler must accept exactly the programs the spec accepts.
- LatticeFoundry's lattice engine and SMT solver (`z3rs`) sit **below** that
  line. They remove runtime checks in explicit fallback code, verify the
  optimizer, and may offer *suggestions* in diagnostics. They never decide
  whether a program is accepted.

### The fact language

**Status:** Proposed; implemented in the compiler (`src/sema/facts.rs`)

The checker tracks facts about **terms**. A term is an integer local, the
length of a view local (`xs.len` of a slice or `str` parameter or local), or
an integer field of a struct local, reached through fields only (`p.x`,
`r.min.y`, but not `ps[i].x`). An
expression can be a term plus a constant: `i`, `i + 1`, `xs.len - 1`. More
generally, it can be a **form**: a constant plus at most two terms, each
times a constant other than 0: `9 - d`, `a + b`, `10 * v + d`. There are
four kinds of fact:

- **Ranges:** a term lies in `lo..=hi`.
- **Holes:** a term is not `k`, for a constant `k` inside its range
  (`b != 0` for a signed `b`).
- **Relations:** for two terms, `a - b <= c`.
- **Sums:** for two terms, `p*a + q*b <= c`, with constants `p` and `q`
  other than 1 and -1 (that's a relation, either way round): `a + b <= c`,
  `-a - b <= c` (`a + b >= -c`), `10*v + d <= c`. They're kept divided by
  the largest number that divides both `p` and `q` (`2*a + 2*b <= 5` is
  `a + b <= 2`). See [Sums](#sums).

All are decidable and cheap, and the rules for how they flow are fixed:

| Where | What the checker learns |
| --- | --- |
| A literal or constant | Its exact value |
| An expression | The range computed from its operands' ranges (e.g. `a + b` from both ranges), as below |
| `a / b`, `a >> n` | For `/`, on each side of 0 of the divisor's range, the four quotients of the ranges' ends (rounded toward zero) bound the result; the two sides are joined. For `>>`, the four `a.lo >> n.lo` ... `a.hi >> n.hi` (rounded down). So `x / 10` and `x >> 4` of a `u64` are at most a tenth and a sixteenth of the largest `u64`. When `a` is a term plus a constant and can't be negative, and `b >= 1` (`n >= 0`), the result is also at most `a`; when `a >= 1` and `b >= 2` (`n >= 1`), at most `a - 1`. `let mid = xs.len / 2` gives the relation `mid <= xs.len - 1` when `xs.len >= 1` |
| `a % b` | Smaller in size than `b` can be, with the sign of `a`: in `-m..=m`, with `m` the largest size of `b` minus 1, and 0 for an end where `a` can't have that sign. It doesn't depend on `a`'s size, so `a = (a + x) % m` has the same range at every iteration of a loop |
| `a & b`, `a \| b`, `a ^ b` | `&`: with a non-negative operand, `0..=` its largest value (the smaller of both, if both are). `\|`, `^`: when both are non-negative, at most the smallest `2^k - 1` that's at least both largest values; `\|` is also at least the larger of both smallest values. Otherwise, the type's range |
| `a.len` | For an array, its constant length. For a slice or `str`, a term, in `0..=` the largest `isize` of the target. For a slice `a[i..j]` that isn't a local, the range of `j - i` (below), and with a constant `i`, `j - i` as a term plus a constant: `xs[..n].len` is `n`, `xs[1..].len` is `xs.len - 1` |
| `a[i..j]` | Its length is `j - i` (`j` is `a.len` when left out, `i` is 0): between `j.lo - i.hi` and `j.hi - i.lo`, narrowed by a relation between `i` and `j` (`j - i <= c` bounds it above by `c`, `i - j <= c` below by `-c`), and never below 0 |
| `T[i]` of an array constant `T` (literal or computed by a function) | Between the smallest and the largest of the elements `i` can pick (of all the elements, past 4096 of them): with `const DAYS: [12]u8 = [31, 28, ...]`, `DAYS[m]` is `28..=31`, and `DAYS[1]` is 28. Other elements have no facts |
| A struct literal | In `let p = Point{x: 1, y: v}` (or `p = ...`), the fields given as constants: here `p.x` is 1. An integer field of a struct constant is its value |
| `p.x = v`, `p.a = q` | The value's range for the field assigned; everything else about it (or about the fields of a struct field) is forgotten. Assigning a whole struct forgets all its fields. |
| `let` / `var` / assignment | The value's range. A term plus a constant is related to the term (`let last = xs.len - 1` gives `last - xs.len <= -1`), and has its holes, moved by the constant. A form of one other term is related to it by a sum, both ways: `let x = 250 - b` gives `x + b <= 250` and `x + b >= 250`. A value known to be at most a term plus a constant (from `/` or `>>`, above) is related to it that way. A view of a whole `[N]T` array has length `N`, and a copy of a view has its length. A slice `s = a[i..j]` has the range of `j - i` as its length, and when `j` is a term plus a constant (`a.len` for `a[i..]`), the relations `j - i.hi <= s.len <= j - i.lo`; so with a constant `i`, `s.len == j - i`. Assigning forgets every fact involving the variable, and for a view, its length, except that assigning a variable itself plus a constant (`i = i - 1`, `i += 2`) shifts its relations, sums and holes by the constant (`i <= xs.len` becomes `i - xs.len <= -1`; `p*i + q*b <= c` becomes `p*i + q*b <= c + p*k` for `i += k`). |
| `if cond` | Inside the branch, the facts of `cond` being true; in `else`, of it being false |
| After an `if` | If one branch always leaves (`return`, `throw`, `break`, `continue`, a call to a `never` function), the other branch's facts. Otherwise, what both branches agree on: ranges widened to cover both, each relation or sum one branch knows directly that the other gives too (at the weaker bound; see below for what a point gives), and holes at values neither branch's facts allow. |
| `match`, `if let`, `let ... else` | Each arm starts with the facts from before. In a `match` on an integer that is a term (plus a constant), an arm also knows the value is between the smallest and the largest of its pattern's values, and that no earlier arm matched it: a value or a range at an end of what's left narrows the range, a single value inside it is a hole (`0 => ...` then `_ => ...`: in `_`, `k != 0`). After, the arms that don't always leave are joined, as after an `if`. Payload values have no facts. A `match` on a call that throws is the same, with the arms `ok` and `err`. |
| A call `f(&x)`, `p.scale(2)` | A call changes only the places passed `inout` or `set` (with `&`, or as the receiver of a method that takes `inout self`): what was known about each (a variable, or a struct field and the fields in it) is forgotten. A slice's length doesn't change, and elements have no facts. A variable passed `set` is assigned, with nothing known ([memory.md](memory.md#parameter-conventions-in-the-compiler-today)). |
| `try f()`, `throw` | The error leaves the function, so it adds nothing to the facts after. After `try`, the facts are those after the call. `throw` always leaves, like `return`. |
| A call to a `never` function | It doesn't return ([types.md](types.md#never-in-the-compiler-today)): the point after it can't be reached, and it leaves like `return`. In `opt ?? fail()`, only the facts from before `fail()` remain after the `??`. |
| `f() catch e { ... }`, `f() catch v` | The block (or the value `v`) starts with the facts after the call. After, the block's facts are joined with the call's, as after an `if` without `else`; a block that always leaves adds nothing. A `break` or `continue` in it is a loop exit like any other. |
| `defer`, `errdefer` | The body is checked where it's written, knowing the facts there about the variables nothing after it in the block assigns. It can't assign variables declared outside it (or pass them `inout` or `set`), so running it changes no facts. |
| `a && b`, `a \|\| b` | `b` is checked knowing `a` is true (`&&`) or false (`\|\|`). After, what `b` may change is forgotten. |
| `a ?? b` | After, what holds whether `b` ran or not: the facts before `b` joined with those after it |
| A comparison `x < y` (and `<=`, `>`, `>=`, `==`) | Each side narrows by the other's range; between two terms (plus constants), a relation: `i + 1 < xs.len` gives `i - xs.len <= -2`. More generally, when both sides are forms and `x - y` has at most two terms, `x - y <= c` gives a relation or a sum for two terms, and a range for one (`10 - d >= 3` gives `d <= 7`); a side can also be a quotient (see [Sums](#sums)). `x != k` (and `x == k` being false), with `k` a single value: when `k` is at an end of `x`'s range, the range narrows past it; when it's inside, a hole at `k`. A range that narrows to a hole's value moves past it too. |
| The head of a loop | The facts before the loop, with those about the variables the loop assigns kept as far as every iteration keeps them: see [Facts through loops](#facts-through-loops) |
| `while cond` | The body knows `cond` is true. After the loop, what the head and `cond` being false give, joined (as after an `if`) with the facts at each `break` |
| `loop` | After the loop, the facts at its `break`s, joined. Without a `break`, the code after it can't be reached. |
| `for i in a..b` | In the body, `i` lies in `a.lo..=b.hi - 1`, and when `a` or `b` is a term (plus a constant) the body doesn't assign, `a <= i` and `i < b` as relations. So `for i in 0..xs.len` proves `xs[i]`. After the loop, the head facts, with `i` past the end: in `b.lo..=b.hi` (`..=max(a.hi, b.hi)` unless `a.hi <= b.lo` or a relation gives `a <= b`), and when `b` is a term the body doesn't assign, `b <= i`, and `i <= b` in the same case; joined with the facts at each `break`. (`i` itself can't be used after the loop, but relations go through it.) |
| `for x in xs` | The same as `for` over `0..xs.len` with a hidden index, which proves the hidden `xs[index]` that gives `x` |
| `x + y`, `x - y`, `x * k` | A proven `+` or `-` of two forms, or `*` of a form by a constant, is a form if it has at most two terms. A form of two terms is bounded by a relation or a sum that matches it (see [Sums](#sums)), besides its operands' ranges: `y <= x` proves `x - y` doesn't go below zero, and `a + b <= MAX` proves `a + b` |
| Reading a term | Its range, narrowed by each of its relations and the other term's range (or its type's): `a - b <= c` gives `a <= b.hi + c` and `b >= a.lo - c`. One step: the other term's range isn't narrowed in turn. So `n <= i` and `i < xs.len` give `n` below the largest `isize`. |

A relation can also come from two known relations through one other term:
`i < n` and `n == xs.len` (from `let n = xs.len`) give `i < xs.len`. Only
one step: longer chains are not followed, which keeps the check cheap and
easy to predict. Where facts are compared or joined (after an `if`, at a
loop's head), what a point **gives** for `a - b` is the tightest of a
relation, a chain of two through one other term, and, when it knows ranges
for both, `a.hi - b.lo`.

#### Sums

The rules for forms and sums, exactly:

- **Forms.** A literal or a constant is a form (a constant). So is a term
  plus a constant, and a lossless conversion of a form. `x + y` and `x - y`
  of two forms, and `x * k` or `k * x` of a form and a single value `k`,
  are forms when the operation is proven (not `+%` or `+|`) and the result
  has at most two terms (terms whose coefficients add up to 0 drop out:
  `(a + b) - a` is `b`). Nothing else is a form.
- **Quotients.** `F / m` of a form `F` with at least one term that can't be
  negative (its range starts at 0 or more), by a single value `m >= 1`, is a
  quotient: it rounds toward zero, which for `F >= 0` is down. A quotient is
  only used in a comparison.
- **From a comparison.** `x <= y + c` (from `<`, `<=`, `>`, `>=`, `==`, true
  or false, as for relations) gives, when both sides are forms, the facts of
  the form `x - y <= c`: nothing if it has no term, a range for one term
  (`m*t <= c'` gives `t <= c'/m` rounded down for `m > 0`, `t >= c'/m`
  rounded up for `m < 0`), a relation or a sum for two, and nothing for
  more. When `y` is a quotient `F / m`, it gives `m*x - F <= m*c` (because
  `x - c <= F / m` rounded down means `m*(x - c) <= F`), and when `x` is
  one, `F - m*y <= m*c + m - 1`. Each is then the facts of that form, as
  above.
- **Using sums.** For a form `p*a + q*b + k` of two terms, the largest
  number `g` dividing `p` and `q` is taken out: a relation (for `p/g`,
  `q/g` being 1 and -1, directly or through one other term, as above) or a
  sum known directly for `(p/g)*a + (q/g)*b` bounds it above by `g*c + k`,
  and one for `(-p/g)*a + (-q/g)*b` bounds it below by `k - g*c`. These
  bounds narrow the range computed from the operands' ranges, before the
  operation is checked. A sum isn't chained through a relation: `x == a`
  and `a + b <= c` don't give `x + b <= c`.
- **Flow.** Sums are forgotten, shifted, joined and kept at a loop's head
  like relations, where what a point gives for a sum is the tightest of a
  sum it knows directly and, when it knows ranges for both terms, the
  largest value of `p*a + q*b` they allow. At a loop's head, no sum is made
  before the search (only relations are, between the variables the loop
  assigns). Reading a term doesn't narrow its range by its sums.

So both of these are proven:

```
fn add(a: u32, b: u32) -> ?u32 {
	if a > 4294967295 - b {                  // false: a + b <= MAX
		return none
	}
	return a + b
}

fn add_digit(v: u64, d: u64) -> ?u64 {
	if d > 9 {
		return none
	}
	if v > (18446744073709551615 - d) / 10 { // false: 10*v + d <= MAX
		return none
	}
	return v * 10 + d                        // v * 10 by ranges, + d by the sum
}
```

The second also works in two steps: `if v > MAX / 10` bounds `v * 10` by
ranges, and with `let t = v * 10`, `if t > MAX - d` gives `t + d <= MAX`.
Both guards must be about the same variables as the sum that's checked: a
guard on `a + c`, or on a copy of `a`, doesn't prove `a + b`.

`a / b` and `a % b` are proven when `b` can't be 0 (its range doesn't
contain 0, or 0 is a hole in it) and, for a signed type, when `a` can't be
the type's smallest value or `b` can't be -1 (again by its range or a
hole). `if a == MIN && b == -1 { return }` gives no fact after it, since
`&&` being false says neither side is false; write the test so that one
operand's fact holds where the division is:

```
if b == 0 {
	return none
}
if b == -1 {
	if a == MIN {                        // MIN: the type's smallest value
		return none
	}
	return -a                            // a > MIN: proven
}
return a / b                             // b != 0 and b != -1: proven
```

`a[i]` is proven when `i` can't be negative and either `i`'s range is below
the length's (for an array, its constant `N`), or a relation gives
`i - a.len <= -1`.

`a[i..j]` is proven when `i` can't be negative (or `j`, for `a[..j]`), and
`i <= j` and `j <= a.len` are each proven by the ranges (the largest value
of one is at most the smallest of the other) or by a relation (`i - j <= 0`).
A missing `i` is 0, and a missing `j` is `a.len`, so `a[i..]` needs
`i <= a.len`. There's no run-time check, and no `?` form yet:

```
fn search(xs: []i32, v: i32) -> bool {
	if xs.len == 0 {
		return false
	}
	let mid = xs.len / 2                     // mid <= xs.len - 1
	if xs[mid] < v {
		return search(xs[mid + 1..], v)      // proven: mid + 1 <= xs.len
	}
	return xs[mid] == v || search(xs[..mid], v)
}
```

Everything else gives no facts. In particular, facts cross function calls
only through [refinements](#refinements-in-types), array elements (and
fields under them) have no facts but their fields' refinements, a copy of
a struct keeps only its fields' refinements, and a loop's head knows only
facts of the kinds above that held before the loop (there's no counting:
the checker can't prove that a loop dividing by 10 runs at most 20
times).

#### Values of a type parameter

**Status:** Implemented (M7a; the design is in
[generics.md](generics.md#facts-about-t-values))

A generic function's body is checked once, for every type its type
parameters can be. A local whose type is a type parameter `T` with a
numeric bound (`Integer`, `Unsigned` or `Signed`) is a term, like an
integer local. With other bounds (`Ordered`, `Eq`, `Copy`, or none), a `T`
value is not a term and has no facts.

A numeric bound admits integer types: all of them for `Integer`, the
unsigned ones for `Unsigned`, the signed ones for `Signed` (today `u8` to
`u64` and `usize`, `i8` to `i64` and `isize`). Two ranges come from them:

- **values**, the hull of their ranges: every value of `T` lies in it,
  whatever `T` is. `Integer`: the smallest `i64` to the largest `u64`;
  `Unsigned`: 0 to the largest `u64`; `Signed`: the `i64` range. It is
  `T`'s range wherever the rules above use a type's range: for a term with
  no known range, the result of `+%` or `+|`, a dropped range end, and so
  on.
- **fits**, the intersection of their ranges: the values every `T` holds.
  `Integer`: `0..=127`; `Unsigned`: `0..=255`; `Signed`: `-128..=127`.

Where a value must fit in `T`:

| Operation | Proven when |
| --- | --- |
| A literal or a constant converted to `T` | It's in fits: `100` for any numeric bound, `200` with `Unsigned`, `-1` with `Signed` |
| `a + b`, `a - b` of type `T`, and `T(x)` | Each end of the value's range fits on its own. The upper end fits when it's in fits, or when the value is at most a value of type `T`: for `a + b`, `b <= 0` or `a <= 0` (by their ranges); for `a - b`, `b >= 0`; or, for a term plus a constant, a relation (directly or through one other term) `value - t <= 0` with a local `t` of type `T`. The lower end likewise: it's in fits, or `a + b` with `b >= 0` or `a >= 0`, `a - b` with `b <= 0`, or a relation `t - value <= 0` |
| `a * b` of type `T` | The result's range is in fits |
| `a / b`, `a % b`, when `T` may be signed (`Integer`, `Signed`) | `b` can't be 0, and `a` is above -128 by its range (so it's no signed type's smallest value) or `b` can't be -1 |
| `-a` | `T: Signed`, and `a` is above -128 by its range |
| `a << n`, `a >> n` | `n` is below 8, the narrowest width |

So after `if i < n` (both `T`), `i + 1` fits: the relation gives
`i + 1 <= n`, and `i + 1 >= i`. After `if b <= a` with `T: Unsigned`,
`a - b` fits: the relation gives at least 0, and `b >= 0` gives at most `a`.
A conversion out of `T` is checked against `x`'s range like any other:
`u64(x)` of an `Unsigned` is always proven, `u8(x)` needs `x <= 255`. A
failed proof shows the whole values range as "any `T`".

A **value parameter** (`N` in `[N: usize]`, M7b) is a term like an
integer `let`: a local of its type, with that type's range, which the body
never assigns (each instance assigns it its value first). An array of type
`[N]T` has the length `N`: `a.len`, `for x in a` and `a[i..j]` use that
term, so after `if i < N` (or in `for i in 0..N`), `a[i]` is proven, once,
for every `N`. A relation through the term works as for any other:
`if self.count >= N { return }` makes `self.items[self.count]` proven.

#### Facts through loops

At the head of a loop, the facts before it, `E`, still hold about everything
the loop doesn't assign. The variables it assigns (`A`: every variable
assigned anywhere in the body, including in nested loops; for `a[i] = v` and
`p.x = v`, `a` and `p`; a variable passed with `&`, and the receiver of every
method call, since the method may take `inout self`; but not an `inout`
slice, of which only the elements change, nor another view that isn't
assigned whole, `xs = ...`, since `&` and a method's receiver only reach its
elements) can change on each iteration, so
for them the head
keeps only facts that every iteration keeps. Those are found by checking the
body from a few candidate heads, in a fixed order, and taking the first that
**holds**: each of its facts about `A` holds again at every **back-edge** (a
`continue`, and the end of the body when it can be reached). At a back-edge,
a range end holds if the back-edge's range for the term (or its type's range,
if none is known) is within it, and a relation `a - b <= c` holds if the
back-edge gives `a - b <= c'` with `c' <= c` (directly or through one other
term, or from both ranges as above, where a term with no known range has its
type's), and a hole at `k` holds if the back-edge's range doesn't
contain `k` or has a hole there. A back-edge that can't be reached holds
everything.

Before the search, `E` gets relations between the variables of `A`, so
that the head can keep how they move together:

- for each two integer locals `v` and `w` in `A`, `v - w <= c` with the
  tightest `c` that `E` gives (as above);
- in a `for` loop, whose index `i` counts from a start `s`, for each integer
  local `v` in `A`, `v - i <= c` with the tightest of `v.hi - s.lo` (when
  `E` knows `v`'s range) and what `E` gives for `v - s` (when `s` is a term
  plus a constant). The index belongs to `A`, and at each back-edge it
  first goes on to the next value (as `i = i + 1` would), so `n - i <= 0`
  holds there when `n` grew by at most 1. In the body, `i`'s range is that
  of the `for` rule, and its head facts are only these relations.

So with `var n = 0` before `for x in xs`, a body that only adds 1 to `n`
(on some paths) keeps `n <= i` at the head: reading `n` then gives a range
below `xs.len`'s largest value, so `n + 1` is proven, and after the loop
`n <= xs.len`. The same holds for `n` and `i` in a `while` loop where both
start at 0. Two copies of one value (`var i = pos`, `var start = pos`)
start out related through `pos`, and keep `start <= i` while `start` only
catches up with `i`.

Two ways to weaken facts, each fact about `A` on its own (the two ends of a
range are separate facts):

- **drop** for some back-edges: forget each fact that doesn't hold at one of
  them (a range end goes to its type's limit);
- **cover** some back-edges: widen each range just enough to include the
  back-edges' ranges (a term with no range has its type's), and raise each
  relation's `c` to the largest the back-edges give. A hole can't be
  widened: it's forgotten as when dropping.

Either way, a relation no tighter than what the types of its terms give
(`c` at least `a`'s type's largest value minus `b`'s type's smallest) is no
fact, as a range as wide as its type is none. A sum is weakened like a
relation, with what a back-edge gives for it (a term with no known range
having its type's), and is no fact when its types give as much.

The **thresholds** of a term of `A` are the constants it's compared with in
the body: each comparison (`<`, `<=`, `>`, `>=`, `==`, `!=`) between the
term plus a constant `d` and a side whose range is a single value `k`, met
anywhere in a check of the body (nested loops included), gives the
threshold `k - d`.

The candidates, in order:

1. `E` itself.
2. `C`: `E` covering the back-edges of the check from `E`.
3. `W`: `C` dropping for the back-edges of the check from `C`. If `W` doesn't
   hold, the head is `E` with every fact about `A` forgotten, and the search
   ends.
4. `T`: `N` (below) with range ends moved in to thresholds, from those of
   the check from `W`: for each term of `A` with thresholds, the largest
   threshold at least `E`'s upper end (its type's limit if `E` has no
   range) becomes the upper end if it's below `N`'s, and the smallest
   threshold at most `E`'s lower end becomes the lower end if it's above
   `N`'s. `T` is only checked if that changes something, and is the head if
   it holds.
5. `N`: `E` covering the back-edges of the check from `W`. If `N` doesn't
   hold, the head is `W`.

So the body is checked at most six times, and only the check from the
chosen head counts: errors found from other candidates are not reported.
Step 1 keeps what the loop doesn't change, step 2 one round of change (a
variable set to a bounded value on some path), step 3 the bounds that only
move one way (`i` counting down from `buf.len` keeps `i <= buf.len`), step
4 the bounds a guard keeps for a variable that moves both ways (a stack
pointer that only grows under `if sp < DEPTH` and shrinks elsewhere keeps
`sp <= DEPTH`), and step 5 bounds that come from the loop's own tests (a
`while i > 1` that counts down leaves `i >= 1` at the head).

A nested loop is checked that often for each check of the loop around it,
so the search is limited by the loop's **height**: a loop with no loop in
its body has height 1, and any other loop one more than the highest loop in
its body (at any depth: in branches, arms, `catch` and `defer` blocks). A
loop higher than 4 doesn't search: its head is `E` with every fact about `A`
forgotten, and its body is checked once. The loops nested in it still
search if they are low enough. The height depends only on the program text,
so this limit never makes acceptance depend on time, and a chain of nested
loops of any depth costs at most what four nested searches cost.

```
var i = buf.len                  // E: i == 21
var v = n
loop {
	buf[i - 1] = digit(v)        // needs 1 <= i <= 21 at the head
	v = v / 10
	if v == 0 {
		break
	}
	if i <= 2 {
		break
	}
	i = i - 1                    // back-edge: 2 <= i <= 20
}
```

Here `E` (`i` is 21) and `C` (20 to 21) don't hold. `W` (`i <= 21`) does,
though `buf[i - 1]` can't be proven from it, and `N` (2 to 21, covering the
back-edge's 2 to 20) holds too: it's the head, and proves `buf[i - 1]`. After
the loop, both `break`s know `i >= 2`.

Example, from the standard library's `os.write_all`:

```
let n = syscall(SYS_WRITE, fd, p, left)  // n: isize, any value
...
if n < 0 {
	return n                             // leaves: below, n >= 0
}
...
if usize(n) > left {                     // proven: 0 <= n
	break                                // leaves: below, usize(n) <= left
}
left = left - usize(n)                   // proven by that relation
```

### Refinements in types

**Status:** Decided; implemented (2026-10-06, `src/sema/refine.rs`)

Facts cross function boundaries through **lightweight refinements** attached
to types. The caller must prove the refinement, and the callee assumes it:

```
fn byte_at(buf: []u8, i: usize where i < buf.len) -> u8 {
	return buf[i]                    // proven by the refinement
}

fn digit_value(c: u8 where c >= '0' && c <= '9') -> u8 where result <= 9 {
	return c - '0'                   // no underflow: proven
}
```

Rules:
- A refinement can only use the **same decidable fact language** as the
  checker: comparisons, `.len`, constants, and `&&`. There are no arbitrary
  function calls and no quantifiers. Anything the checker can prove at a call
  site, a refinement can express, and nothing more.
- Refinements can mention other parameters (`i < buf.len`) and, on the return
  type, `result`.
- A named refinement can be reused as a type:
  `type Digit = u8 where self <= 9`. A `Digit` value carries its proof with it,
  so storing it in a struct keeps the fact.
- Refinements cost nothing at run time. They exist only for the checker.

Not included: full `requires`/`ensures` contracts with arbitrary predicates.
A verification language is not "easy to read".

#### In the compiler today

Where a refinement can be written:

| Form | Example | Names in it |
| --- | --- | --- |
| A parameter's | `i: usize where i < buf.len` | the parameter and those before it |
| A result's | `-> usize where result <= buf.len` | `result` and every parameter |
| A value parameter's | `fn last[N: usize where N > 0]` | the function's value parameters |
| A struct field's | `head: usize where head < CAP` | the struct's fields, any of them |
| A named refinement | `type Digit = u8 where self <= 9` | `self` |

Each can also name constants (`CAP`, `pkg.MAX`) and the value parameters in
scope (`N` of `[N: usize]`, also a generic struct's). A parameter is named
by its value (an integer, or a `T` with a numeric bound), its `.len` (a
slice, a `str`, or an array, whose length is a number or a value
parameter), or an integer field (`p.x`, `p.a.b`, `self.count`). A name in
scope hides a constant of the same name; `result` names the result even
if a parameter has that name.

**The language.** A refinement is comparisons (`<`, `<=`, `>`, `>=`, `==`,
`!=`) joined with `&&`. Each side adds up integer constants (literals,
characters, constants) and the values above, with `+`, `-`, a unary `-`,
and `*` by a constant. With everything moved to one side, at most two
values may remain, so each comparison is a range, a relation, a sum or a
hole ([The fact language](#the-fact-language)). The arithmetic is exact,
over all integers: `i + 1 <= n` can't overflow. Anything else is an error
where the refinement is declared: a product of two values (`a * b < 100`),
a call, an element (`xs[0]`), three values (`a + b < c`), or a parameter
declared later. A comparison of constants only is checked there (false is
an error).

**Proving.** Where a refinement must hold (below), each value it names is
mapped to what the checker knows there: an argument that's a form (a term
plus a constant, or two terms, like `9 - d`) is its terms, and any other
value is known by its range (and, for a call's value, by what its result
refinement says, below). Then `x <= y` holds when the largest value of
`x - y` the checker knows is at most 0, the others likewise (`x < y` is
`x - y <= -1`, `==` is both ways). That largest value is, for the terms
left after merging: with two terms, the tighter of their ranges and a
relation or a sum about them (directly, or a relation through one other
term); otherwise their ranges, each read narrowed by its relations as
when a term is read. `x != y` holds when `x - y` can't be 0 by its range,
or when it's one term (times 1 or -1) plus a constant and that term has a
hole there or a range without it.

**Assuming.** Where a refinement is known, each comparison gives the facts
an `if` on it would give when true: a range, a relation or a sum, and for
`!=`, a hole (or a range end moved past the value). A value that isn't a
form is replaced by the end of its range that keeps the comparison true.

**Calls.**
- At a call, each parameter's refinement (but a `set` parameter's) must
  hold for the arguments, as they are before the call: an error at the
  argument otherwise. So must the value parameters' refinements, for the
  generic arguments: a number, or the caller's own value parameter, which
  its own refinement may bound.
- After the call, the result's refinement says what the value is: a range,
  and when `result` is in it once with the coefficient 1 or -1, a bound
  relative to the arguments' terms. So `let n = try f.read(&buf)` with
  `buf: [4096]u8` gives `n <= 4096`, and with a slice local `buf`,
  `n <= buf.len`. An argument passed `inout` or `set` is read after the
  call (its new value); an argument that isn't a term is known by its
  range only.
- For a `?T` result (`-> ?usize where result < CAP`), the refinement is
  about the value in it, when there is one. `if let`, `let ... else`,
  `??` (the range of either side), `try`, and `catch` (when the block
  leaves; with a fallback value, the range of either) keep it. A `match`
  on it doesn't.

**Bodies.**
- The parameters' refinements are facts when the body starts (except a
  `set` parameter's), and each `return` must meet the result's. `return
  none` meets any result refinement of a `?T`.
- A parameter the body can assign (`inout`, `sink` or `set`, but not a
  slice) keeps its refinement: every value assigned to it must meet it.
  Its refinement can't name another parameter the body can assign, nor its
  own fields, and no refinement can name a `set` parameter but its own. A
  result's refinement can't name a `sink` parameter (the caller doesn't
  have its value after the call).
- A `let` or `var` declared with a named refinement (`var d: Digit`) keeps
  it: every value assigned to it must meet it, and it's a fact after each.
  `Digit(x)` converts to a named refinement, proven like `u8(x)` and then
  the refinement.

**Places passed `&`.** A place with a refinement (such a variable or
parameter, or a field some refinement of its struct names) passed `inout`
or `set` may come back changed: after the call, the parameter's refinement
(if it has one) is assumed for the place, and the place's own refinement
must follow from it. Otherwise it's an error at the argument.

**Struct fields.** Every value of a struct keeps its fields' refinements,
so a struct's refinements are a first form of invariant
([memory.md](memory.md#struct-invariants)):
- They're proven at each literal, with the values given; at each
  assignment to a field (`p.f = v`, `p.f += 1`, `ps[i].f = v`), for every
  refinement that names the field, with the new value and the other
  fields' current values (terms for a place made of fields only, their
  types' ranges otherwise); and for a field passed `&`, as above. A copy of
  a struct needs nothing: its value already keeps them.
- They're facts about the fields of a struct place made of fields only (a
  local, a parameter, `p.inner`) wherever one of its fields is read, and
  when it's passed to a call. A field read from another value (an element,
  a call's result) is bounded by its own refinement, the other fields
  known by their types' ranges.
- A refined field is an integer. A refinement that relates two fields
  (`start <= end`) is checked when either is assigned, so a struct whose
  fields move together is changed in an order that keeps it at each step.

**Named refinements.** `type Digit = u8 where self <= 9` refines an integer
type. `Digit` is `u8` with the refinement: it's the whole type of a
parameter, a result, a struct field, or a `let` or `var`, and where it is,
its refinement applies as written there. Anywhere else (an array's
elements, `?Digit`, a type argument, a payload field, a constant's type)
it's an error for now: it would lose its refinement. A `type` declaration
without `where` is an error too (distinct types are still
[Proposed](types.md#distinct-types)).

**Generic code.** A value parameter is a term, and a `T` with a numeric
bound is one too ([Values of a type parameter](#values-of-a-type-parameter)),
so `fn take[N: usize](xs: [N]u8, n: usize where n <= N)` proves `xs[i]`
for `i < n`, once for every `N`, and `fn gap[T: Unsigned](lo: T, hi: T
where lo <= hi)` proves `hi - lo`. A refinement's constants needn't fit in
the bound's intersection: the comparison is exact. A trait's and an
impl's methods, and functions with `comptime` parameters or a pack, can't
have refinements yet; neither can a struct's, an enum's or an impl's value
parameters.

**Compile-time code.** In code that only runs at compile time (a
constant's value), a refinement the checker doesn't prove at a call, a
struct literal or a `Digit(x)` is checked as it runs, like any other
obligation there ([Proof obligations](#proof-obligations)): one that fails
is an error at the argument or the expression, "`i` of `at` doesn't meet
its refinement `i < xs.len`".

**Cost.** None at run time: refinements are facts for the checker, and
they remove checks. In std, `File.read` and `File.read_full` return `n
where result <= buf.len`, `StackBuf` keeps `start <= end <= N`, `ArrayVec`
keeps `count <= N`, `slices.sort`'s helper takes `end where end <=
xs.len`, and `print`'s buffer keeps `len <= 256`; the checks they made
again are gone. Every program that prints is 64 bytes smaller at `-O2`,
`std_containers.lode` 807; hello world is still 577 bytes.

## Stack bounds

**Status:** Proposed. Reporting is implemented (below).

The compiler computes the worst-case stack usage of the call graph from each
entry point (`main`, thread entries, interrupt handlers).

- If the call graph has no recursion and no unknown indirect calls, the bound is
  exact, and it is reported in build output and embedded in the binary's
  metadata.
- A target profile can **require** a bound (the embedded profile does). An
  unbounded call graph is then a compile error that points at the recursion or
  indirect call.
- Otherwise, stacks get guard pages (or the target's equivalent), and overflow
  is a defined abort.

This matches what embedded developers already do by hand, and it follows from
LatticeFoundry's cost/resource lattice (bet B9).

**Implemented now:** `lode build --stack-usage` prints each function's frame
size and the worst-case depth from `main`, along the deepest call path. If
there is no bound, it names the cause: the recursive functions, or the
function making an indirect call or a runtime-sized allocation. The numbers
come from LatticeFoundry's frame layout, the same one the prologue uses. A
frame includes the return address. The library returns the same report from
`lode::build` (`Executable::stack`).

**Still proposed:** other entry points (thread entries, interrupt handlers),
the bound in the binary's metadata, and a profile that requires a bound.
Today there is only `main`, and Lode has no indirect calls or runtime-sized
allocations yet, so recursion is the only cause of a missing bound. Overflow
already hits a guard page: LatticeFoundry's stack probes are on.

## The trusted boundary

**Status:** Proposed

Kernels, allocators, drivers and FFI need operations that cannot be checked:
raw pointers, MMIO, reinterpreting memory, calling foreign code. These are only
allowed inside `unsafe`:

```
unsafe fn mmio_write(addr: usize, value: u32) {
	volatile_store(addr as *u32, value)
}
```

Rules:
- An `unsafe fn` can only be called from an `unsafe` block or another
  `unsafe fn`.
- An `unsafe` block is a promise by its author that the surrounding safe API
  upholds the guarantee. Doc comments on `unsafe fn` must state what the caller
  must ensure.
- Package metadata records whether a package contains `unsafe` code, and the
  tooling can list every `unsafe` site in the whole dependency tree. Auditing
  should be one command.

What's unsafe so far (implemented): calling `syscall` or an `unsafe fn`,
reading the raw pointer of a `str`, an array or a slice (`s.ptr`),
pointer arithmetic (`p + n`), and leaving an `@uninit` field out of a
struct literal.
Holding or comparing a pointer is safe; only using it isn't.

Leaving an `@uninit` field unwritten
([memory.md](memory.md#uninitialized-buffers)) promises this: **the
struct's package never reads an element of that field that wasn't
written since the value was made.** The compiler checks the rest:

- The field is private, so no other package reads it, and `==` doesn't
  apply to the struct, so no derived code reads it either.
- Copying the struct copies the unwritten elements without using them,
  which is defined (they're poison in LatticeFoundry, and storing poison
  is not undefined behavior).

So the promise covers every read of the field in its package's code, safe
code included: a method that reads `bytes[i]` must know `i` was written,
which is usually the range a pair of private fields keeps, as
`StackBuf`'s `start..end`. Breaking it reads poison: a branch on it is
undefined behavior, and output of it can leak old stack contents. The
`unsafe` block that makes the value is where an auditor starts, and the
struct's doc comment says what keeps the promise.

Low-level operations are **compiler intrinsics**, not asm in the standard
library:

| Intrinsic | Purpose |
| --- | --- |
| `syscall(nr, args...)` | Lowered per os/arch to the right trap instruction and calling convention. Implemented for Linux x86-64: up to 6 integer or pointer arguments (integers are sign- or zero-extended to 64 bits by their type), returns the raw kernel result as `isize` (`-errno` on failure) |
| `volatile_load`, `volatile_store` | MMIO |
| `fence(ordering)` and the atomics | Memory ordering |
| `context_switch` (name to be decided) | Save and restore register state, for kernels and green threads |
| `interrupt_entry` (attribute) | Handler prologue and epilogue for the target |

A project that reimplements an os/arch (see [backend.md](backend.md)) builds on
these intrinsics. Inline asm may still be needed for rare instructions. If we
add it, it is `unsafe` only and never used in the standard library. *(Open.)*
