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
| Integer overflow | `+ - *` need a proof that the result fits. Otherwise use a wrapping, saturating or checked operator. | [types.md](types.md#arithmetic) |
| Division by zero | `/` and `%` need a proof that the divisor is non-zero (and for signed types, not `MIN / -1`). | [types.md](types.md#arithmetic) |
| Narrowing conversion | `u8(x)` needs a proof that `x` fits. Otherwise use `.wrap()`, `.saturate()` or `.try()`. | [types.md](types.md#conversions) |
| Float to int | Always defined: saturating, and NaN gives 0. No proof needed. | [types.md](types.md#floats) |
| Use after free, double free, dangling reference | Ruled out by the memory model. | [memory.md](memory.md) |
| Data race | Ruled out by exclusivity and `Send`-like rules. | [concurrency.md](concurrency.md) |
| Uninitialized read | Every variable is definitely assigned before use (flow analysis, as in Go and Rust). | [memory.md](memory.md#uninitialized-buffers) |
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
expression can be a term plus a constant: `i`, `i + 1`, `xs.len - 1`. There
are two kinds of fact:

- **Ranges:** a term lies in `lo..=hi`.
- **Relations:** for two terms, `a - b <= c`.

Both are decidable and cheap, and the rules for how they flow are fixed:

| Where | What the checker learns |
| --- | --- |
| A literal or constant | Its exact value |
| An expression | The range computed from its operands' ranges (e.g. `a + b` from both ranges) |
| `a.len` | For an array, its constant length. For a slice or `str`, a term, in `0..=` the largest `isize` |
| A struct literal | In `let p = Point{x: 1, y: v}` (or `p = ...`), the fields given as constants: here `p.x` is 1 |
| `p.x = v`, `p.a = q` | The value's range for the field assigned; everything else about it (or about the fields of a struct field) is forgotten. Assigning a whole struct forgets all its fields. |
| `let` / `var` / assignment | The value's range. A term plus a constant is related to the term (`let last = xs.len - 1` gives `last - xs.len <= -1`). A view of a whole `[N]T` array has length `N`, and a copy of a view has its length. Assigning forgets every fact involving the variable, and for a view, its length, except that assigning a variable itself plus a constant (`i = i - 1`, `i += 2`) shifts its relations by the constant (`i <= xs.len` becomes `i - xs.len <= -1`). |
| `if cond` | Inside the branch, the facts of `cond` being true; in `else`, of it being false |
| After an `if` | If one branch always leaves (`return`, `throw`, `break`, `continue`), the other branch's facts. Otherwise, what both branches agree on: ranges widened to cover both, relations both know. |
| `match`, `if let`, `let ... else` | Each arm starts with the facts from before. After, the arms that don't always leave are joined, as after an `if`. Payload values have no facts. A `match` on a call that throws is the same, with the arms `ok` and `err`. |
| A call `f(&x)`, `p.scale(2)` | A call changes only the places passed `inout` or `set` (with `&`, or as the receiver of a method that takes `inout self`): what was known about each (a variable, or a struct field and the fields in it) is forgotten. A slice's length doesn't change, and elements have no facts. A variable passed `set` is assigned, with nothing known ([memory.md](memory.md#parameter-conventions-in-the-compiler-today)). |
| `try f()`, `throw` | The error leaves the function, so it adds nothing to the facts after. After `try`, the facts are those after the call. `throw` always leaves, like `return`. |
| `f() catch e { ... }`, `f() catch v` | The block (or the value `v`) starts with the facts after the call. After, the block's facts are joined with the call's, as after an `if` without `else`; a block that always leaves adds nothing. A `break` or `continue` in it is a loop exit like any other. |
| `defer`, `errdefer` | The body is checked where it's written, knowing the facts there about the variables nothing after it in the block assigns. It can't assign variables declared outside it (or pass them `inout` or `set`), so running it changes no facts. |
| `a && b`, `a \|\| b` | `b` is checked knowing `a` is true (`&&`) or false (`\|\|`). After, what `b` may change is forgotten. |
| `a ?? b` | After, what holds whether `b` ran or not: the facts before `b` joined with those after it |
| A comparison `x < y` (and `<=`, `>`, `>=`, `==`) | Each side narrows by the other's range; between two terms (plus constants), a relation: `i + 1 < xs.len` gives `i - xs.len <= -2`. `x != k` narrows only when `k` is at an end of `x`'s range. |
| The head of a loop | The facts before the loop, with those about the variables the loop assigns kept as far as every iteration keeps them: see [Facts through loops](#facts-through-loops) |
| `while cond` | The body knows `cond` is true. After the loop, what the head and `cond` being false give, joined (as after an `if`) with the facts at each `break` |
| `loop` | After the loop, the facts at its `break`s, joined. Without a `break`, the code after it can't be reached. |
| `for i in a..b` | In the body, `i` lies in `a.lo..=b.hi - 1`, and when `a` or `b` is a term (plus a constant) the body doesn't assign, `a <= i` and `i < b` as relations. So `for i in 0..xs.len` proves `xs[i]`. After the loop, the head facts, joined with the facts at each `break`. |
| `for x in xs` | The same as `for` over `0..xs.len` with a hidden index, which proves the hidden `xs[index]` that gives `x` |
| `x - y` | A known relation bounds the result: `y <= x` proves it doesn't go below zero |

A relation can also come from two known relations through one other term:
`i < n` and `n == xs.len` (from `let n = xs.len`) give `i < xs.len`. Only
one step: longer chains are not followed, which keeps the check cheap and
easy to predict.

`a[i]` is proven when `i` can't be negative and either `i`'s range is below
the length's (for an array, its constant `N`), or a relation gives
`i - a.len <= -1`.

Everything else gives no facts. In particular, facts don't cross function
calls yet (that's what [refinements](#refinements-in-types) are for), array
elements (and fields under them) have no facts, a copy of a struct doesn't
keep its fields' facts, and a loop's head knows only facts of the kinds
above that held before the loop (there's no counting: the checker can't
prove that a loop dividing by 10 runs at most 20 times).

#### Facts through loops

At the head of a loop, the facts before it, `E`, still hold about everything
the loop doesn't assign. The variables it assigns (`A`: every variable
assigned anywhere in the body, including in nested loops; for `a[i] = v` and
`p.x = v`, `a` and `p`; a variable passed with `&`, and the receiver of every
method call, since the method may take `inout self`; but not an `inout`
slice, of which only the elements change) can change on each iteration, so
for them the head
keeps only facts that every iteration keeps. Those are found by checking the
body from a few candidate heads, in a fixed order, and taking the first that
**holds**: each of its facts about `A` holds again at every **back-edge** (a
`continue`, and the end of the body when it can be reached). At a back-edge,
a range end holds if the back-edge's range for the term (or its type's range,
if none is known) is within it, and a relation `a - b <= c` holds if the
back-edge gives `a - b <= c'` with `c' <= c` (directly or through one other
term, as above). A back-edge that can't be reached holds everything.

Two ways to weaken facts, each fact about `A` on its own (the two ends of a
range are separate facts):

- **drop** for some back-edges: forget each fact that doesn't hold at one of
  them (a range end goes to its type's limit);
- **cover** some back-edges: widen each range just enough to include the
  back-edges' ranges (a term with no range has its type's), and raise each
  relation's `c` to the largest the back-edges give (and forget it if one
  gives none).

The candidates, in order:

1. `E` itself.
2. `C`: `E` covering the back-edges of the check from `E`.
3. `W`: `C` dropping for the back-edges of the check from `C`. If `W` doesn't
   hold, the head is `E` with every fact about `A` forgotten, and the search
   ends.
4. `N`: `E` covering the back-edges of the check from `W`. If `N` doesn't
   hold, the head is `W`.

So the body is checked at most five times (a nested loop is checked that
often for each check of the loop around it), and only the check from the
chosen head counts: errors found from other candidates are not reported.
Step 1 keeps what the loop doesn't change, step 2 one round of change (a
variable set to a bounded value on some path), step 3 the bounds that only
move one way (`i` counting down from `buf.len` keeps `i <= buf.len`), and
step 4 bounds that come from the loop's own tests (a `while i > 1` that
counts down leaves `i >= 1` at the head).

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

**Status:** Decided (the syntax is still provisional)

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
reading the raw pointer of a `str`, an array or a slice (`s.ptr`), and
pointer arithmetic (`p + n`).
Holding or comparing a pointer is safe; only using it isn't.

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
