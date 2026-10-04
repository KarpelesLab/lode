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
| Uninitialized read | Every variable is definitely assigned before use (flow analysis, as in Go and Rust). | |
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
| `let` / `var` / assignment | The value's range. A term plus a constant is related to the term (`let last = xs.len - 1` gives `last - xs.len <= -1`). A view of a whole `[N]T` array has length `N`, and a copy of a view has its length. Assigning forgets every fact involving the variable, and for a view, its length. |
| `if cond` | Inside the branch, the facts of `cond` being true; in `else`, of it being false |
| After an `if` | If one branch always leaves (`return`, `break`, `continue`), the other branch's facts. Otherwise, what both branches agree on: ranges widened to cover both, relations both know. |
| `a && b`, `a \|\| b` | `b` is checked knowing `a` is true (`&&`) or false (`\|\|`) |
| A comparison `x < y` (and `<=`, `>`, `>=`, `==`) | Each side narrows by the other's range; between two terms (plus constants), a relation: `i + 1 < xs.len` gives `i - xs.len <= -2`. `x != k` narrows only when `k` is at an end of `x`'s range. |
| `while cond` / `loop` | Before the loop, everything is forgotten about the variables the loop assigns. The body knows `cond` is true. After a `while` without `break`, `cond` is false. |
| `for i in a..b` | Everything about the variables the loop assigns is forgotten, as for `while`. In the body, `i` lies in `a.lo..=b.hi - 1`, and when `a` or `b` is a term (plus a constant) the body doesn't assign, `a <= i` and `i < b` as relations. So `for i in 0..xs.len` proves `xs[i]`. |
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
keep its fields' facts, and there's no induction beyond the loop
condition.

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
reading a `str`'s raw pointer (`s.ptr`), and pointer arithmetic (`p + n`).
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
