# Generics, traits and `comptime` (M7 proposal)

This is the design proposal for milestone M7 ([roadmap.md](roadmap.md)). It
builds on what's already written: [types.md](types.md#generics-and-traits)
(the `[T]` syntax, traits checked at the definition, static dispatch),
[comptime.md](comptime.md) (one compile-time mechanism, hermetic and
bounded), and the proof checker of [safety.md](safety.md). Each section lists
the options, the trade-offs and a recommendation. The decisions only the user
can make are collected at the end, in
[Questions for the user](#decisions).

M7 is implemented, in five steps: M7a, generic functions over the
built-in traits; M7b, generic structs and enums, value parameters and
generic methods; M7c, traits and `impl` blocks; M7d, compile-time
evaluation and target selection; M7e, format strings. What the compiler
does is in [M7a in the compiler](#m7a-in-the-compiler),
[M7b](#m7b-in-the-compiler), [M7c](#m7c-in-the-compiler),
[M7d](#m7d-in-the-compiler) and [M7e](#m7e-in-the-compiler). The rest is
**Proposed** unless a section says otherwise.

## Principles

**Status:** Decided; followed by the compiler for generic functions (M7a)

Five rules shape the whole proposal. They follow from decisions already made.

1. **A generic body is checked once, at its definition.** Types, names,
   parameter conventions, exclusivity and proof obligations are all checked
   against the bounds, not against each use. An instantiation can't fail to
   type-check. This is the point of difference with Zig and C++
   ([concept.md](concept.md#positioning)).
2. **The only errors at an instantiation are about the arguments**: a type
   argument that doesn't satisfy a bound, a value argument that doesn't meet
   its refinement, or a compile-time evaluation that fails (see
   [Proof obligations in compile-time code](#proof-obligations-in-compile-time-code)).
   Each is reported at the call site.
3. **No operator overloading, also not through traits.** An operator in
   generic code means what it means on the primitive types, or it isn't
   allowed ([types.md](types.md#operators)).
4. **Pay only for what you use.** An instantiation exists in the binary only
   if `main` reaches it, like functions today.
5. **The checker stays specified and decidable.** Generics add no solver and
   no search. Bounds are checked by lookup; facts about generic values use the
   existing fact language ([safety.md](safety.md#the-fact-language)).

## Generic functions

**Status:** Implemented (M7a; value parameters in M7b)

```
fn max[T: Ordered](sink a: T, sink b: T) -> T {
	if a.lt(b) {
		return b
	}
	return a
}

fn sum[T: Integer](xs: []T) -> T {
	var total: T = 0
	for x in xs {
		total = total +% x
	}
	return total
}

let m = max(3, x)            // T inferred: the type of x
let s = sum[u64](values)     // explicit
```

- Generic parameters come in brackets after the name: `[T]`, `[T: Ordered]`,
  `[T: Ordered + Copy, U]`. A bound is a trait, or several joined with `+`.
- A generic parameter can also be a **value** of an integer type or `bool`:
  `[N: usize]`. It's known at compile time. See
  [Value parameters](#value-parameters).
- Bounds stay in the brackets. `where` is not used for bounds: it's taken by
  [refinements](safety.md#refinements-in-types), which are facts about
  values. A long parameter list wraps like any other list.

### Type arguments at the call site

**Options:**

1. **Always explicit** (`max[u32](a, b)`). Simple, but noisy for the common
   case.
2. **Inferred from the arguments only.** Predictable, but `parse[u32](s)` and
   `let x: u8 = max(1, 2)` need explicit arguments.
3. **Inferred from the arguments, then from the expected type.** One pass
   over the parameters in order, then the context's type for what's left.
   No backtracking, no inference across statements.
4. **Full bidirectional inference** (Rust, Swift). Fewer annotations, but
   errors are harder to explain and compile time is harder to predict.

**Decided: 3** (implemented in M7a). It covers the common cases and stays
easy to explain: "a type argument comes from the first argument that fixes it, or
from the type expected for the result". An untyped literal doesn't fix a type
argument, as with `let b = 300` today: `max(3, 4)` alone is an error that
asks for a type, and `let m: u8 = max(3, 4)` works. Explicit arguments are
always allowed, and must be complete (all or none).

### `[T]` and indexing

`[` after an expression is either an index or a list of generic arguments.
Declarations are never ambiguous (`fn max[T]`, `struct List[T]`), and neither
are types (`List[u32]` in a type position).

**Options:**

1. **Decide in the checker** (Go). The parser builds one node for
   `expr[args]`, and the checker looks at what `expr` names: a generic
   function or type means generic arguments; a value means an index.
2. **A different bracket for generics in expressions** (Rust's `::<>`,
   `max.[u32]`). Unambiguous for the parser, but a second spelling of the
   same thing.
3. **No explicit arguments in expressions**, only inference or a typed
   `let`. Too limiting: `List[u32].new()` has nothing to infer from.

**Decided: 1** (implemented in M7a). The parser gains one rule: inside
`[...]` after an expression, each comma-separated item is parsed as a type
when it starts with a token that only a type can start with (`?`, `??`,
`*`), or when it starts with `[` and parses as a slice or array type
(`[]u8`, `[4]u8`) followed by `,` or `]`; otherwise as an expression, which
the checker reinterprets as a type name (`u32`, `geo.Point`) when the base
names a generic function. One expression in brackets is an index node;
anything else is a type-arguments node. `a[i, j]` on an array stays an
error, in the checker. The formatter's rule "no space before an index's
`[`" already gives `max[u32](a, b)` and `fn max[T: Ordered]`.

### Value parameters

**Status:** Implemented (M7b), without refinements, which don't exist yet

```
struct StackBuf[N: usize] {
	bytes: [N]u8
	len: usize where len <= N
}

fn first_n[N: usize](xs: []u8) -> ?[N]u8 { ... }
```

- A value parameter is a term in the fact language, like a `let` of its type
  ([safety.md](safety.md#the-fact-language)). Its range is its type's, and a
  refinement narrows it: `[N: usize where N > 0]`.
- `[N]T` with a value parameter `N` has length `N`, so `for i in 0..a.len`
  proves `a[i]` once, for every `N`.
- At an instantiation, the argument must be known at compile time, and its
  refinement is checked there.

This replaces Zig's "`comptime` parameter checked at each use" for the cases
where a type depends on a number. It keeps rule 1: the body is checked once
with `N` unknown.

## Generic types

**Status:** Implemented (M7b); `Box` waits for the allocator

```
struct Pair[A, B] {
	first: A
	second: B
}

enum Tree[T] {
	leaf(value: T)
	node(left: Box[Tree[T]], right: Box[Tree[T]])
}

let p = Pair{first: b, second: true}      // b: u8, so Pair[u8, bool]
let q = Pair[u8, u16]{first: 1, second: 2}
```

- Structs and enums take generic parameters, with bounds, like functions.
  `Pair[u8, bool]` and `Pair[u8, u16]` are different types.
- A literal infers the arguments from its fields when it can, with the same
  rule as calls.
- A generic type can't contain itself by value (as today); through `Box`
  it can, once `Box` exists ([memory.md](memory.md#owning-pointers-are-values)).

### `?T` stays built in

**Status:** Decided; followed in M7b

`?T` is already an enum `none | some(value: T)` in the compiler. **Options:**
keep it built in, or define it in the standard library as `Option[T]` with
`?T` as sugar.

**Recommendation: keep it built in.** It has syntax that a library type
can't have (`??`, `if let`, `let ... else`, `none` from context, the
implicit `T` to `?T`) and a layout rule (niches). Making it a library type
gains nothing a user can see. The same goes for a call's result,
`throws(E) -> T`. User code writes its own generic enums freely; there is no
`Option` in the standard library, so there is one way to write an optional.

### Views as type arguments

**Status:** Implemented (M7a, M7b)

A type argument can't be a view (`str`, `[]T`, later `dyn Trait`). Views are
never stored in fields ([memory.md](memory.md#views)), and a generic type
can put `T` in a field, so allowing `Pair[str, u8]` would need a check per
instantiation (breaking rule 1) or a second kind of type parameter. Generic
functions over views take the view in the signature instead:
`fn find[T: Eq](xs: []T, v: T) -> ?usize`. A view parameter kind
(`[T: view]`) can be added later if real code needs it.

## Generic methods

**Status:** Implemented (M7b)

```
fn Pair[A, B].swap(self) -> Pair[B, A] {
	return Pair{first: self.second, second: self.first}
}

fn StackBuf[N].push(inout self, b: u8) throws(Full) { ... }

fn List[T].map[U](self, f: fn(T) -> U) -> List[U] { ... }

fn List[T: Ordered].sort(inout self) { ... }   // only when T: Ordered
```

- `fn Pair[A, B].swap` declares the type's parameters for this method (as
  Go's `func (p Pair[A, B])`). The names can differ from the struct's; the
  bounds the struct declares are implied and aren't repeated.
- A method can add bounds to the type's parameters: `List[T: Ordered].sort`
  exists only for lists whose element type is `Ordered`. Calling it on a
  `List[Point]` without `impl Ordered for Point` is an error at the call
  that names the missing bound.
- A method can have parameters of its own: `.map[U]`.
- Methods are still declared in the type's package only
  ([types.md](types.md#methods)).

## Traits

**Status:** Implemented (M7c), without `uses`; `Ordered` stays built into
the compiler ([M7c in the compiler](#m7c-in-the-compiler))

```
trait Ordered: Eq {
	fn cmp(self, other: Self) -> Ordering

	fn lt(self, other: Self) -> bool {      // default method
		return self.cmp(other) == .less
	}
}

trait Encoding {
	type Rune: Copy + Eq
	const MAX_LEN: usize

	fn decode(bytes: []u8) -> ?(Rune, usize)
	fn encode(r: Rune, set out: [MAX_LEN]u8) -> usize
	fn validate(bytes: []u8) -> bool
}
```

- A trait lists **required methods** (with `self`, `inout self` or
  `sink self`), **associated functions** (no `self`, called `E.decode(b)` on
  the type), **associated types** (`type Rune`, used as `E.Rune`) and
  **associated constants** (`const MAX_LEN: usize`, used as `E.MAX_LEN`).
  Associated constants settle the "max rune length per encoding" question in
  [strings.md](strings.md#types).
- `Self` is the implementing type.
- `trait Ordered: Eq` makes `Eq` a **supertrait**: every `Ordered` type is
  `Eq`, and a bound `T: Ordered` gives `==` too.
- A **default method** has a body, checked once in the trait against the
  trait's own declarations. An implementation may replace it.
- Signatures are complete: conventions, `throws(E)` and `uses` are part of a
  trait method, and an implementation must match them, except that it may
  throw nothing where the trait throws, and may use fewer contexts
  ([Contexts and errors](#contexts-and-errors)).

### Implementations

**Status:** Decided (question 1); implemented (M7c)

**Options:**

1. **Explicit `impl` blocks** holding the trait's methods (Rust):

   ```
   impl Ordered for Point {
   	fn cmp(self, other: Point) -> Ordering { ... }
   }
   ```

2. **A conformance line plus ordinary methods**:

   ```
   impl Ordered for Point
   fn Point.cmp(self, other: Point) -> Ordering { ... }
   ```

   Every method keeps the greppable `fn Point.cmp` form, and there's one way
   to declare a method. But an `impl` in the trait's package (allowed, see
   [Coherence](#coherence)) can't declare `fn Point.cmp` there, so that case
   still needs a block, and two traits with a method of the same name can't
   both be implemented.
3. **Implicit satisfaction** (Go): a type that has the methods implements
   the trait. Easy to read, but conformance can be accidental, errors are
   worse ("does not implement" far from the cause), and associated types
   have nowhere to be declared.

**Recommendation: 1.** It's the form types.md already shows, it covers
both packages an impl may live in with one syntax, it groups associated
types and constants with the methods, and a missing or wrong method is
reported on the `impl` line. `impl Ordered for Point` is the greppable
anchor. A method in an impl is called like any method, `p.cmp(q)`. A type's
method names are one namespace: an impl can't bring a method whose name the
type already has (as a field, a variant, a method, or a method of another
impl). The rare clash is resolved by calling through the trait:
`Ordered.cmp(p, q)`. As implemented, the clash isn't an error at the
`impl`: `p.cmp(q)` finds the type's own method first, and is an error
when two impls give the method, which then needs `Ordered.cmp(p, q)`
([M7c in the compiler](#m7c-in-the-compiler)).

Generic and conditional implementations:

```
impl[A: Eq, B: Eq] Eq for Pair[A, B]          // derived, see below
impl[T: Ordered] Ordered for List[T] { ... }
```

### Coherence

**Status:** Recommended (question 5); implemented (M7c)

**Options:** (1) Rust's orphan rule: an impl lives in the trait's package or
the type's package, and there's at most one impl of a trait for a type in a
program. (2) Only the type's package (Go-like, simplest). (3) Anywhere,
picked by import (Scala implicits): flexible and confusing.

**Recommendation: 1, without blanket impls.** The trait's package needs
impls for types it doesn't own (a serialization package implementing its
trait for `std` types), and the type's package needs impls for traits it
doesn't own (`Format` for a user type). Additionally:

- An impl's type is a named type (`Point`, `Pair[A, B]`, `u32`), never a
  bare parameter (`impl[T: Ordered] Format for T` is not allowed). This
  makes overlap trivial to check: at most one impl per trait and type name,
  found by a table lookup. There is no specialization.
- The primitive types belong to the standard library for this rule, so
  `std` can implement its traits for `u32`.

Blanket impls can be added later, with an overlap rule, if real code needs
them.

## Built-in traits

**Status:** Proposed; `Eq`, `Ordered`, `Copy`, `Integer`, `Unsigned` and
`Signed` implemented (M7a, built into the compiler), `impl Ordered`
for structs and enums (M7c), and `Format`, declared in Lode in `std/io`
(M7e)

Some traits are known to the compiler. They are declared in the standard
library (`std/core`, name Open) so they have documentation and a place in
the package graph, but some of their impls come from the compiler. The
compiler still knows the six of M7a by name, and `Ordering` is a built-in
enum: `std/core` and an implicit import of it would be needed to declare
them in Lode, and nothing needs that yet.

| Trait | Meaning | Who implements it |
| --- | --- | --- |
| `Eq` | `==` and `!=` are defined | Derived by the compiler only (below) |
| `Ordered: Eq` | A total order, `cmp` and the defaults `lt`, `le`, `gt`, `ge`, `min`, `max` | Built in for integers and `bool`; user types write an impl |
| `Integer: Ordered + Copy` | The integer operators | Sealed: only the integer primitives |
| `Unsigned`, `Signed` | `Integer` and the sign | Sealed |
| `Copy` | A value can be copied implicitly | Automatic, see below |
| `Format` | Writable by `print("{}")` ([Format strings](#format-strings)) | `std/io` implements it for integers, `bool`, `str`; user types write an impl |
| `Send`, `Sync` | May cross / be shared across threads ([concurrency.md](concurrency.md#data-race-freedom)) | Automatic; opt-out and `unsafe impl`. Deferred to the concurrency milestone. |

A **sealed** trait can't be implemented outside the standard library.

### Operators in generic code

No operator is overloaded (rule 3). So in a generic body:

- `==` and `!=` need `T: Eq`, and they are the compiler's derived equality
  of the concrete type. Users can't implement `Eq` with code: a type is `Eq`
  when its parts are, which is what `==` already does today
  ([types.md](types.md#operators)). For generic types the compiler derives
  `impl[A: Eq, B: Eq] Eq for Pair[A, B]`.
- `<`, `<=`, `>`, `>=`, arithmetic, bitwise and shifts need a **sealed**
  numeric bound (`Integer`, `Unsigned`, `Signed`; float traits later). They
  mean exactly what they mean on the primitive, so the body reads the same
  whatever `T` is.
- `T: Ordered` gives **methods**, not operators: `a.lt(b)`, `a.cmp(b)`. If
  `<` worked on `T: Ordered`, a `Point` with a hand-written `cmp` would have
  a user-defined `<`: operator overloading through a side door.

The cost: generic sorting code reads `xs[j].lt(xs[i])` rather than
`xs[j] < xs[i]`. We accept it, as types.md accepts `a.add(b)` for big
integers.

**Floats** are not `Ordered` (types.md) and, by the same reasoning, not
`Eq`: `==` on floats is IEEE (`NaN != NaN`), not an equivalence. A struct
with a float field therefore gets no derived `==` (it compares fields, or
uses `total_cmp`). Floats aren't in the compiler yet; this only fixes the
rule ahead of time.

### `Copy` and moves in generic code

**Status:** Decided (question 2); implemented (M7a)

memory.md says small plain types are copied implicitly and types that own
resources move. In generic code, `T` may be either. **Options:**

1. **`T` is move-only unless bounded `T: Copy`.** Using a read-only `T`
   parameter as a value to keep (returning it, storing it, `let b = a`
   while `a` is used later) needs `T: Copy`, or the parameter must be
   `sink`. Every type today is `Copy`, so existing code is unaffected.
2. **`T` is `Copy` unless it says otherwise** (`[T: move]`, like Rust's
   `?Sized`). Shorter for the common case, but containers and most std
   generics will opt out, and forgetting to makes a generic unusable with
   owning types, found only when someone tries.

**Recommendation: 1.** It's the honest default under value semantics, and
it costs little: `max` takes `sink a: T, sink b: T` (callers don't mark
`sink`, so `max(a, b)` reads the same), and returns one while the other is
destroyed, which is exactly right for owning values. Reading a `T` in place
(passing `xs[i]` to a default parameter, calling a method on it) never needs
`Copy`. `Copy` is automatic: a struct, enum or array is `Copy` when its
parts are and it has no `deinit`.

## Dispatch

**Status:** Proposed; monomorphization implemented (M7a)

### Static by default: monomorphization

Each instantiation that `main` reaches becomes its own function, with the
type arguments substituted and trait calls resolved to the impl's method.
This is decided in types.md and fits "pay only for what you use": `max[u8]`
and `max[u32]` are two small functions, and an instantiation nothing calls
isn't emitted.

In the compiler, the checker produces one typed tree per generic function,
with type parameters in it. A pass between checking and lowering
(`src/mono.rs`, which replaced `src/reach.rs`) walks the call graph from
`main` and produces concrete functions by substitution. `src/lower.rs`
sees only concrete types.

Linker symbols include the arguments: `std/math.max[u32]`.

### Sharing code between instantiations

types.md allows an optimization profile to share code on small targets.
**Options**, in order of cost:

1. **Identical code folding** in LatticeFoundry: instantiations that compile
   to the same machine code (`max[u32]` and `max[i32]` often do not, but
   `len[u8]` and `len[i8]` do) become one. No language change.
2. **Witness tables** (Swift): one body takes a hidden table with `T`'s size,
   alignment and trait methods. Saves the most space, costs a call per trait
   method, and needs the same tables as `dyn`.

**Recommendation:** monomorphization only in M7. Ask LatticeFoundry for 1
when code size on small targets is measured to need it. Do 2 after `dyn`
exists, as a profile option that must not change behavior.

### `dyn Trait`

Dynamic dispatch is explicit (types.md). A sketch, so M7's traits don't
rule it out:

- `dyn Writer` is a **view**: a pointer to a value plus a pointer to the
  impl's table of methods. Like `[]T`, it can be a parameter, a local or a
  return value, never a field ([memory.md](memory.md#views)). An owned one
  is `Box[dyn Writer]`, once the allocator context exists.
- A trait can be used as `dyn` only if its methods take `self` (in any
  convention but `sink`, which would move an unsized value), have no generic
  parameters of their own, and don't use `Self` in arguments or results.
  The compiler says which method breaks it.
- [Stack bounds](safety.md#stack-bounds) survive: the program is linked
  whole, so the set of impls of the trait is known, and a call through `dyn`
  costs the worst of them.

**Recommendation: not in M7.** Nothing M7's std needs uses it (I/O traits,
`Format` and `select` are all static), and it brings a value layout and a
coercion rule of its own. It's a good candidate for right after M7.

## Checking generic bodies

**Status:** Implemented (M7a), without refinements, which don't exist yet

### Against the bounds

In a generic body, a value of type `T` can only be used in ways every type
satisfying `T`'s bounds supports:

- calling methods and associated functions of the bounds' traits (and their
  supertraits);
- the operators the bounds give ([Operators in generic code](#operators-in-generic-code));
- passing it on to another generic whose bounds `T`'s bounds imply;
- moving it, and copying it only with `T: Copy`.

Anything else is an error in the generic function, never at an
instantiation.

### Facts about `T` values

The proof checker must prove each obligation once, for every possible `T`.
For bounds without numeric meaning (`Ordered`, `Format`), a `T` value is not
a term: it has no facts, and nothing needs any. For the sealed numeric
bounds:

- A `T` term's **range** starts as the hull of the ranges of every type the
  bound admits (for `Unsigned`: `0..=` the largest `u128`; for `Integer`:
  the smallest `i128` to the largest `u128`). Every value of every
  instantiation is inside it, so facts learned from it are true for all.
- An obligation "the result fits in `T`" (`a + b`, `a - b`, `T(x)`) is
  proven when the result's range is within the **intersection** of those
  ranges (`0..=127` for `Integer` over the 8-bit and wider types), or when
  a **relation** places it between two `T` terms: after `if i < n`, `i + 1`
  is at most `n`, which is a `T`, so it fits. `x - y` after `y <= x` is
  proven as today.
- A literal converts to `T` only if it fits in the intersection: `0`, `1`
  and `100` are fine for `T: Integer`, `200` needs `T: Unsigned`, and `-1`
  needs `T: Signed`.
- Relations between terms are unchanged, so `for i in 0..xs.len` still
  proves `xs[i]` for `xs: []T`.

This needs no new kind of fact, only two ranges per bound and one rule for
"fits in `T`". Generic integer code that can't be proven uses `+%`, `+|` or
`checked_add` as usual. Whether `u1`..`u7` count as `Integer` (they would
shrink the intersection to `0..=0`) is settled with the arbitrary widths of
[types.md](types.md#integers).

Value parameters (`[N: usize]`) are ordinary terms, as above.

The rule as implemented, with the types the compiler has today (up to 64
bits), is in [safety.md](safety.md#values-of-a-type-parameter).

### Refinements on generic code

Refinements work unchanged on value parameters and on `T` terms with a
numeric bound: `fn take[N: usize](xs: []u8, n: usize where n <= N)`. Their
constants must fit in the bound's intersection, like literals. A refinement
can't mention a trait method (no calls in the fact language,
[safety.md](safety.md#refinements-in-types)).

### Error messages

The checking model makes errors local:

- In a generic body: "`T` has no method `cmp`", with the help "add a bound:
  `[T: Ordered]`".
- At a call: "`Point` doesn't implement `Ordered`", pointing at the
  argument, with a note at the bound that requires it (`max[T: Ordered]`)
  and the help "add `impl Ordered for Point`". There is never a trace into
  the generic body.
- Inference: "can't tell what `T` is", with the help "write `max[u32](...)`
  or give the result a type".
- A failed proof in a generic body names `T`'s range as "any `Integer`"
  instead of a 39-digit number.

## `comptime`

**Status:** Proposed; What M7 needs is implemented: items 1 to 4 and 6 in
M7d ([in the compiler](#m7d-in-the-compiler)), 5 in M7e
([in the compiler](#m7e-in-the-compiler))

[comptime.md](comptime.md) describes the mechanism. M7 needs a part of it.

### What M7 needs

1. **Constants computed by calls.** `const TABLE: [256]u32 =
   make_table()`, where `make_table` is an ordinary function. Constants of
   any type that can be stored (integers, `bool`, arrays, structs, enums,
   optionals), not only integers as today.
2. **`if comptime`** in function bodies, with `target` (`os`, `arch`,
   `endian`, `pointer_bits`, `profile`) and constants. The untaken branch is
   removed before checking (Decided in comptime.md).
3. **Per-target declarations at package scope**, so `std/os` can hold
   Linux and other implementations side by side:

   ```
   if comptime target.os == .linux {
   	pub fn write(fd: i32, s: str) -> isize { ... }
   } else {
   	compile_error("std/os: unsupported target")
   }
   ```

   **Options:** this, or Go's file suffixes (`os_linux.lode`). Suffixes are
   simple but a second mechanism, and they can't express
   `target.cpu.has(.avx2)`. **Recommendation:** package-scope `if comptime`,
   with conditions limited to `target`, literals and `&&`, `||`, `!`, `==`,
   so they're evaluated before names are resolved, with no cycles.
4. **`compile_error("...")`**, an error at the place it's evaluated.
5. **Compile-time parameters and packs** for format strings
   ([Format strings](#format-strings)).
6. **`lode check --targets=...`** checks a package once per target. It's
   what keeps dead branches from rotting (comptime.md).

### Rules

As in comptime.md, unchanged:

- **Hermetic**: no `syscall`, no `unsafe`, no I/O. `embed_file` comes later.
  A call to `syscall` reached at compile time is an error that shows the
  call chain.
- **Bounded**: a step budget per evaluation (a step is one statement or one
  call; proposed default one million), and a memory budget. Exceeding it is
  an error with the chain of calls. `@comptime_budget(n)` on a declaration
  raises it.
- **Same semantics as runtime**: the code is the same code, already checked
  and proven. Arithmetic is exact and host-independent; `usize` is the
  target's.

### Proof obligations in compile-time code

A function called at compile time is an ordinary function: it was checked,
and its obligations proven, like any other. So its evaluation can't
overflow or index out of bounds.

Code that runs **only** at compile time is different: a `comptime` block,
the initializer of a `comptime let`, a `comptime for`, the evaluation of a
package-scope `if comptime`. It never runs in the program, so there's no
crash path to rule out. **Proposal:** its obligations are discharged by
running it. An index out of bounds there is a compile error at the point of
failure, with the evaluation's chain, which is what comptime.md already says
("a failure during comptime evaluation is a compile error"). This keeps
format-string parsing ordinary code instead of code written for the prover.

### The evaluator

**Options:** (1) a tree-walking interpreter over the checker's typed tree;
(2) lowering to LatticeFoundry's IR and running its interpreter.

**Recommendation: 1.** Compile-time values must be known *during* checking
(an array length, a value argument, a branch to remove), before anything is
lowered. The interpreter works on abstract values (integers as `i128`
within their type, aggregates as lists), with no memory layout, so it's
host-independent by construction. It needs function bodies checked on
demand (a constant may call a function checked later), which changes the
checker's order from "constants, then every function" to "on demand, with
cycle detection", as `const_value` already does for constants.

### Deferred

- **Reflection** (fields and variants of a type). Open in comptime.md; the
  leaning there (read-only, respects visibility) stands. Without it, `Format`
  for a struct is written by hand.
- **Code generation** (declarations built at compile time). Not planned.
- **`embed_file`**.
- `comptime` parameters of arbitrary types (types as values, Zig's `type`).
  M7 has types only in brackets, where bounds check them.

### Format strings

**Status:** Implemented (M7e), with the differences in
[M7e in the compiler](#m7e-in-the-compiler): no buffer, and the parts of
the format found by index rather than in a list

`print("x = {}\n", x)` is the reason std needs comptime soon. It's built
from three pieces.

1. **A compile-time parameter in the argument list**, `comptime fmt: str`.
   The argument must be known at compile time. Unlike a value parameter in
   brackets, it doesn't change types, so it's passed like any argument.
2. **A pack**: `..A: Format` is any number of type parameters, each
   satisfying `Format`, and `args: ..A` the matching values. A pack can only
   be used with a compile-time index: `args.len`, `args[i]` in a
   `comptime for`. Each `args[i]` is "some `Format`", so the body is checked
   once against the bound.
3. **`comptime for`**: a loop over a compile-time list whose body is
   repeated for each element, with the element known at compile time.

```
pub fn print[..A: Format](comptime fmt: str, args: ..A) {
	comptime let parts = fmt_parse(fmt, args.len)  // ordinary Lode; errors at the call
	if comptime parts.len == 1 && parts[0].is_text() {
		os.write_all(os.STDOUT, parts[0].text)     // hello world: one write
		return
	}
	var out = BufWriter[256].new(os.STDOUT)
	comptime for part in parts {
		match comptime part {
			text(s) => out.write(s)
			arg(i, spec) => args[i].format(&out, spec)
		}
	}
	out.flush()
}
```

- `fmt_parse` is an ordinary function, run at compile time. A `{}` without
  an argument, an argument without a `{}`, or a bad spec is a
  `compile_error` reported at the `print` call.
- `{{` and `}}` are literal braces. `{}` is the only placeholder in M7;
  specs like `{:x}` and widths come with `Format`'s `spec` parameter.
- `print("hello world\n")` is the first branch: one `write`, no formatting
  code linked. The hello-world benchmark must stay at 2 syscalls.
- A runtime string is printed with `print("{}", s)`, which `Format` for
  `str` turns into the same direct write. There's no separate
  `print(s: str)`.
- The same packs give `select(.{...})` its comptime tuple of cases
  ([concurrency.md](concurrency.md#select-without-syntax)).

## Interactions

**Status:** Proposed

### Parameter conventions and views

- Conventions apply to `T` as to any type: `inout x: T`, `sink x: T`,
  `set x: T`. Exclusivity is checked in the generic body as today.
- Swapping or replacing a `T` in place without `Copy` needs moving out of
  a place, which the language doesn't allow. `std/mem` provides `swap` and
  `replace` (`unsafe` inside, safe outside).
- `[]T` and `inout xs: []T` work for any `T`: reading `xs[i]` into a default
  parameter or a method call doesn't copy. `let x = xs[i]` needs `T: Copy`.
- A generic function returning a view borrows from its parameters, with the
  same rule as any function ([memory.md](memory.md#views)).

### Contexts and errors

- `throws(E)` may name a type parameter or an associated type:
  `fn read_all[R: Reader](inout r: R) throws(R.Error) -> ...`. `try` keeps
  today's rule (same error type, no conversion). A function that calls two
  generic operations with different error types has to convert by hand
  until error-set unions exist ([errors.md](errors.md#error-sets)); the
  concurrency doc's `copy[R: Reader, W: Writer]` waits for those.
- An impl's method may throw nothing where the trait's throws, never a
  different type.
- `uses alloc` is part of a trait method's signature. An impl may use fewer
  contexts than the trait declares, never more. A generic function that
  calls a trait method with `uses alloc` must declare it too. The rule is
  the same for `uses task` later.

### Sequencing with the allocator

Heap containers (`List[T]`, `Map[K, V]`, `Box[T]`) need generics *and* the
allocator context. **Recommendation:** M7 doesn't wait for allocation. It
ships generics with fixed-capacity types (`StackBuf[N]`, `ArrayVec[T, N]`)
and generic functions over slices. The allocator context comes in its own
milestone right after, and its containers are the first big user of M7.
`StackBuf[N]` is also option 3 for
[uninitialized buffers](memory.md#uninitialized-buffers). M7b ships
`StackBuf[N]` and `ArrayVec[T, N]` ([M7b in the compiler](#m7b-in-the-compiler)).

### Strings

`str` stays built in during M7. Moving to `Str[E]` with an `Encoding` trait
needs associated types and constants (M7c), plus literals re-encoded at
compile time; it's a separate step after M7, with `str` remaining the name
of `Str[utf8]` ([strings.md](strings.md)). M7c ships the trait and two
encodings as a library over bytes, `std/encoding`
([M7c in the compiler](#m7c-in-the-compiler)).

## Implementation plan

**Status:** Implemented: M7a to M7e

Five steps, each shippable on its own with tests, std changes and docs, as
the earlier milestones were. Sizes are rough estimates of compiler code
(the compiler is about 14,000 lines today).

### M7a: generic functions over the built-in traits

- Parser: `[...]` after a function name (today an error), generic arguments
  in types and after expressions (the `[T]` rule above), `+` in bounds.
- Checker: type parameters as a new `Ty::Param`, the built-in traits
  `Eq`, `Ordered`, `Integer`, `Unsigned`, `Signed`, `Copy` with their
  compiler impls, bounds at call sites, inference from arguments and the
  expected type, the move-only rule for `T`.
- Facts: hull and intersection ranges for numeric bounds, the relation
  rule for "fits in `T`", literal checks.
- `src/mono.rs`: instantiation from `main` (replacing the walk in
  `reach.rs`), substitution, symbols with arguments. Lowering sees
  concrete types only.
- About 1,500 to 2,000 lines.
- **std gains:** `math.min`, `max`, `clamp`, `abs` for any integer;
  `sort[T: Ordered](inout xs: []T)`; `io.print_int[T: Integer]` replacing
  `print_u64` and `print_i64` (until M7e removes it too).

### M7a in the compiler

**Status:** Implemented (2026-10-04)

What M7a does, and the choices made while implementing it where this
proposal left room:

- **Declarations.** `fn name[T: A + B, U](...)` declares type parameters,
  each bounded by built-in traits joined with `+`. A bound that isn't one of
  the six, a generic `main`, and a parameter that is both `Unsigned` and
  `Signed` are errors. (Value parameters, `[N: usize]`, and generic
  methods, `fn Point.f[T]`, were errors too until M7b.)
- **The traits.** `Eq`: every type the compiler has but views. `Ordered`:
  the integers and `bool` (structs and enums wait for `impl`, M7c). `Copy`:
  every type, except a type parameter without the bound and what holds one
  (`?T`, `[N]T`); a view is `Copy`. `Integer`, `Unsigned`, `Signed`: the
  integer types. `Ordered` implies `Eq`, and the numeric bounds imply
  `Ordered` and `Copy`.
- **`Ordered`'s methods** are `cmp`, `lt`, `le`, `gt` and `ge`, on a `T:
  Ordered` and on every integer and `bool` (on a numeric type, `a.lt(b)`
  gives the facts `a < b` gives). `min` and `max` are functions in
  `std/math` rather than methods for now. `a.cmp(b)` returns the built-in
  `Ordering`, a C-style enum `i8 { less = -1, equal = 0, greater = 1 }`,
  so `i8(a.cmp(b))` is the usual -1, 0 or 1. A package may declare its own
  `Ordering`, which hides the built-in one there.
- **Operators.** On a type parameter, `==` and `!=` need `Eq`; every other
  operator (`<`, arithmetic in all its modes, bitwise, shifts, `~`) needs a
  numeric bound, and `-x` needs `Signed`. `T(x)` converts an integer to a
  numeric `T`, and `u64(x)` converts a `T` like any integer.
- **Type arguments.** Explicit and complete, or none. Inferred from the
  arguments in order: an argument whose parameter's type has an unknown
  type parameter is checked on its own, and its type fixes it (an array
  fixes `[]T`, a value fixes `?T`); an argument that takes its type from
  the context (an integer literal, `none`, `.name`, an array literal) waits
  until the others and the expected type are used. Then the type expected
  for the result fixes what's left. A type argument can't be a view, `()`,
  a pointer or a call's result.
- **Bounds at a call** are checked where each type argument came from:
  "`Point` doesn't implement `Ordered`, which `max` requires of `T`".
- **Copies and moves.** A value of a type that isn't `Copy` is kept (stored
  in a variable, a field, an element or an optional, returned, passed
  `sink`, bound by a pattern, taken out by `??`) by moving it. Only a `let`
  or `var`, or a `sink` parameter, can be moved from, whole, and not from a
  `defer` block when it's declared outside it; using it again before it's
  assigned is an error, on any path, loops included. Keeping an element, a
  read-only parameter or an `inout` one is a copy, an error without `Copy`,
  as is `[v; n]`. Reading in place (comparing, calling a method, passing to
  a parameter that isn't `sink`) needs nothing.
- **Facts** about integer type parameters follow
  [Facts about `T` values](#facts-about-t-values), over the integer types
  the compiler has (up to 64 bits): the exact rule is in
  [safety.md](safety.md#values-of-a-type-parameter).
- **Instances.** `src/mono.rs` replaces `src/reach.rs`: from `main`, it
  makes one function per generic function and type arguments reached,
  ordered like the functions in the program, with symbols like
  `main.max[u32]` and `std/slices.sort[main.Point]` (a struct or an enum by
  its package's path). A cycle of calls between generic functions must
  pass type parameters unchanged (`f[T]` calling `f[?T]` is an error), so
  there are finitely many instances.
- **std.** `std/math` (`min`, `max`, `clamp` over `Ordered`, `abs` over
  `Integer`, saturating), `std/slices` (`sort` for `Ordered + Copy`
  elements, a heapsort, and `is_sorted`), and `io.print_int[T: Integer]`
  and `io.eprint_int`, which replace `print_u64`, `print_i64` and their
  `eprint` forms.

### M7b: generic structs and enums, value parameters, generic methods

- Instantiated types in the interner (a declaration plus arguments),
  inference for literals, implied bounds, methods with added bounds,
  `[N: usize]` as a term.
- About 1,000 to 1,500 lines.
- **std gains:** `StackBuf[N]` (and with it the end of `[0; 21]` in
  `std/io`), `ArrayVec[T, N]`, `Pair` if wanted.

### M7b in the compiler

**Status:** Implemented (2026-10-04)

What M7b does, and the choices made while implementing it where this
proposal left room:

- **Declarations.** `struct Pair[A, B: Ordered]` and `enum Either[L, R]`
  declare generic parameters with bounds, as a function does. A value
  parameter, `[N: usize]`, has an integer type (any of them; `bool` not
  yet). A C-style enum can't be generic.
- **Types.** `Pair[u8, bool]` is an instance: the declaration plus its
  arguments, interned like other compound types. So `Pair[u8, bool]` and
  `Pair[u8, u16]` are two types, and two spellings of one instance are the
  same type. A value argument is an integer known when compiling (a
  literal, a constant) or a value parameter of the same type. The
  arguments must satisfy the declaration's bounds where the type is
  written. In a type, a generic type's name needs its arguments: `let p:
  Pair = ...` is an error.
- **Inference in literals.** `Pair{first: b, second: true}`,
  `Either.left(x)` and `Pair.new(a, b)` infer the arguments with the rule
  of calls: from the values, in order, then from the expected type. A
  value that takes its type from the context (an integer literal, `none`,
  `.name`, an array literal) doesn't fix an argument. A literal of a
  generic type written without its arguments, nested in another, waits for
  the expected type too, and fixes them itself when that doesn't. Explicit
  arguments are written on the type: `Pair[u8, u16]{...}`,
  `Pair[u8, bool].new(...)`.
- **Value parameters are terms.** In a body, `N` is an immutable local of
  its type, which each instance assigns first; in the fact language it's a
  term like any local ([safety.md](safety.md#values-of-a-type-parameter)).
  `[N]T` has length `N`: `a.len`, `for x in a` and slicing use it, and
  `a[i]` is proven by `i < N` (or `i < a.len`) once, for every `N`.
  `[v; N]` builds one. `N` can be used as a value of its type (`x *| K`).
  It's also inferred from an argument's array length (`total(a)` with
  `a: [3]u32`) or the expected type. No refinements yet: `[N: usize where
  N > 0]`, and a field `len: usize where len <= N`, wait for them.
- **Methods.** `fn Pair[A, B].swap(self)` names every parameter of the
  type, in order, under any names; a value parameter is written `N` (or
  `N: usize`). The type's bounds are implied. A method can add bounds,
  `fn Pair[A: Ordered + Copy, B].min_first`, and then exists only where
  they hold: a call where they don't is an error at the call, "`Point`
  doesn't implement `Ordered`, which `Pair.min_first` requires of `A`". A
  method can have parameters of its own, `fn Pair[A, B].with_first[C]`,
  given after its name (`p.with_first[u16](5)`) or inferred; so can a
  method of a type that isn't generic.
- **Calls.** A method's receiver gives the type's arguments (`p.swap()` on
  a `Pair[u8, bool]`). An associated function takes them from the type
  written before it (`Pair[u8, bool].new(...)`), or infers them
  (`Pair.new(a, b)`, `let v: ArrayVec[u8, 4] = ArrayVec.new()`).
- **Bounds in functions.** A generic function that names a bounded generic
  type must have the bound itself: `fn f[T](s: Sorted[T])` is an error
  when `Sorted` requires `T: Ordered`. Only a method gets its type's
  bounds implied.
- **Copy and moves.** A struct or an enum is `Copy` when every field of
  the instance is: `Pair[T, U]` is `Copy` only if `T` and `U` are. Keeping
  a field of a value that isn't `Copy` moves the whole variable out (there
  are no partial moves yet). So `swap` with a read-only `self` needs
  `A: Copy, B: Copy`, and `fn Pair[A, B].into_first(sink self)` needs
  nothing.
- **Recursive types.** A struct or an enum that holds any instance of
  itself by value is an error, "the struct `Holder` contains itself", also
  through another generic type's parameter (`p: Pair[u8, Holder]`), and
  when its instances would grow without end (`struct W[T] { w:
  ?W[Pair[T, T]] }`). What each declaration holds, by declaration and by
  parameter, is a fixed point over the declarations, so the check ends.
- **Instances.** `src/mono.rs` makes one function per method and set of
  arguments `main` reaches. A symbol puts the type's arguments after its
  name, and the method's own after the method's: `std/buf.StackBuf[64].push`,
  `main.Pair[u8, bool].with_first[u16]`. A call in a cycle that makes
  instances grow is an error naming the instance, "this calls
  `Grow[Pair[T, T]].deeper`, which calls back here".
- **`?T` stays built in**, as decided above.
- **std.** `std/buf.StackBuf[N]`, a byte buffer written at either end;
  `std/vec.ArrayVec[T: Copy, N]`, a vector of at most `N` elements; and
  `io.File.write_buf`, which writes a `StackBuf`'s bytes
  ([packages.md](packages.md#the-standard-library-in-the-compiler-today)).
  (`io.print_int` built its digits in a `StackBuf[21]` at first, and went
  back to a plain array: 640 bytes less at `-O2`.) Every access in
  them is proven. Without refinements, each method checks the invariant it
  needs (`end <= N`), and without private fields, `StackBuf` still fills
  its storage when it's made ([memory.md](memory.md#uninitialized-buffers)).
  `ArrayVec` keeps its elements as `[N]?T`, so it needs no value to fill
  empty slots with, and `T: Copy` to make them `none`.

### M7c: user traits

- `trait` declarations: methods, associated functions, types and constants,
  default methods, supertraits. `impl` blocks, conditional impls, the
  coherence check, derived `Eq` for generic types, dot calls on trait
  methods.
- About 1,500 to 2,000 lines.
- **std gains:** `Ordered` for user types, `io.Writer` implemented by
  `io.File`, the `Encoding` trait and `utf8` (as a library, beside the
  built-in `str`).

### M7c in the compiler

**Status:** Implemented (2026-10-05)

What M7c does, and the choices made while implementing it where this
proposal left room:

- **Traits.** `trait Shape: Named + Copy { ... }`, or `pub trait` to be
  used from other packages, holds one item per line: methods (`self`,
  `inout self` or `sink self`), associated functions (no `self`), a body
  for a default method, associated types (`type Rune: Copy + Eq`) and
  associated constants of an integer type (`const MAX_LEN: usize`). In a
  trait, `Self` is the implementing type, and `Rune` and `MAX_LEN` are
  `Self.Rune` and `Self.MAX_LEN`. A default method's body is checked once,
  with `Self` a type parameter bounded by the trait. A trait that is its
  own supertrait, directly or not, is an error. A trait isn't generic, and
  its methods have no generic parameters of their own yet.
- **Bounds** name traits declared in Lode beside the built-in ones, in the
  package or another: `[W: io.Writer]`, `[T: Shape + Copy]`. A bound brings
  its supertraits: with `trait Ranked: Ordered`, `T: Ranked` has `lt`.
- **Impls.** `impl Shape for Rect { ... }` gives the trait's methods, each
  with the trait's signature, `Self` replaced by the type: the same
  parameters, conventions, return type and error type (or none where the
  trait throws). A missing required method, a method the trait doesn't
  have, and a signature that differs are errors at the impl, with the
  signature to write. A default method the impl doesn't give is the
  trait's. The impl also gives every associated type (`type Rune = u32`)
  and constant (`const MAX_LEN: usize = 4`, known when compiling). Its
  type must implement the trait's supertraits, and its associated types
  their bounds.
- **What an impl is for.** A named type: a struct, an enum, an integer type
  or `bool`. A generic type is written with the impl's parameters, one per
  parameter of the type and in order, as a method of the type names them:
  `impl[A: Ordered] Ordered for Pair[A]`, `impl[N: usize] Writer for
  buf.StackBuf[N]`. The type's bounds are implied; the impl's own make it
  conditional: `Pair[Point]` is `Ordered` only if `Point` is. An impl for
  a type parameter (`impl[T] Shape for T`) is an error: there are no
  blanket impls. So is an impl for one instance (`impl Shape for
  Pair[u8]`): with one impl per trait and named type, it would be the only
  one for all of `Pair`.
- **Coherence** (question 5, as recommended). An impl is in the trait's
  package or the type's. The built-in traits and the primitive types
  belong to the standard library. A second impl of a trait for a type is an
  error. `impl Eq` is an error, as equality is derived (question 4, as
  recommended), and so are `impl Copy` (automatic) and impls of `Integer`,
  `Unsigned` and `Signed` (sealed).
- **`impl Ordered`.** A struct or an enum implements the built-in `Ordered`
  with `fn cmp(self, other: Self) -> Ordering`. It may also give `lt`, `le`,
  `gt` and `ge` (`-> bool`); the others are `cmp`'s result compared with
  `.less` or `.greater`. Then `slices.sort`, `math.min` and the rest work
  on it. `<` still doesn't (question 3). The type must be `Eq`.
- **Calls.** `p.area()` finds the type's own method first, then the
  methods its impls give (theirs, or the traits' defaults). The doc's "one
  namespace" isn't an error at the impl: a clash between the type's method
  and an impl's is resolved for the type's, and `io.File` has both its own
  `write` and `Writer`'s. When two impls give the method, the call is an
  error, and `Shape.area(p)` (or `io.Writer.write(&f, s)`) calls through
  the trait, with `self` as the first argument, passed as it's declared.
  An associated function is called on the type: `Rect.unit()`, or
  `T.unit()` in a generic body. On a type parameter, the built-in
  `Ordered`'s methods come first, then those of the other bounds; two of
  which giving a method is an error too.
- **Generic bodies** are checked once against the traits, as before: a
  trait's method on `T` has the trait's signature with `Self` as `T`. A user
  trait gives no operator (`a < b` on `T: Shape` is an error).
- **Associated items.** `E.Rune` in generic code is a type parameter that
  stands for each instance's type; `E.MAX_LEN` is a value, like a value
  parameter: a term for the checker, and an array's length in
  `[E.MAX_LEN]u8`. On a type, `Utf8.Rune` and `Utf8.MAX_LEN` are what its
  impl gives. An associated type can't be the error type in `throws` yet.
- **Dispatch** is static. A trait's method called on a type parameter, or
  through the trait, is a call of the trait's function with `Self` as its
  first type argument. `src/mono.rs` makes it a call of the method of
  `Self`'s impl once `Self` is known, or of an instance of the trait's
  default; the compile-time evaluator does the same, so a constant can call
  generic code bounded by a trait. An impl's method's symbol names its
  trait after the method, since the type may have a method of the same
  name: `main.Point.cmp<Ordered>`, `std/io.File.write_bytes<std/io.Writer>`;
  a default method has the trait's name and `Self`:
  `std/io.Writer[std/buf.StackBuf[4]].write`. The check that instances end
  follows calls through traits.
- **std.** `io.Writer` (`write_bytes` required, `write` a default), which
  `io.File` and `buf.StackBuf[N]` implement, the latter in `std/io`, the
  trait's package; `std/encoding` with `Encoding` as above (`decode`
  returns `?Decoded[Rune]`, a struct, since there are no tuples),
  implemented by `Utf8` and `Ascii`, and `count[E]`. An encoding is an enum
  of one variant, a type that's never a value: structs without fields
  aren't supported yet ([packages.md](packages.md#the-standard-library-in-the-compiler-today)).
- **Not yet:** generic traits, trait methods with generic parameters of
  their own (since M7e, they are), `uses` in traits, `Format` (M7e), `dyn
  Trait`, and declaring the built-in traits in Lode.

### M7d: compile-time evaluation and target selection

- The evaluator with budgets, constants of any storable type computed by
  calls, `if comptime` in bodies and at package scope, `target`,
  `compile_error`, on-demand checking of functions, `lode check
  --targets=...`.
- About 1,500 to 2,500 lines, most of it the evaluator.
- **std gains:** `std/os` split by `target.os` and `target.arch` (one real
  target until LatticeFoundry's others are wired, but the structure for
  them), tables built at compile time.

M7d depends only on M7a and could go before M7b or M7c if multi-target work
becomes urgent.

### M7d in the compiler

**Status:** Implemented (2026-10-04)

What M7d does, and the choices made while implementing it where this
proposal left room:

- **Constants.** A typed constant's value is any expression of its type,
  calls included: `const CRC_TABLE: [256]u32 = make_crc_table()`. Its type
  is an integer, `bool`, or an array, struct, enum or optional of those
  (instances of generic types too). An array of integers or `bool` is a
  table in read-only data, as before, and the checker knows the range of
  its elements. Another constant is built where it's used, so it holds at
  most 256 scalars. Untyped constants are still integer literals.
- **The evaluator** (`src/sema/eval.rs`) walks the typed tree, as
  recommended. An integer is an `i128` within its type; an array, a
  struct or an enum is a list. Arithmetic in every mode, shifts,
  conversions, `match`, `try`, `catch`, `defer`, `inout` and `set`
  arguments (copied in, then out), slices, and generic functions and
  methods (with the instance's type and value arguments) behave as at
  run time. tests/programs/comptime_semantics.lode runs the same function
  both ways and compares.
- **On-demand checking.** A function a constant calls is checked then,
  before the others, and once: its errors are reported once. A function
  with errors isn't run, and the constant fails without another error. A
  value that needs itself, also through a function's body, is an error:
  "the value of `X` depends on itself". When a trial check of a loop body
  is rolled back, the functions checked during it are checked again later.
- **Types are declared first.** A constant needed to declare a type or a
  signature (an array length in a field or a parameter) can't call a
  function: "a constant needed to declare a type or a signature can't
  call a function". A computed constant can be a value argument in a
  body: `StackBuf[SIZE].new()`.
- **Checked by running it** (decision 7). A constant's value and an `if
  comptime` condition only run at compile time. An operation in them the
  prover can't prove (an overflow, an index, a slice, a division, a
  shift, a negation, a conversion) is checked as it runs, and a failure is
  an error at it: "evaluating `BIG` at compile time: 100 * 3 overflows
  `u8`". The functions they call were checked and proven like any other.
- **Bounds.** A budget of one million steps (a step is a statement, a
  loop iteration or a call); `@comptime_budget(n)` on the line before a
  `const` sets another. A memory budget of 16,777,216 scalars allocated
  (arrays built, or copied to be changed). At most 1,000 nested calls.
  Going over one is an error with the calls running, innermost first; a
  recursion is one line, "in `depth`, 1000 calls deep". The checker runs
  on a thread with a 256 MiB stack, which the evaluator's recursion
  needs.
- **Hermetic.** A raw pointer (`s.ptr`, `p + n`) or a `syscall` reached at
  compile time is an error, with the calls that reached it. `unsafe` code
  that only computes runs.
- **`target`** is a value of the built-in struct `target.Target`: `os`
  (`target.Os`: `linux`, `none`), `arch` (`target.Arch`: `x86_64`,
  `aarch64`, `wasm32`, `arm`, `avr`), `pointer_bits` (a `u32`) and
  `endian` (`target.Endian`: `little`, `big`). `target.os` and the others
  are known values, with facts. A local or a declaration named `target`
  hides it. `profile`, `abi` and CPU features wait for profiles.
- **`if comptime` in a function** checks only the branch its condition
  picks; the others must parse. The branch is a block of its own. The
  condition is evaluated: constants, `target`, calls and operators, never
  a variable ("`n` is a variable, so this condition isn't known when
  compiling").
- **`if comptime` at package level** picks declarations, nested `if
  comptime` included. Its condition is evaluated before names are
  resolved, so it uses only `target`, literals, comparisons, `&&`, `||`
  and `!`, as recommended.
- **`compile_error("message")`** is an error where it's compiled: a
  statement in a body that's checked, or a declaration of a package
  outside `if comptime` or in a branch the target takes. At package level
  it also ends the check, since what uses the package would only give
  errors that follow from it.
- **Targets.** `lode targets` lists the targets: x86_64-linux, which is
  built, and aarch64-linux, wasm32, thumbv7m (Cortex-M) and avr, which are
  checked only, as LatticeFoundry can generate code for them
  ([backend.md](backend.md)) but Lode doesn't use it yet. `lode check
  --targets=x86_64-linux,aarch64-linux` (or `all`) loads and parses once
  and checks once per target. Each message is printed once, with the
  targets it's for unless it's all of them. `usize` has the target's
  width (16 bits on avr), and so does the longest view.
- **std.** `std/os` is the Linux implementation inside `if comptime
  target.os == .linux`, with the system call numbers per architecture
  (x86-64 and AArch64); any other target gets `compile_error("std/os:
  unsupported target")` ([packages.md](packages.md#per-target-code)).
  Hello world is unchanged: 655 bytes, two system calls.
- **Not yet:** `comptime` parameters, packs, `comptime for` and `match
  comptime` (M7e has them); `comptime` blocks and `comptime let` (M7e has
  `comptime let`); `str` constants; conditional imports; building for a
  target other than x86_64-linux.

### M7e: format strings

- `comptime` parameters, packs, `comptime for`, `match comptime`, the
  "discharged by running it" rule, `Format` with impls for integers, `bool`
  and `str`.
- About 1,000 to 1,500 lines, plus `fmt_parse` and `BufWriter` in std.
- **std gains:** `io.print("x = {}\n", x)` and `io.eprint`; `print_u64`,
  `print_i64` and `print_int` go away. Hello world stays 2 syscalls, and
  its size is checked in CI.

### M7e in the compiler

**Status:** Implemented (2026-10-05)

What M7e does, and the choices made while implementing it where this
proposal left room:

- **`comptime` parameters.** `comptime fmt: str`, of an integer type,
  `bool` or `str`. The argument must be known when compiling: a literal,
  a constant, a `comptime` value of the caller, or an expression of
  those. A variable is an error at the argument: "`fmt` of `io.print` is
  `comptime`, so its argument must be known when compiling, and `s` is a
  variable".
- **Packs.** `[..A: Format]` declares a pack, the last generic parameter,
  and `args: ..A` is its parameter, the last one: any number of
  arguments, each of a type with the pack's bounds. In the body,
  `args.len` is a `usize` known when compiling, `args[i]` needs an `i`
  known when compiling, and `..args` passes the pack on as a call's last
  argument. A pack's types may be views, so that `print("{}", s)` takes a
  `str`: the arguments are read-only parameters, and `args[i]` can only
  be the `self` of a trait's method or be passed on in another pack. A
  generic function or type, which may store a value, can't take a pack's
  type as an argument (an error).
- **Templates and expansions.** A function with `comptime` parameters or
  a pack isn't checked on its own. Each call makes (or reuses) an
  expansion of it: the function for the call's `comptime` values and
  number of pack arguments, a function of its own (`std/io.print$3`). In
  it, the `comptime` parameters are values known when compiling, and the
  pack is that many type parameters and parameters. The expansion is
  checked like a generic function: once for the pack's types, against
  their bounds, as proposed; the values known when compiling shape its
  body, as an `if comptime` condition does. So a template that nothing
  calls is only parsed, like an `if comptime` branch not taken. An error
  found in every expansion is reported once. Expansions nest at most 64
  deep (a template calling itself with new values).
- **Statements that run when compiling.** `comptime let x = e` computes a
  value when compiling. `comptime for x in a..b` (of `usize`) or
  `comptime for x in list` (an array or a slice known when compiling)
  checks its body once for each value, with `x` known; `break` and
  `continue` can't leave it, and it repeats at most 1,000 times. `match
  comptime v { ... }` checks only the arm `v` picks (a variant with its
  payload, a value, a range, `_`), and no arm matching is an error. An
  `if comptime` condition can use these values. In code that runs with
  the program, a value known when compiling is its literal.
- **Checked by running it** (decision 7), for these too: the value of a
  `comptime let`, the list of a `comptime for`, the value of a `match
  comptime`, and a `comptime` argument. There, a `str` can be sliced
  (`fmt[i..j]`): the evaluator checks the bounds, and that they don't
  split a character.
- **`compile_error`** takes values for the `{}` in its message:
  `compile_error("{} is odd", n)`, with `{{` and `}}` for braces.
  `compile_error_at(place, message, values...)` points at `place`, a `str`
  that's part of a string literal in the source, such as a slice of a
  format string. In code that runs when compiling (the `catch` of a
  `comptime let`), it's an error when it's reached. In an expansion, it's
  reported at the call that made it, or at the outermost one when an
  expansion calls another (`print`'s format errors are at the user's
  `print`, not in `std/io`).
- **`Format`** is a trait of `std/io`:
  `fn format[W: Writer](self, inout w: W) throws(os.Error)`. That needed
  trait methods with generic parameters of their own, which M7c didn't
  have: an impl's method declares the same ones, with the same bounds,
  and a call through the trait passes them on. Impls for `str` are now
  allowed. `std/io` implements `Format` for every integer type (decimal,
  with a `-` when negative), `bool` (`true`, `false`) and `str` (as it
  is); a user type implements it with `impl io.Format for Point`, which
  may itself call `io.write_fmt`. A generic function that prints a `T`
  needs the bound, `[T: Integer + io.Format]`: `Integer` doesn't imply it.
- **Format strings.** `format_pieces` and `format_piece` in `std/io` are
  ordinary Lode, run when compiling, and `write_fmt` finds piece `k` with
  `format_piece(fmt, k)` rather than keeping a list, which would need a
  growable list of a type that holds a `str`. `{}` is an argument, `{{`
  and `}}` a brace. A piece of text runs up to a brace, and `{{` or `}}`
  ends it with the brace, so text without braces is one piece. The
  errors, at the call: "unclosed `{` in the format string" and "unmatched
  `}` in the format string" at the brace; a spec like `{:x}` ("a
  placeholder is `{}`: format specs are not supported yet"); "this `{}`
  has no argument: 3 placeholders but 2 arguments" at that `{}`; "1
  placeholder but 2 arguments: each argument needs a `{}` in the format
  string"; and an argument whose type isn't `Format`: "`Point` doesn't
  implement `io.Format`, which `io.print` requires of `A`".
- **`io.print`, `io.eprint`, `io.write_fmt`.**
  `print[..A: Format](comptime fmt: str, args: ..A)` writes each piece of
  text with one `os.write_all` and each argument with its `Format` impl,
  ignoring errors; `eprint` writes to standard error. `write_fmt[W:
  Writer, ..A: Format](inout w: W, comptime fmt: str, args: ..A)
  throws(os.Error)` writes to any `Writer` (a `File`, a `StackBuf`) and
  passes errors on. `print_int` and `eprint_int` are gone (decision 8).
  `print("hello world\n")` is one `write` and no formatting code.
- **No buffer** (a choice by measurement). The proposal's
  `BufWriter[256]` makes one `write` per `print`. A 256-byte buffer in
  `print` (zeroed, filled byte by byte, flushed) made programs that print
  integers 1 to 3 KB larger at `-O2`, so each piece is its own `write`:
  `print("x = {}\n", x)` is three. A buffered writer is for later, with
  uninitialized buffers ([memory.md](memory.md#uninitialized-buffers)).
- **An impl's method that doesn't throw, called through a trait's that
  does** (`print`'s writer ignores errors): `crate::mono` makes an
  instance of it that returns a result (`<throws>` in its symbol), and
  the evaluator wraps its value the same way. M7c allowed such impls, but
  their calls through the trait didn't lower.
- **Sizes** at `-O2`, with the cleanup after inlining of the same day
  (unused functions dropped, blocks merged): hello world 577 bytes (655
  before both); tests/programs/print_integers.lode 3,918 bytes (2,884
  with `print_int`); the dogfood programs from 2,750 to 21,471 bytes,
  some larger and some smaller than with `print_int` (dogfood_bit_tricks
  +1,303, dogfood_integer_edges -2,986). All runnable test programs:
  436,049 bytes, 2.6% less than with `print_int`. An expansion is a
  function per format string and argument types, and the error each
  `Format` impl may throw is checked after it, even when the writer
  can't fail.
- **Not yet:** format specs (`{:x}`, widths: `Format` gains a `spec`
  parameter), `comptime` parameters of other types (types as values),
  methods with `comptime` parameters or packs, packs for `select`
  ([concurrency.md](concurrency.md#select-without-syntax)), a buffered
  writer, and `Format` derived by reflection.

### After M7

`dyn Trait`; the allocator context and heap containers; `Send`/`Sync` with
the concurrency work; `Str[E]`; error-set unions with generic errors; code
sharing for small targets; reflection.

## Decisions

**Status:** Decided 2026-10-04 for questions 1–3 and 6 (by the user); the
others keep the recommended answer unless the user changes them.

1. **Traits are implemented in `impl Trait for T { ... }` blocks** holding
   the methods, callable as `p.cmp(q)` ([Implementations](#implementations)).
   *Decided.*
2. **`T` is not copyable by default:** copying needs `T: Copy`, and `max`
   takes `sink` parameters
   ([`Copy` and moves](#copy-and-moves-in-generic-code)). *Decided;
   implemented in M7a.*
3. **`<` doesn't work on `T: Ordered`:** only sealed numeric bounds get
   operators, `Ordered` gives `a.lt(b)`
   ([Operators in generic code](#operators-in-generic-code)). *Decided;
   implemented in M7a.*
4. **Equality is derived only:** `Eq` is never written by hand, stays
   automatic as today, and floats (so structs with float fields) aren't
   `Eq`. This closes types.md's "opt-in or automatic" question as automatic.
   *Recommended, pending; followed in M7c (`impl Eq` is an error).*
5. **Coherence:** impls live in the trait's or the type's package, one per
   trait and type, no blanket impls ([Coherence](#coherence)).
   *Recommended, pending; implemented in M7c.*
6. **Per-target code uses package-scope `if comptime`**, not file-name
   suffixes ([What M7 needs](#what-m7-needs)). *Decided; implemented in
   M7d.*
7. **Code that only runs at compile time is checked by running it** instead
   of by the prover ([Proof obligations in compile-time
   code](#proof-obligations-in-compile-time-code)). *Recommended, pending;
   implemented in M7d for constants' values and
   `if comptime` conditions, and in M7e for `comptime let`, `comptime
   for`, `match comptime` and `comptime` arguments.*
8. **One `print`:** `io.print` becomes the formatted print with a
   compile-time format, and `print(s)` of a runtime string becomes
   `print("{}", s)` ([Format strings](#format-strings)).
   *Recommended, pending; implemented in M7e.*
9. **`dyn Trait` and allocation stay out of M7:** M7 ships with
   fixed-capacity containers, and `dyn` and the allocator context come
   right after ([`dyn Trait`](#dyn-trait),
   [Sequencing](#sequencing-with-the-allocator)). *Recommended, pending.*
