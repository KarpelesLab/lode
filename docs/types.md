# Types

## Primitive types

### Integers

**Status:** Proposed

| Type | Meaning |
| --- | --- |
| `i8 i16 i32 i64 i128` | Signed, two's complement |
| `u8 u16 u32 u64 u128` | Unsigned |
| `usize`, `isize` | Address-sized. 16 bits on 8-bit targets with a 16-bit address space. |
| `uN` / `iN` | Arbitrary width, N ≤ 128 (Open: up to 65535 like Zig?). Maps directly to LatticeFoundry's `Int(width)`. |

There is **no default `int`**. A platform-sized `int` is a portability trap,
especially on 8-bit targets. Every integer has an explicit size, or it is
inferred from context.

**Literals** are compile-time integers of unbounded precision. They take a
concrete type from context, and a literal that does not fit is a compile error:

```
let a: u8 = 300      // error: 300 does not fit in u8
let b = 300          // error: no type from context (Open: default to i32?)
```

### Arithmetic

Plain operators carry a **proof obligation** (see
[safety.md](safety.md#proof-obligations)). When the obligation can't be
discharged, the programmer picks the behavior they want:

| Intent | Operator / method | Result |
| --- | --- | --- |
| Result proven to fit | `a + b`, `a - b`, `a * b` | `T` |
| Wrap around | `a +% b`, `a -% b`, `a *% b` | `T` |
| Clamp | `a +| b`, `a -| b`, `a *| b` | `T` |
| Detect | `a.checked_add(b)` and so on | `?T` |
| Widen | `a.wide_mul(b)` | the double-width type, can't overflow |

Division `a / b` and remainder `a % b` require `b != 0`, and for signed types
also `!(a == MIN && b == -1)`. `a.checked_div(b)` returns `?T`.

Shifts: `a << n` requires `n < bits(T)`. `a <<% n` masks `n`.

Why proofs and not traps: a trap is an implicit crash path. Why not wrap by
default: silent wrapping is a common source of security bugs. Requiring proof
is stricter than both, and it's workable because most arithmetic in real code
is on loop counters, lengths and small constants, which the checker can bound.
**This is the design's biggest ergonomic risk** and must be tested early on real
code.

### Conversions

- **Widening** that can't lose information (`u8` → `u16`, `u8` → `i16`) is
  implicit.
- **Narrowing** `u8(x)` needs a proof that `x` fits. Otherwise use `x.wrap[u8]()`,
  `x.saturate[u8]()` or `x.try[u8]()` (returns `?u8`).
- Signed ↔ unsigned is always explicit and follows the same rule.
- No conversion is implicit if it could fail.

### Floats

`f16`, `f32`, `f64`. `f128` is Open and depends on target support. IEEE-754
semantics.

- Float → int conversion is **defined**: it saturates, and NaN converts to 0. No
  proof obligation.
- Floats are not `Ordered` (NaN), so `max[T: Ordered]` can't take them. They
  have their own `min`/`max` with defined NaN behavior, plus `total_cmp`.
- Soft-float is selected per target when there is no FPU
  ([backend.md](backend.md)).

### Other primitives

| Type | Notes |
| --- | --- |
| `bool` | `true`, `false`. No truthiness: `if x` requires `x: bool`. |
| `()` | Unit. The return type of functions without `->`. |
| `never` | Type of expressions that don't return (`abort()`, infinite `loop`). |
| runes | Per encoding, e.g. `utf8.Rune`. See [strings.md](strings.md). |

## Composite types

### Arrays and slices

- `[N]T`: fixed-size array, a value. `N` is a compile-time `usize`.
- `[]T`: slice, a view into contiguous `T`s. How slices relate to the memory
  model is in [memory.md](memory.md#views).
- `a.len` is always available. Indexing follows the
  [safety rules](safety.md#failure-sources-in-detail).

#### In the compiler today

**Status:** Implemented subset (syntax in [syntax.md](syntax.md#arrays-slices-and-for))

- Element types: integers, `bool`, and arrays (`[4][4]u8`). Arrays and slices
  of other types are not supported yet.
- An array is a value. `let b = a` copies the elements, and changing `a`
  afterwards doesn't change `b`. Array locals live on the stack.
- A slice is a read-only view, a pointer and a length, like `str`. Assigning
  through a slice (`xs[i] = v`) needs `inout`, which isn't there yet.
- An array converts to a slice of all its elements where a slice is
  expected: in a call argument, or in a `let`/`var` with a slice type. A slice
  kept in a local may only view a `let` array (or part of one), so it never
  sees the array change. This stands in for the [view rules](memory.md#views)
  until they're checked.
- Every `a[i]` must be [proven](safety.md#the-fact-language) to be in
  bounds. The index can have any integer type.
- Not yet: passing or returning an array by value (take a slice instead),
  returning a slice, comparing arrays with `==`, slicing (`a[i..j]`), and
  `a.get(i)`.

### Structs

```
struct Point {
	x: f32
	y: f32
}

let p = Point{x: 1, y: 2}
```

- Every field must be initialized. There is no zero-value magic. **Open:** do
  field defaults declared in the struct count?
- Field order in memory is **unspecified** unless the struct is marked
  `@layout(c)` or `@layout(packed)`. This lets the compiler reorder fields per
  target (for example to reduce padding on 8-bit targets).

### Enums (sum types)

```
enum Token {
	ident(name: str)
	number(value: u64)
	eof
}

match tok {
	ident(n) => ...
	number(v) => ...
	eof => ...
}
```

- `match` must be exhaustive. `_` is allowed but linted when used on an enum
  declared in the same package (it hides new variants).
- C-style enums with explicit integer values: `enum Color: u8 { red = 1, green = 2 }`.
  Converting an integer to such an enum returns `?Color`.

### Optional

`?T` is a value of `T` or `none`.

```
if let v = map.get(key) {
	use(v)
}
let v = map.get(key) else { return }
let v = map.get(key) ?? default_value
```

No `.unwrap()`. It would be an implicit crash path. Where the programmer knows
the value is present, the checker should know it too. If it can't, the code
must handle `none`.

Layout: `?T` uses a niche when `T` has one (for example a non-null handle), so
`?T` is the same size as `T`.

### Tuples

`(A, B)`, destructured with `let (a, b) = pair`. **Open:** are tuples needed if
structs are cheap to declare and functions can return multiple values?

### Function types

`fn(i32) -> i32`. A function value is a code pointer. Closures that capture
state are Open; they interact with the memory model and with stack bounds
(indirect calls).

## Distinct types

**Status:** Proposed

```
type UserId = u64        // a new type: UserId and u64 do not mix
alias Bytes = []u8       // just another name
```

Distinct types are cheap and make "is this a byte count or an index?" visible
in signatures.

## Methods

**Status:** Decided that types have methods. The syntax is Proposed.

```
struct Point {
	x: f32
	y: f32
}

fn Point.length(self) -> f32 {
	return sqrt(self.x * self.x + self.y * self.y)
}

fn Point.scale(inout self, k: f32) {
	self.x = self.x * k
	self.y = self.y * k
}

fn Point.origin() -> Point {              // no self: an associated function
	return Point{x: 0, y: 0}
}

let d = p.length()
p.scale(2)                                // mutation, see Open below
let o = Point.origin()
```

- A method is a function whose first parameter is `self`, declared as
  `fn Type.name(...)`. The declaration is greppable: search for `Point.length`
  and you find it.
- `self` takes the usual [parameter conventions](memory.md#chosen-direction-mutable-value-semantics):
  `self` (read), `inout self`, `sink self` (consumes the value, e.g.
  `file.close()`).
- Methods can only be declared **in the package that defines the type** (as
  in Go). No extension methods on other packages' types, so every method a type
  has is found next to its definition.
- Trait implementations are the exception: `impl Ordered for Point { ... }`
  can also live in the package that defines the trait.

**Open:** memory.md marks mutable arguments with `&` at the call site. Should
`p.scale(2)` also need a marker (`(&p).scale(2)` is ugly; maybe `p&.scale(2)`
or nothing, because `inout self` is visible in the declaration)? Leaning
toward no marker on the receiver.

## Operators

**Status:** Decided: no user-defined operator overloading

Operators keep one meaning each. User types can't overload them, because
overloading tends to become a footgun, or bends an operator's meaning for
syntax sugar (C++'s `std::cout << x`). A `+` in Lode is always arithmetic,
and it can always be read without looking up a type's definition.

What operators work on:

| Operators | Types |
| --- | --- |
| Arithmetic, bitwise, shifts | Integer and float primitives, `secret[T]` of them, and SIMD vectors |
| `<` `<=` `>` `>=` | Integer and float primitives. Other types use `.cmp()` from `Ordered`. |
| `==` `!=` | Primitives, plus **compiler-derived** structural equality for structs, enums, arrays and tuples whose parts all have it (like Go's comparable types). This is never user-written, so it can't do anything surprising. **Open:** opt-in per type, or automatic? |
| `a[i]`, `a[a..b]` | Arrays, slices, strings (slicing only), and a fixed set of standard-library containers the compiler knows about (`List`, `Map`, name list Open). This is the same approach as Go, whose built-in map and slice types get syntax that user types don't. |
| `??`, `try`, `catch` | Optionals and error results |

The cost is that math-heavy user types (big integers, complex numbers, matrices)
use methods: `a.add(b).mul(c)`. We accept that cost. If it turns out to be too
high, the only exception we'd consider is a numeric trait with algebraic laws
(`+` must be associative, and so on). That wouldn't cover `<<` for streams.

## Generics and traits

**Status:** Proposed

Generics are compile-time parameters (see [comptime.md](comptime.md)).
**Traits** constrain them so that a generic function is type-checked once, at
its definition, instead of failing deep inside an instantiation (the Zig and C++
template problem):

```
trait Ordered {
	fn cmp(a: Self, b: Self) -> Ordering
}

fn max[T: Ordered](a: T, b: T) -> T {
	if a.cmp(b) == .less {
		return b
	}
	return a
}
```

- Dispatch is static by default (monomorphized). The optimization profile may
  choose to share code between instantiations to save space on small targets
  ([backend.md](backend.md)).
- Dynamic dispatch is explicit: `dyn Trait` (Open: exact form).
- **Open:** trait coherence (orphan rules). Go-like "interfaces are satisfied
  implicitly" is easier to read. Rust-like explicit `impl` gives better errors
  and no accidental conformance. Leaning explicit.

## `secret` types

**Status:** Proposed

For constant-time code (crypto):

```
fn eq(a: secret[[32]u8], b: secret[[32]u8]) -> secret[bool] { ... }
```

A `secret[T]` value:
- can't be used as a branch condition, a loop bound, an array index or a
  divisor, because those leak timing
- can't be converted to a non-secret type except through an explicit
  `declassify(x)`
- taints everything computed from it

The compiler guarantees these rules at the language level, and **LatticeFoundry
must preserve them** through optimization. No pass may turn secret-dependent
data flow into control flow, and instruction selection must avoid
variable-time instructions on secrets (for example, division on some CPUs). See
[backend.md](backend.md#needed-for-the-safety-story). Prior art: FaCT, Jasmin, and the Rust
`subtle` crate (which is best-effort, not guaranteed).
