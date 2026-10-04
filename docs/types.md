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

Every binary arithmetic, bitwise and shift operator `op` has an assignment
form `x op= v` (`+= -= *= /= %= +%= -%= *%= +|= -|= *|= &= |= ^= <<= <<%= >>=`).
It means `x = x op v`, with the same proof obligation, and evaluates the
place `x` once. It works on variables, fields, elements and `inout`
parameters.

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

- Element types: integers, `bool`, arrays (`[4][4]u8`) and structs. Arrays
  and slices of other types (`str`, pointers, slices) are not supported yet.
- An array is a value. `let b = a` copies the elements, and changing `a`
  afterwards doesn't change `b`. Array locals live on the stack.
- A slice is a view, a pointer and a length, like `str`. It's read-only,
  except an `inout` slice parameter, whose elements the function can assign
  (`xs[i] = v`): the caller passes `&a` for a `var` array `a`
  ([memory.md](memory.md#parameter-conventions-in-the-compiler-today)).
- An array converts to a slice of all its elements where a slice is
  expected: in a call argument, or in a `let`/`var` with a slice type. A slice
  kept in a local may only view a `let` array (or part of one), so it never
  sees the array change. This stands in for the [view rules](memory.md#views)
  until they're checked.
- Every `a[i]` must be [proven](safety.md#the-fact-language) to be in
  bounds. The index can have any integer type.
- Arrays are passed and returned by value, like structs (see
  [Structs](#in-the-compiler-today-1)). `a == b` compares two arrays of the
  same type element by element.
- In `unsafe` code, `a.ptr` of an array or slice of integers is a raw
  pointer to its first element (`*u8` for `[N]u8` and `[]u8`). An array's
  pointer points to the array itself, not to a copy.
- Not yet: returning a slice, slicing (`a[i..j]`), and `a.get(i)`.

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
- Structs are **nominal**: two struct declarations are two types, even with
  the same fields.
- A struct holds its fields by value, so it can't contain itself, directly or
  through other structs or arrays. A field can't be a view (`str`, `[]T`):
  views are never stored in structs ([memory.md](memory.md#views)).
- **Open:** field visibility. Today a struct's fields are visible wherever
  the struct is, and `pub` applies to the whole struct. Private fields (for
  types that keep an invariant) are likely to come with methods.

#### In the compiler today

**Status:** Implemented subset (syntax in [syntax.md](syntax.md#structs))

- Field types: integers, `bool`, arrays, other structs, enums and
  optionals. Arrays and slices of structs work too. Not yet: pointer fields, field defaults, structs
  without fields, generic structs and `@layout`.
- A struct is a value, like an array. `let q = p` and `q = p` copy it, and
  changing `p` afterwards doesn't change `q`. Fields of a `var` struct can be
  assigned, also nested and with `op=`: `r.min.x = 1`, `ps[i].y += 2`.
- Structs and arrays are passed and returned by value. A default parameter
  is read-only, so the callee reads the caller's value in place, without a
  copy ([memory.md](memory.md#in-the-compiler-today)). An `inout` one
  changes it in place: `mirror(&p)`, `mirror(&ps[i])`.
- Structs have methods ([Methods](#methods)): `p.length()`, `p.scale(2)`,
  `Point.origin()`.
- `a == b` and `a != b` work on two structs of the same type: they compare
  every field, recursively. Every field type supported today has `==`, so
  every struct does. Equality is automatic for now; whether it should be
  opt-in is still Open (see [Operators](#operators)). `<` and the other
  orderings don't apply to structs.
- In memory, fields are laid out in declaration order with natural
  alignment (LatticeFoundry's struct layout). This is not a promise: see the
  unspecified field order above.
- Another package's public struct is `pkg.Name`, in types and in literals
  (`geo.Point{x: 1, y: 2}`). Using a struct that isn't `pub` from another
  package is an error.
- The proof checker knows the integer fields of struct locals
  ([safety.md](safety.md#the-fact-language)): after `if p.x < 10`, `p.x + 1`
  is proven.

### Enums (sum types)

```
enum Token {
	ident(start: u32, len: u32)
	number(value: u64)
	eof
}

match tok {
	ident(s, n) => ...
	number(v) => ...
	eof => ...
}
```

- `match` must be exhaustive. `_` is allowed but linted when used on an enum
  declared in the same package (it hides new variants).
- A payload holds its fields by value, like a struct. A payload field can't
  be a view (`str`, `[]T`), for the same reason a struct field can't
  ([memory.md](memory.md#views)). So a token refers to its text by position
  (`ident(start, len)`), not with a `str`.
- C-style enums with explicit integer values:

  ```
  enum Color: u8 {
  	red = 1
  	green = 2
  }
  ```

  Converting an integer to such an enum returns `?Color`.

#### In the compiler today

**Status:** Implemented subset (syntax in [syntax.md](syntax.md#enums-and-match))

- Variants have named payload fields, or none. Payload field types are the
  struct field types: integers, `bool`, arrays, structs, enums and optionals.
  An enum can't contain itself, directly or through other types.
- `Shape.circle(p, 2)` builds a variant, with its payload fields in
  declaration order, and `Shape.dot` one without payload. Where a `Shape`
  (or a `?Shape`) is expected, `.circle(p, 2)` and `.dot` are short for
  them.
- An enum is a value, like a struct: copied by `let` and assignment, passed
  and returned by value, stored in structs and arrays.
- `a == b` compares two enums of the same type: the same variant, then the
  same payload fields. `<` and the other orderings don't apply.
- `match` is a statement. A missing variant is an error. A `_` arm on an
  enum of the same package gives a warning, which doesn't fail the build.
  So does a `_` arm that can match nothing; on another package's enum that's
  allowed, since the package may add variants.
- A C-style enum (`enum Color: u8 { red = 1 ... }`) gives every variant a
  value of its integer type, all different, and no payloads.
  `Color(x)` converts an integer `x` of any type to a `?Color`: `none` if no
  variant has that value. `u8(c)` converts back, with the usual proof: the
  checker knows a `Color` lies between its smallest and largest value.
- Another package's public enum is `pkg.Name`: `geo.Shape.circle(p, 2)`.
- The proof checker has no facts about payloads, but it keeps the facts it
  had before a `match` (or an `if let`, a `let ... else`) and joins the arms'
  facts after it, as after an `if`.
- In memory, an enum is its tag (a `u8`, or a C-style enum's integer type)
  followed by an area that fits the largest payload, aligned for it. A
  variant without payload uses only the tag. The layout is not a promise.
- Methods work on enums, C-style ones too, as on structs
  ([Methods](#methods)).
- Not yet: generic enums, `match` as an expression, `match` on integers,
  and patterns that nest (`some(circle(c, r))`) or list several variants
  (`a | b`).

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

#### In the compiler today

**Status:** Implemented subset (syntax in [syntax.md](syntax.md#optionals))

- `?T` works for every type a struct field can have: integers, `bool`,
  arrays, structs, enums and optionals (`??u8`). Not for views (`?str`,
  `?[]u8`), which can't be stored.
- `none` takes its type from the context: `let x: ?u8 = none`,
  `return none`, `o == none`. Without one, it's an error.
- A `T` converts to `?T` where a `?T` is expected: `let x: ?u8 = 5`,
  `return i`, `o == 5`.
- `if let v = o { ... } else { ... }` runs the first block with `v` bound to
  the value when `o` isn't `none`.
- `let v = o else { ... }` binds the value, or runs the block when `o` is
  `none`. The block must leave (`return`, `break` or `continue`).
- `o ?? d` is the value, or `d` when `o` is `none`. `d` is only evaluated
  then.
- `?T` is an enum with the variants `none` and `some(value: T)`, so
  `match o { some(v) => ..., none => ... }` works, and `==` compares two
  optionals.
- There's no niche yet: `?T` is a tag plus a `T`, like any enum.

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

**Status:** Decided that types have methods. The syntax is Proposed;
implemented in the compiler (see [In the compiler today](#in-the-compiler-today-4)).

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

**Decided:** no marker on the receiver. memory.md marks mutable arguments
with `&` at the call site, but `p.scale(2)` needs none: `inout self` is
visible in the declaration, and `(&p).scale(2)` or `p&.scale(2)` would be
noise on the most common kind of call. The receiver must still be a place
that can change, and it counts for exclusivity like an `&` argument.

### In the compiler today

**Status:** Implemented (syntax in [syntax.md](syntax.md#methods-and-parameter-conventions))

- `fn T.name(self, ...)`, `fn T.name(inout self, ...)` and
  `fn T.name(sink self, ...)` declare a method of the struct or enum `T`;
  `fn T.name(...)` without `self` an associated function. `self` comes
  first and has no type: it's a `T`. It can't be `set`.
- `p.name(...)` calls a method; `T.name(...)` an associated function, and
  `pkg.T.name(...)` one of another package's type. Calls chain:
  `a.b().c()`. A method that throws is called with `try` or `catch` like
  any function: `try io.stdout().write(s)`.
- The receiver of a method that takes `inout self` must be a place that can
  change, like the argument of an `&`: a `var`, a parameter the function
  may change, or a field or an element of one (`ps[i].scale(2)`), but not a
  `let` or a temporary. A default `self` can be any value, a temporary too.
- Methods are declared only in the package that declares `T`. A method
  can't have the name of one of the type's fields or variants (so `T.dot`
  is always a variant and `p.x` always a field), or of another method:
  each is an error at the declaration.
- `pub fn T.name` makes it usable from other packages. Without `pub`, it's
  private to its package, like a function.
- Calling a method on the type (`Point.length(p)`) is not supported; call
  it on the value.
- A method is a function with `self` as its first parameter. Its linker
  symbol is `<package path>.<T>.<name>` (`std/io.File.write`).
- No extension methods and no traits yet (M7).

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

**Status:** Proposed. The detailed proposal for M7 is in
[generics.md](generics.md).

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
[backend.md](backend.md#available-in-lf-002). Prior art: FaCT, Jasmin, and the Rust
`subtle` crate (which is best-effort, not guaranteed).
