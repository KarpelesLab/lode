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

#### `never` in the compiler today

**Status:** Implemented

- `never` is only a function's return type: `fn fail(code: i32) -> never`.
  There are no values of type `never`, so it can't be the type of a
  parameter, a variable, a field or an element.
- The checker verifies that a `never` function doesn't return: it has no
  `return`, and every path through its body ends in a call to another
  `never` function or in an endless `loop` (one without `break`). It can't
  `throw` either. `os.exit` and `os.abort` are the `never` functions std
  has ([packages.md](packages.md)).
- A call to a `never` function leaves, like `return`: the code after it
  can't be reached, and it counts as leaving for "missing return", for
  joining facts after `if` and `match`
  ([safety.md](safety.md#the-fact-language)), and for blocks that must
  leave (`let ... else`, a `catch` block whose value is used). A statement
  leaves this way when the call is always evaluated in it, not only on some
  paths: `f(fail())` leaves, `a && fail()` and `opt ?? fail()` don't.
- Where a value is expected, a call to a `never` function stands for any
  type: `let v: u32 = opt ?? fail(1)`, `return fail(2)`. Without an
  expected type (`let x = fail()`), it's an error: there's no value.
- `main` may return `never`, and so may a generic function
  (`fn fail_with[T: Integer](code: T) -> never`). `never` can't be a type
  argument.
- Lowering ends each call to a `never` function with `unreachable`.

## Composite types

### Arrays and slices

- `[N]T`: fixed-size array, a value. `N` is a compile-time `usize`: a
  constant, or a value parameter of a generic declaration.
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
- `a[i..j]` is a slice of the elements `i` up to, but not including, `j`,
  of an array or a slice (`s.bytes()` too). `a[i..]` goes to the end,
  `a[..j]` starts at 0, and `a[..]` is all of them. It views the same
  storage, without a copy. It must be [proven](safety.md#the-fact-language)
  that `0 <= i <= j <= a.len`; there's no run-time check. The bounds can
  have any integer type. A slice of a `var` array follows the rule above:
  it can be passed to a function, but not kept in a local. `&a[i..j]`
  passes part of a `var` array or of an `inout` slice to an `inout` slice
  parameter ([memory.md](memory.md#parameter-conventions-in-the-compiler-today)).
  A `str` can't be sliced: use `s.bytes()[i..j]`
  ([strings.md](strings.md#in-the-compiler-today)).
- Every `a[i]` must be [proven](safety.md#the-fact-language) to be in
  bounds. The index can have any integer type.
- Arrays are passed and returned by value, like structs (see
  [Structs](#in-the-compiler-today-1)). `a == b` compares two arrays of the
  same type element by element.
- In `unsafe` code, `a.ptr` of an array or slice of integers is a raw
  pointer to its first element (`*u8` for `[N]u8` and `[]u8`). An array's
  pointer points to the array itself, not to a copy.
- An array of integers or `bool` (or of arrays of them) can be a constant:
  `const DAYS: [12]u8 = [31, 28, ...]`. Its value is any expression of
  its type, computed while compiling, calls of functions included
  ([generics.md](generics.md#m7d-in-the-compiler)). It lives in read-only data: `DAYS[i]` and `for d in DAYS` read
  it in place, and passing it where a slice is expected views it without a
  copy. `let a = DAYS` copies it into a variable that can change. The
  checker knows the range of its elements: `DAYS[i]` is `28..=31`
  ([safety.md](safety.md#the-fact-language)). A constant can't be assigned
  or passed with `&`. At most 2^24 elements.
- Not yet: returning a slice, and `a.get(i)`.

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
- **Decided:** field visibility. A field is private to the struct's
  package unless it's marked `pub`, as in Go and Rust:

  ```
  pub struct StackBuf[N: usize] {
  	@uninit bytes: [N]u8
  	start: usize
  	end: usize
  }

  pub struct Decoded[R] {
  	pub rune: R
  	pub len: usize
  }
  ```

  Outside the package, a private field can't be read, assigned or passed
  with `&`, and a struct with a private field can't be built with a
  literal: its package's functions make it (`buf.StackBuf[64].new()`).
  Inside the package, every field is visible, to methods and to any other
  function. So a type keeps its invariants with private fields and
  methods, and the checker doesn't need to know them. A field marked
  `pub let` can be read everywhere but assigned only in its package
  (decided with M8, [allocation.md](allocation.md#field-visibility)):
  `pub let len: usize` lets users read a length that only the type's
  methods change.
- `==` (derived `Eq`) compares private fields too, from any package: it
  says whether two values are equal, not what they hold. A struct with an
  `@uninit` field isn't `Eq` at all ([memory.md](memory.md#uninitialized-buffers)).
- Enum payload fields are always visible: `match` binds them. An enum
  that hides its payload wraps it in a struct with private fields.

#### In the compiler today

**Status:** Implemented subset (syntax in [syntax.md](syntax.md#structs))

- Field types: integers, `bool`, arrays, other structs, enums and
  optionals, and a generic struct's parameters. Arrays and slices of
  structs work too. Not yet: pointer fields, field defaults, structs
  without fields and `@layout`.
- Generic structs: `struct Pair[A, B] { ... }`, used as `Pair[u8, bool]`
  ([Generics](#in-the-compiler-today-5)).
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
  every field, recursively, private ones too. Every field type supported
  today has `==`, so every struct does, except one with an `@uninit`
  field. Equality is automatic for now; whether it should be
  opt-in is still Open (see [Operators](#operators)). `<` and the other
  orderings don't apply to structs.
- Field visibility as decided above: `pub name: T` is visible everywhere,
  any other field only in the struct's package. Outside it, reading,
  assigning or passing a private field is an error ("`len` is a private
  field of `buf.StackBuf`"), and so is a literal of a struct with one
  ("`buf.StackBuf` has private fields, so it can only be built in package
  `std/buf`", with a hint to a public function of that package that
  returns one, `new` first). A method of another package's trait,
  implemented in that package, sees only the `pub` fields. Generic code
  can't reach fields through a type parameter, so visibility is checked
  where the struct is named.
- `pub let name: T` is read-only outside the package: reading it works
  as for a `pub` field (its refinement is a fact there too), but
  assigning it, passing it with `&` or calling an `inout self` method on
  it is an error ("`lo` of `geo.Span` is read-only outside package
  `std/geo`"), and so is a literal of the struct ("`geo.Span` has
  read-only (`pub let`) fields, so it can only be built in package
  `std/geo`"). `let` without `pub` is a syntax error: a private field is
  already invisible outside.
- `@uninit name: [N]T`, with `T` an integer type, marks a private array
  that `unsafe` code may leave out of a literal
  ([memory.md](memory.md#uninitialized-buffers)).
- In memory, fields are laid out in declaration order with natural
  alignment (LatticeFoundry's struct layout). This is not a promise: see the
  unspecified field order above.
- Another package's public struct is `pkg.Name`, in types and in literals
  (`geo.Point{x: 1, y: 2}`, if `x` and `y` are `pub`). Using a struct
  that isn't `pub` from another package is an error.
- The proof checker knows the integer fields of struct locals
  ([safety.md](safety.md#the-fact-language)): after `if p.x < 10`, `p.x + 1`
  is proven.
- An integer field can have a refinement, `head: usize where head < CAP`
  or `start: usize where start <= end`, which every value of the struct
  keeps: literals and field assignments prove it, and reading a field knows
  it ([memory.md](memory.md#struct-invariants)).

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
- `add | sub => ...` handles several variants in one arm; such an arm
  binds no payload fields.
- `match` also works on integers and `bool` ([syntax.md](syntax.md#enums-and-match)).
- Generic enums: `enum Either[L, R] { ... }`, used as `Either[u8, bool]`
  ([Generics](#in-the-compiler-today-5)). A C-style enum can't be generic.
- Not yet: `match` as an expression, and patterns that nest
  (`some(circle(c, r))`).

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

### Refined types

**Status:** Implemented (2026-10-06)

A `type` declaration with a `where` names a refinement of an integer type
([safety.md](safety.md#refinements-in-types)):

```
type Digit = u8 where self <= 9

fn add(a: Digit, b: Digit) -> u8 {
	return a + b                     // proven: at most 18
}
```

- A refined type isn't distinct: a `Digit` is a `u8` known to be at most
  9. It's used wherever a `u8` is, and a `u8` becomes a `Digit` where the
  checker proves the refinement: an argument, a `return`, a field's value,
  `let d: Digit = c - '0'` after `if c >= '0' && c <= '9'`, or the
  conversion `Digit(x)`. Nothing happens at run time.
- It's the whole type of a parameter, a result, a struct field, or a `let`
  or `var`, and its refinement applies there as if written with `where`. A
  `var d: Digit` keeps it: every value assigned must meet it.
- For now it can't be part of another type (`[4]Digit`, `?Digit`,
  `Pair[Digit, u8]`), a payload field or a constant's type: it would lose
  its refinement, so that's an error. A `type` without `where` is the
  distinct type above, still Proposed: an error.

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
- The methods of an `impl` are methods of the type too, also in the
  trait's package ([Generics and traits](#in-the-compiler-today-5)). A call
  finds the type's own methods first.
- No extension methods.

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

**Status:** Proposed; generic functions, generic structs and enums, value
parameters, generic methods, traits and `impl` blocks are implemented
(see [In the compiler today](#in-the-compiler-today-5)). The detailed
proposal for M7 is in [generics.md](generics.md).

Generics are compile-time parameters (see [comptime.md](comptime.md)).
**Traits** constrain them so that a generic function is type-checked once, at
its definition, instead of failing deep inside an instantiation (the Zig and C++
template problem):

```
trait Ordered: Eq {
	fn cmp(self, other: Self) -> Ordering
}

fn max[T: Ordered](sink a: T, sink b: T) -> T {
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
- Traits are implemented in explicit `impl Trait for T { ... }` blocks
  (Decided, [generics.md](generics.md#decisions)). Coherence: an `impl` is
  in the trait's package or the type's, one per trait and type
  ([generics.md](generics.md#coherence)).

### In the compiler today

**Status:** Implemented subset (M7a, M7b and M7c; syntax in
[syntax.md](syntax.md#generic-functions),
[syntax.md](syntax.md#generic-types-and-value-parameters) and
[syntax.md](syntax.md#traits-and-impls))

- Generic functions: `fn max[T: Ordered](sink a: T, sink b: T) -> T`, with
  bounds from the built-in traits `Eq`, `Ordered`, `Copy`, `Integer`,
  `Unsigned` and `Signed` and from traits declared in Lode, joined with
  `+`. A generic body is checked once,
  against its bounds; the errors at a call are about its arguments.
- `Eq` gives `==` and `!=`. `Ordered` gives the methods `a.cmp(b)` (an
  `Ordering`: `less`, `equal` or `greater`, a C-style enum of `i8` -1, 0
  and 1) and `a.lt(b)`, `a.le(b)`, `a.gt(b)`, `a.ge(b)`; the integers and
  `bool` have them too. Only a numeric bound gives operators, which mean
  what they mean on the integers.
- A `T` without `Copy` is moved, never copied: keeping a read-only
  parameter or an element is an error, and a `let` or a `sink` parameter
  can't be used after its value was moved out
  ([generics.md](generics.md#copy-and-moves-in-generic-code)). Every type
  but such a `T` is `Copy`, and the arrays, optionals, structs and enums
  holding one. Keeping a field moves the whole variable out.
- Type arguments are written (`max[u32](a, b)`) or inferred from the
  arguments, then from the type expected for the result. A type argument
  can't be a view.
- Generic structs and enums: `struct Pair[A, B: Ordered]`,
  `enum Either[L, R]`. An instance is the declaration plus its arguments:
  `Pair[u8, bool]` and `Pair[u8, u16]` are two types. A type names its
  arguments (`let p: Pair[u8, bool]`); a literal or a call infers them
  like a call's type arguments (`Pair{first: b, second: true}`,
  `Either.left(x)`, `Pair.new(a, b)`). The arguments must satisfy the
  declaration's bounds. A struct or an enum can't hold any instance of
  itself by value.
- Value parameters: `[N: usize]` (any integer type) is a value known when
  compiling. `[N]T` is an array of `N` elements, and `N` is a term for the
  checker, so `for i in 0..N` proves `a[i]` once for every `N`
  ([safety.md](safety.md#values-of-a-type-parameter)). The argument is a
  constant: `StackBuf[64]`, `first_n[4](xs)`, or inferred from an array's
  length.
- Methods of a generic type name its parameters:
  `fn Pair[A, B].swap(self) -> Pair[B, A]`. They have the type's bounds,
  and can add some, `fn Pair[A: Ordered, B].min_first`, then existing
  only for the instances where they hold. A method can have parameters of
  its own: `fn Pair[A, B].with_first[C]`.
- Each set of type arguments `main` reaches makes an instance with its
  own symbol: `std/math.max[u32]`, `std/buf.StackBuf[64].push`.
- Facts about integer type parameters: [safety.md](safety.md#values-of-a-type-parameter).
- Traits: `trait Shape { fn area(self) -> u32 ... }` with required and
  default methods, associated functions (`fn unit() -> Self`), associated
  types (`type Rune: Copy`) and constants (`const MAX_LEN: usize`), and
  supertraits (`trait Counter: Named`). `impl Shape for Rect { ... }` gives
  the methods and the associated items, with the trait's signatures; a
  generic type's impl names its parameters, and may bound them:
  `impl[A: Ordered] Ordered for Pair[A]`. Structs and enums implement the
  built-in `Ordered` with `cmp`. `Eq` stays derived, `Copy` automatic,
  and the numeric traits sealed.
- An `impl` is in the trait's package or the type's, one per trait and
  type, never for a bare type parameter.
- `p.area()` finds the type's own methods, then its impls'; when two
  traits give it, `Shape.area(p)` names one. A trait's method on a type
  parameter is dispatched statically to the impl of each instance.
- A trait's method may have generic parameters of its own, which an
  impl's method declares the same way: `fn format[W: io.Writer](self,
  inout w: W)` (M7e).
- The details are in [generics.md](generics.md#m7a-in-the-compiler),
  [generics.md](generics.md#m7b-in-the-compiler),
  [generics.md](generics.md#m7c-in-the-compiler) and
  [generics.md](generics.md#m7e-in-the-compiler).
- A function's value parameters can have a refinement, `fn last[N: usize
  where N > 0]`, proven where it's called
  ([safety.md](safety.md#refinements-in-types)).
- Not yet: `dyn`, generic traits, refinements on a struct's, an enum's or
  an impl's value parameters.

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
