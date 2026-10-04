# Syntax

**Everything in this file is Provisional.** It exists so the other documents can
show examples in one consistent style. The syntax will change once the semantics
settle.

## Guiding rules

- Readability first. Read top to bottom without backtracking. Keywords are
  preferred over sigils when a sigil would be the only clue to the meaning.
- One obvious way to write a construct.
- No hidden control flow: no user-defined operator overloading, no implicit
  conversions that can fail, no property getters that allocate.

## Lexical

**Status:** Proposed

- Source files are UTF-8. The extension is `.lode`.
- Statements end at a newline. There are no semicolons.
- Indentation is **tabs** (Decided). Alignment inside a line uses spaces.
- Comments: `//` for a line, `///` for doc comments. There are no block
  comments, so commented-out code can't nest badly.
- Integer literals: `123`, `0x7f`, `0o17`, `0b1010`, with `_` separators
  (`1_000_000`).
- String literals: `"..."` (UTF-8, see [strings.md](strings.md)) and raw
  strings (syntax Open).

## Formatting

**Status:** Decided: enforced, tabs

There is a single canonical format, produced by `lode fmt`, which is part of
the compiler and not a separate tool.

`lode fmt <files or directories>` rewrites files in place. Directories are
searched for `.lode` files. `lode fmt --check` changes nothing: it lists the
files that aren't canonical and exits with status 1 if there are any (for CI).
A file that doesn't lex or parse is left unchanged, with its errors.

The canonical form:

- Each line is indented with one tab per block level. A block's body is one
  tab deeper than the line that starts its header (even when the header spans
  several lines), and its `}` lines up with that line.
- A line that continues a statement gets one more tab. Inside a `(` or `[`
  left open, that extra tab is given once, not once per line (as in gofmt).
- Inside a line, tokens are separated by one space, except:
  - none after `(`, `[` and `.`, and none before `)`, `]`, `,`, `:` and `.`
  - none around `..`: `0..n`
  - none after a unary operator: `-x`, `!ok`, `*u8`
  - none before a call's `(` or an index's `[`: `f(x)`, `a[i]`
  - none inside a type prefix: `[4]u8`, `[]*u8`
- One statement per line. A `;` between statements becomes a line break, and
  a block written on one line (`if a { return 1 }`) is split into lines.
- `else` goes on the line of the `}` before it: `} else {`.
- A `{` glued to a name, as in `Point{x: 1}`, is a literal and keeps its
  lines. After `if`, `while`, `for`, `fn` and the like, `{` always starts a
  block.
- Blank lines between statements and items are kept, at most one in a row.
  There are none at the start or end of a block or file.
- `package` comes first. One blank line follows it, and one follows the
  imports.
- Comments stay where they are. Trailing comments on consecutive lines at the
  same indentation are aligned with spaces.
- No trailing whitespace, and the file ends with exactly one newline.

The formatter works on tokens, not on the syntax tree, so comments are kept and
most new syntax needs no formatter changes. It only changes whitespace: it
lexes its own output again and leaves the file alone if the tokens or comments
differ.

**Open:** how "enforced" should it be?
- **A.** `build` warns on non-canonical files and `build --strict` (CI) rejects
  them.
- **B.** `build` always rejects non-canonical files.

Leaning **A**. B makes quick experiments painful.

## Sketch

```
package main

import "std/io"

/// A point in 2D space.
struct Point {
	x: f32
	y: f32
}

enum Shape {
	circle(center: Point, radius: f32)
	rect(min: Point, max: Point)
}

fn area(s: Shape) -> f32 {
	match s {
		circle(_, r) => return 3.14159 * r * r
		rect(a, b) => return (b.x - a.x) * (b.y - a.y)
	}
}

fn main() {
	let s = Shape.circle(Point{x: 0, y: 0}, 2)
	io.print("area: {}\n", area(s))
}
```

## Constructs used across the docs

| Construct | Provisional form |
| --- | --- |
| Immutable binding | `let x = 5` |
| Mutable binding | `var x: u32 = 0` |
| Function | `fn name(a: T, b: U) -> R { ... }` |
| Function that can fail | `fn name(a: T) throws(E) -> R`, `try f()`, `f() catch e { ... }` (see below) |
| Generic parameters | `fn max[T: Ordered](a: T, b: T) -> T` |
| Parameter conventions | `inout x: T`, `sink x: T`, `set x: T`, passed `f(&x)` (see below) |
| Optional | `?T`, `none`, `if let v = opt { ... }` |
| Visibility | `pub` (default is package-private) |
| Method | `fn Point.length(self) -> f32`, called as `p.length()` (see below) |
| Refinement | `i: usize where i < buf.len` ([safety.md](safety.md#refinements-in-types)) |
| Mutable global | `static n: Atomic[u64] = Atomic.new(0)` ([memory.md](memory.md#globals)) |
| Compile-time | `comptime`, `if comptime cond { ... }` |
| Unsafe | `unsafe fn`, `unsafe { ... }` |
| Cleanup | `defer`, `errdefer` |
| Array, slice | `[4]u8`, `[]u8`, `[1, 2, 3]`, `[0; 16]`, `a[i]`, `a.len` (see below) |
| Struct | `struct Point { x: u32 ... }`, `Point{x: 1, y: 2}`, `p.x` (see below) |
| Enum | `enum Shape { circle(c: Point, r: u32) ... }`, `Shape.circle(p, 2)`, `match s { ... }` (see below) |
| Loop over a range or elements | `for i in 0..n { ... }`, `for x in xs { ... }` |

## Arrays, slices and `for`

**Status:** Proposed; implemented in the compiler

```
const N = 4

fn sum(xs: []u32) -> u32 {
	var total: u32 = 0
	for x in xs {
		total = total +% x
	}
	return total
}

fn main() -> u32 {
	var grid: [N][N]u8 = [[0; N]; N]
	for i in 0..N {
		grid[i][i] = 1
	}
	let primes: [4]u32 = [2, 3, 5, 7]
	return sum(primes)
}
```

- `[N]T` is an array of `N` elements of type `T`. `N` is a constant: an
  integer literal or a `const`. `[N][M]T` is an array of `N` rows, each a
  `[M]T`, so `grid[i][j]` is row `i`, column `j` (as in Go).
- `[]T` is a slice of `T`.
- `[a, b, c]` is an array literal. Its element type comes from the context
  (`let a: [3]u8 = [1, 2, 3]`), or else from its first element that has a
  type of its own (`[1, x, 2]` with `x: u32` is a `[3]u32`).
- `[v; N]` repeats one value `N` times. `N` is a constant.
- `a[i]` is an element. `a[i] = v` and `a[i][j] op= v` assign to an element
  of a `var` array.
- `a.len` is the length: a `usize`, and for an array its constant `N`.
- `for i in a..b { ... }` runs the body for each integer from `a` up to, but
  not including, `b`. Both bounds are evaluated once, before the loop. When
  both are untyped (literals or untyped constants), they're `usize`, because
  ranges are mostly for indexing.
- `for x in xs { ... }` runs the body for each element of an array or slice.
  `xs` is evaluated once, before the loop: if the body assigns to an array
  `xs`, the loop still goes over the elements it had when it started.
- The loop variable is immutable. `break` and `continue` work as in `while`.

## Structs

**Status:** Proposed; implemented in the compiler

```
struct Point {
	x: i32
	y: i32
}

pub struct Rect {
	min: Point
	max: Point
}

fn width(r: Rect) -> i32 {
	return r.max.x -% r.min.x
}

fn main() -> i32 {
	var r = Rect{
		min: Point{x: 0, y: 0},
		max: Point{x: 4, y: 3},
	}
	r.max.x += 1
	if r.min == (Point{x: 0, y: 0}) {
		return width(r)
	}
	return 0
}
```

- A declaration lists one field per line, `name: Type`. `pub struct` makes
  the struct usable from other packages.
- `Name{field: value, ...}` is a literal. Every field is given exactly once,
  in any order. The values are evaluated in the order they're written. A
  literal can span lines, with a comma after each field, the last one too.
- `pkg.Name` is another package's struct, in a type or a literal:
  `geo.Point{x: 1, y: 2}`.
- `p.x` is a field. `p.x = v` and `p.a.b op= v` assign to a field of a `var`
  struct; fields and indexes mix: `ps[i].x`, `p.steps[i]`.
- In the header of `if`, `while` and `for`, a `{` after a name starts the
  block, as in Go. A struct literal there goes in parentheses:
  `if p == (Point{x: 0, y: 0}) {`.

## Enums and `match`

**Status:** Proposed; implemented in the compiler

```
enum Shape {
	circle(center: Point, radius: u32)
	rect(min: Point, max: Point)
	dot
}

enum Color: u8 {
	red = 1
	green = 2
}

fn radius(s: Shape) -> u32 {
	match s {
		circle(_, r) => return r
		rect(a, b) => {
			let w = b.x -% a.x
			return w / 2
		}
		dot => return 0
	}
}

fn main() -> u32 {
	let s = Shape.circle(Point{x: 0, y: 0}, 2)
	let c = Color(1) ?? Color.green
	return radius(s) +% u32(c)
}
```

- A declaration lists one variant per line: a name, and its payload fields
  in parentheses, `name: Type`, as in a struct. `pub enum` makes the enum
  usable from other packages.
- `Name: T` after the enum's name gives it an integer type, and each variant
  a value: `red = 1`. Such variants have no payload.
- `E.variant(a, b)` builds a value, with the payload fields in declaration
  order, like the arguments of a call. A variant without payload is
  `E.variant`, without parentheses. `pkg.E.variant(...)` for another
  package's enum.
- Where the context expects an enum `E` (or a `?E`), `.variant` and
  `.variant(a, b)` are short for `E.variant` and `E.variant(a, b)`:
  `let s: Shape = .dot`, `area(.circle(p, 2))`, `return .dot`,
  `s == .dot`, `throw .empty`. Without such a context, it's an error.
- `E(x)` converts an integer to a C-style enum, as an optional. `u8(c)`
  converts one to an integer.
- `match value { ... }` has one arm per line: a pattern, `=>`, then a block,
  or a single statement on the same line (`dot => return 0`).
- A pattern is a variant's name. `name(a, b)` binds its payload fields by
  position; `_` skips one. A variant with a payload can be matched by its
  name alone, ignoring the payload. `_` matches every variant no earlier
  arm matched.
- `match` is a statement. Using it as an expression (each arm's value) is
  still Open.

## Optionals

**Status:** Proposed; implemented in the compiler

```
fn find(xs: []u32, v: u32) -> ?usize {
	for i in 0..xs.len {
		if xs[i] == v {
			return i
		}
	}
	return none
}

fn main() -> usize {
	let xs: [3]u32 = [4, 5, 6]
	if let i = find(xs, 5) {
		return i
	}
	let j = find(xs, 6) else {
		return 1
	}
	return find(xs, 7) ?? j
}
```

- `?T` is an optional `T`; `??T` is an optional of an optional.
- `if let name = opt { ... }` runs the block when `opt` isn't `none`, with
  `name` bound to the value. It can have `else` and `else if`.
- `let name = opt else { ... }` and `var name = opt else { ... }` bind the
  value, or run the block, which must leave.
- `a ?? b` binds tighter than comparisons and looser than arithmetic, and
  groups to the right: `a ?? b ?? c` is `a ?? (b ?? c)`, and
  `x ?? 0 == 1` compares `x ?? 0`.

## Errors

**Status:** Proposed; implemented in the compiler (semantics in
[errors.md](errors.md#in-the-compiler-today))

```
enum ParseError {
	empty
	invalid_digit(pos: usize)
}

fn parse(s: []u8) throws(ParseError) -> u32 {
	if s.len == 0 {
		throw .empty
	}
	defer cleanup()
	errdefer log_failure()
	...
}

fn sum(a: []u8, b: []u8) throws(ParseError) -> u32 {
	return (try parse(a)) +% (try parse(b))
}

fn main() -> u32 {
	let n = parse(input) catch e {
		return 1
	}
	let m = parse(other) catch 0
	parse(input) catch _ {}
	match parse(input) {
		ok(v) => return v
		err(e) => return 2
	}
}
```

- `throws(E)` comes after the parameters and before `-> T`.
- `try call` applies to the call that follows it: `try f() + 1` adds 1 to
  the value.
- `call catch name { ... }`, `call catch _ { ... }`, `call catch value`.
  `catch` binds like `??`: tighter than comparisons, looser than
  arithmetic, grouping to the right. After `catch`, a `{` following a
  name starts the block; a struct literal fallback goes in parentheses,
  `catch (Point{x: 0, y: 0})`.
- `throw value` is a statement. In an expression, it can only follow
  `??`: `opt ?? throw .missing`.
- `defer` and `errdefer` take a block, or one statement on the same line.

## Methods and parameter conventions

**Status:** Proposed; implemented in the compiler (semantics in
[memory.md](memory.md#parameter-conventions-in-the-compiler-today) and
[types.md](types.md#in-the-compiler-today-4))

```
struct Point {
	x: u32
	y: u32
}

fn Point.origin() -> Point {
	return Point{x: 0, y: 0}
}

fn Point.sum(self) -> u32 {
	return self.x +% self.y
}

fn Point.scale(inout self, k: u32) {
	self.x = self.x *% k
	self.y = self.y *% k
}

fn swap(inout a: u32, inout b: u32) {
	let t = a
	a = b
	b = t
}

fn split(v: u32, set hi: u32, set lo: u32) {
	hi = v / 10
	lo = v % 10
}

fn main() -> u32 {
	var p = Point.origin()
	p.x = 2
	p.scale(3)
	swap(&p.x, &p.y)
	var hi: u32
	var lo: u32
	split(42, &hi, &lo)
	return p.sum() +% hi +% lo
}
```

- A parameter is `name: T`, or with a convention first: `inout name: T`,
  `sink name: T`, `set name: T`.
- `&place` passes an argument to an `inout` or `set` parameter: `&x`,
  `&p.x`, `&a[i]`. It's only allowed there. The `&` is provisional
  ([memory.md](memory.md#chosen-direction-mutable-value-semantics)).
- `fn Type.name(...)` declares a method or an associated function of
  `Type`. A method's first parameter is `self`, `inout self` or
  `sink self`, without a type.
- `value.name(...)` calls a method, with no marker on the receiver, even
  for `inout self`. `Type.name(...)` calls an associated function, and
  `pkg.Type.name(...)` one of another package.
- `var name: T` without a value declares a variable to assign later.

- `match` arms: a block or a single statement now. Should an arm also be a
  single expression, once `match` can be an expression?
- Is `return` required, or is the last expression the value (as in Rust)?
  Leaning toward requiring `return` in functions and allowing the last
  expression in `match` arms and blocks used as expressions.
- Generic brackets: `[T]` (Go) avoids the `<>` parsing ambiguity. Leaning `[T]`,
  with indexing told apart by context.
- The `&` that marks an `inout` or `set` argument: `&x` is familiar from C
  and Rust, but there it takes an address, which Lode code never does. A
  keyword (`f(inout x)`, as in C#'s `ref x`) would read better and say which
  convention it is.
