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

- Each line is indented with one tab per open `{`. A line that continues a
  statement, or follows a `(` or `[` left open, gets one more tab.
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
| Function that can fail | `fn name(a: T) throws(E) -> R` |
| Generic parameters | `fn max[T: Ordered](a: T, b: T) -> T` |
| Parameter conventions | `inout x: T`, `sink x: T` ([memory.md](memory.md)) |
| Optional | `?T`, `none`, `if let v = opt { ... }` |
| Visibility | `pub` (default is package-private) |
| Method | `fn Point.length(self) -> f32`, called as `p.length()` ([types.md](types.md#methods)) |
| Refinement | `i: usize where i < buf.len` ([safety.md](safety.md#refinements-in-types)) |
| Mutable global | `static n: Atomic[u64] = Atomic.new(0)` ([memory.md](memory.md#globals)) |
| Compile-time | `comptime`, `if comptime cond { ... }` |
| Unsafe | `unsafe fn`, `unsafe { ... }` |
| Cleanup | `defer`, `errdefer` |
| Array, slice | `[4]u8`, `[]u8`, `[1, 2, 3]`, `[0; 16]`, `a[i]`, `a.len` (see below) |
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

## Open questions

- `match` arms: single expression, or a block, or both?
- Is `return` required, or is the last expression the value (as in Rust)?
  Leaning toward requiring `return` in functions and allowing the last
  expression in `match` arms and blocks used as expressions.
- Generic brackets: `[T]` (Go) avoids the `<>` parsing ambiguity. Leaning `[T]`,
  with indexing told apart by context.
