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

## Open questions

- `match` arms: single expression, or a block, or both?
- Is `return` required, or is the last expression the value (as in Rust)?
  Leaning toward requiring `return` in functions and allowing the last
  expression in `match` arms and blocks used as expressions.
- Generic brackets: `[T]` (Go) avoids the `<>` parsing ambiguity. Leaning `[T]`,
  with indexing told apart by context.
