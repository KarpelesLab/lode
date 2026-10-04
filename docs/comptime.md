# Compile-time evaluation

`comptime` is the one mechanism behind generics, conditional compilation,
format strings, lookup-table generation and target queries. It follows Zig's
lead, with restrictions for predictability.

## Basics

**Status:** Proposed; implemented for constants (M7d), and for `comptime`
parameters, packs, `comptime let`, `comptime for` and `match comptime`
(M7e) ([generics.md](generics.md#m7d-in-the-compiler),
[M7e](generics.md#m7e-in-the-compiler))

- A subset of the language runs at compile time: arithmetic, control flow,
  structs, enums, arrays, and calls to functions that only use those.
- `const` declarations are always evaluated at compile time.
- `comptime` parameters are known at compile time. Generic `[T]` parameters are
  comptime type parameters constrained by traits ([types.md](types.md#generics-and-traits)).
  What M7 needs of comptime is in [generics.md](generics.md#comptime).
- In the compiler, a `comptime` parameter is an integer, a `bool` or a
  `str`, and a function with one is expanded for each value it's called
  with; `comptime let`, `comptime for` and `match comptime` run while that
  expansion is checked ([generics.md](generics.md#m7e-in-the-compiler)).

```
const CRC_TABLE: [256]u32 = make_crc_table()   // computed while compiling

fn make_crc_table() -> [256]u32 { ... }         // an ordinary function
```

## Rules for comptime code

**Status:** Proposed; implemented (M7d), without `embed_file`. Integers
are exact `i128`s within their type rather than `puremp` numbers, which
is the same while integers are at most 64 bits

- **Deterministic and hermetic.** No I/O, no clock, no environment. The only
  input from outside the program is `embed_file("path")`, which is recorded as
  a build dependency. Builds are reproducible.
- **Bounded.** Evaluation has a step budget, and exceeding it is a compile error
  with a trace. The budget can be raised per declaration.
- **Same semantics as runtime.** Integer overflow, indexing and so on follow the
  same proof rules. A failure during comptime evaluation is a compile error at
  the point of failure.
- Arithmetic is exact and host-independent (LatticeFoundry uses `puremp`), so
  cross-compiling from a 64-bit host to an 8-bit target gives the same results.

## Conditional compilation

**Status:** Decided: dead branches may be invalid; implemented (M7d), with
`target.os`, `arch`, `pointer_bits` and `endian`

```
fn page_size() -> usize {
	if comptime target.os == .linux {
		return linux.getpagesize()
	} else if comptime target.arch == .avr {
		return 256
	} else {
		compile_error("page_size: unsupported target")
	}
}
```

- The condition of `if comptime` must be known at compile time. The branches
  that aren't taken are **removed before type checking**, so they can reference
  packages or symbols that don't exist on this target.
- `target` is a compile-time value describing the build target: `arch`, `os`,
  `abi`, `endian`, `pointer_bits`, CPU features (`target.cpu.has(.avx2)`), and
  the optimization profile ([backend.md](backend.md)).
- Plain `if` on a condition that happens to be known at compile time is still
  type-checked on both sides, and the optimizer removes dead code as usual.
  Only `if comptime` allows invalid dead branches, so the intent is explicit.

### Keeping dead branches from rotting

**Status:** Proposed; implemented (M7d): `lode check --targets=...`

Zig's lazy analysis means code for other targets is never checked and quietly
breaks. Mitigations:

- Untaken branches must still **parse**.
- `lode check --targets=all` (or a listed set) type-checks the package once
  per target in one run. It's cheap because parsing and name resolution are
  shared. CI is expected to run it.

## Format strings

**Status:** Implemented (M7e), without a buffer
([generics.md](generics.md#m7e-in-the-compiler))

`print` and similar take their format string as a comptime parameter. The
format is parsed at compile time, argument types are checked against it, and
the call expands into direct writes of the pieces:

```
io.print("hello world\n")
// → one write(1, "hello world\n", 12) syscall. No formatting code is linked.

io.print("x = {}\n", x)
// → write "x = ", then x's `Format` impl (its digits in one write), then
//   write "\n": three syscalls, as there's no buffer yet

io.print("x = {}\n")
// error: this `{}` has no argument: 1 placeholder but 0 arguments
```

This is how the concept's "hello world is a single `write`" goal is met. It
also removes the whole class of format-string bugs: a placeholder without
an argument, an argument without a placeholder, an unclosed `{` and an
argument that can't be formatted are errors at the call, pointing into the
format string. The parsing is ordinary Lode in `std/io`, run at compile
time.

## Reflection

**Status:** Open

Compile-time introspection of types (fields, variants, sizes) enables
serialization, debug printing and so on without macros. Zig has it
(`@typeInfo`). Questions:
- How much, and does it break encapsulation (private fields)?
- Do we need to generate declarations (code generation), or only inspect?

Leaning: read-only reflection that respects visibility, and no macros.
