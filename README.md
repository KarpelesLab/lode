# Lode

[![CI](https://github.com/KarpelesLab/lode/actions/workflows/ci.yml/badge.svg)](https://github.com/KarpelesLab/lode/actions/workflows/ci.yml)

Lode is a programming language, in early development: the best of Rust, Zig and
Go, each pushed to its limit.

- Memory safety and data-race freedom at compile time, without lifetime
  annotations
- No undefined behavior and no hidden crash paths in safe code
- No runtime: a hello world compiles to a single `write` syscall
- Compile-time evaluation for generics, per-target code and formatting
- Green threads, channels and structured concurrency, all opt-in
- From 8-bit microcontrollers and kernels to servers and wasm

The compiler backend is [LatticeFoundry](https://github.com/KarpelesLab/latticefoundry).

The design is in [docs/](docs/README.md), starting with the
[concept](docs/concept.md).

## Status

The compiler in `src/` compiles a growing subset of the language to static
x86-64 Linux executables:

```
package main

import "std/io"

fn main() {
	io.print("hello world\n")
}
```

That program is 577 bytes and makes exactly two system calls, `write` and
`exit`. `io.print` is ordinary Lode code in [`std/`](std/), down to the
`syscall` in `std/os`. Its format string is read when compiling:

```
fn main() {
	let x: u32 = 7
	let name = "lode"
	io.print("x = {}, name = {}\n", x, name)
	io.print("{} {}\n", x)  // error: this `{}` has no argument: 2 placeholders but 1 argument
}
```

What works:

- functions, `let`/`var` (`var x: u32` assigned later),
  `if`/`while`/`loop`/`for`, `break`/`continue`, `const`
- integer types (`i8`..`i64`, `u8`..`u64`, `isize`, `usize`), `bool`, `str`,
  and `never` for functions that don't return (`fn fail() -> never`): code
  after a call to one can't be reached, and the checker verifies they don't
  return
- arrays (`[4]u8`, `[0; 16]`, `[[1, 2], [3, 4]]`) and slices (`[]u8`),
  read-only except as an `inout` parameter; an array is passed where a slice
  is expected; slicing (`a[i..j]`, `a[i..]`, `a[..j]`), proven in bounds
  with no run-time check, and `&a[i..j]` for an `inout` slice; array constants (`const DAYS: [12]u8 = [31, 28, ...]`) in
  read-only data, whose elements' range the checker knows
- structs (`struct Point { ... }`, `Point{x: 1, y: 2}`, `p.x`, `ps[i].x += 1`)
  with value semantics: `let q = p` copies, and structs and arrays are passed
  and returned by value; `==` compares structs and arrays field by field;
  fields are private to their package unless marked `pub` (`pub x: i32`),
  so a type with private fields is made and changed only by its package's
  functions ([docs/types.md](docs/types.md#structs))
- enums with payloads (`Shape.circle(p, 2)`) and C-style enums
  (`enum Color: u8 { red = 1 ... }`), exhaustive `match` (also on integers and `bool`: `0 => ...`, `1..=9 | 20 => ...`, `_ => ...`), and optionals
  `?T` with `none`, `if let`, `let ... else` and `??`; `.dot` and
  `.circle(p, 2)` where the enum is known
- errors as return values: `fn parse(s: []u8) throws(ParseError) -> u32`,
  `throw .empty`, and every call handled with `try f()`,
  `f() catch e { ... }`, `f() catch 0`, `f() catch _ {}` or `match`;
  `defer` and `errdefer` ([docs/errors.md](docs/errors.md))
- parameter conventions: `inout x: T`, `sink x: T`, `set x: T`, with
  `swap(&a, &p.x)` at the call site and exclusivity checked
  ([docs/memory.md](docs/memory.md#parameter-conventions-in-the-compiler-today))
- methods: `fn Point.length(self)`, `fn Point.scale(inout self, k: u32)`,
  `p.scale(2)`, and associated functions like `Point.origin()`, on structs
  and enums ([docs/types.md](docs/types.md#methods))
- generic functions: `fn max[T: Ordered](sink a: T, sink b: T) -> T`, over
  the built-in traits `Eq`, `Ordered`, `Copy`, `Integer`, `Unsigned` and
  `Signed`, each body checked once against its bounds; `max(a, b)` infers
  `T`, `max[u32](a, b)` writes it ([docs/generics.md](docs/generics.md#m7a-in-the-compiler))
- generic structs and enums: `struct Pair[A, B]`, `enum Either[L, R]`,
  used as `Pair[u8, bool]` or with their arguments inferred
  (`Pair{first: b, second: true}`); value parameters (`[N: usize]`) that
  size arrays, with `a[i]` proven once for every `N`; methods of generic
  types, `fn Pair[A, B].swap(self)`, which may add bounds or have their
  own parameters ([docs/generics.md](docs/generics.md#m7b-in-the-compiler))
- traits: `trait Shape { fn area(self) -> u32 ... }` with default methods,
  associated functions, types and constants, and supertraits;
  `impl Shape for Rect { ... }`, and conditional impls for generic types
  (`impl[A: Ordered] Ordered for Pair[A]`), in the trait's or the type's
  package; `impl Ordered` for structs and enums, so `slices.sort` sorts
  them; bounds on user traits (`[W: io.Writer]`), dispatched statically
  ([docs/generics.md](docs/generics.md#m7c-in-the-compiler))
- compile-time evaluation: a constant's value can call functions
  (`const CRC_TABLE: [256]u32 = make_crc_table()`), with the same
  semantics as at run time, and be a struct, an enum or an optional; an
  overflow or a bad index while computing one is an error where it
  happens; a step budget (`@comptime_budget(n)`) bounds it
- `comptime` parameters and packs: `fn print[..A: Format](comptime fmt:
  str, args: ..A)`, expanded for each format string, with `comptime let`,
  `comptime for`, `match comptime` and `compile_error("{} is odd", n)`
  run while compiling; trait methods with generic parameters of their own
  ([docs/generics.md](docs/generics.md#m7e-in-the-compiler))
- per-target code: `target` (`target.os == .linux`, `target.arch`,
  `target.pointer_bits`), `if comptime` that checks only the branch the
  target takes, in functions and among declarations, and
  `compile_error("...")`; `lode check --targets=all` checks a program for
  every target the compiler knows (only x86-64 Linux is built)
  ([docs/generics.md](docs/generics.md#m7d-in-the-compiler))
- packages: `import "std/..."`, `pub`, `pkg.name`; `std/math` (`min`,
  `max`, `clamp`, `abs`) and `std/slices` (`sort`, `is_sorted`) for any
  element type that fits; fixed-capacity containers `std/buf.StackBuf[N]`
  (bytes, whose storage isn't filled when it's made) and
  `std/vec.ArrayVec[T, N]`; `io.Writer`, implemented by files
  and buffers; `std/encoding` (UTF-8 and ASCII over bytes)
- `unsafe` blocks and functions, raw pointers (`*u8`, `s.ptr` of a string,
  array or slice), the `syscall` intrinsic, and `@uninit` fields, private
  arrays that `unsafe` code may leave unwritten in a literal
  ([docs/memory.md](docs/memory.md#uninitialized-buffers))
- output: `io.print("x = {}\n", x)` with a format string checked when
  compiling, for integers, `bool`, `str` and types with an `impl
  io.Format`, and `io.eprint` for standard error, which ignore errors
  and make one `write` per call (through a 256-byte buffer, not filled
  first);
  `io.write_fmt(&w, fmt, ...)` to any `io.Writer`, and
  `io.stdout().write(s)` and `io.stdout().write_bytes(buf)` (raw bytes),
  which throw an `os.Error`
- input: `io.stdin().read(&buf)` (the bytes it got, 0 at the end) and
  `io.stdin().read_full(&buf)` (until `buf` is full or the input ends),
  which throw an `os.Error`; `os.exit(code)` and `os.abort()` end the
  process at once
- `s.bytes()`, the bytes of a `str` as a read-only `[]u8` (sliced with
  `s.bytes()[i..j]`; a `str` itself can't be sliced yet), and returning a
  `str` literal from a function (`fn Day.name(self) -> str`)
- the proof rules from [docs/safety.md](docs/safety.md): plain
  `+ - * / % <<`, conversions like `u8(x)` and indexing `a[i]` must be proven
  safe, and so must slicing `a[i..j]`. The checker follows value ranges and
  relations between variables, struct fields and lengths through the program, narrowing on conditions, early returns and
  `for` loops, and sums of two of them: `if a > MAX - b { return none }`
  proves `a + b`, and `if v > (MAX - d) / 10 { ... }` proves `v * 10 + d`.
  `+% -% *% <<%` wrap and `+| -| *|` saturate. Every binary
  operator has an assignment form with the same rules: `x += 1`, `x +%= 1`,
  `flags |= bit`.
- refinements, which carry facts across calls and into types, at no run-time
  cost: `fn at(buf: []u8, i: usize where i < buf.len)` (the caller proves
  it, the body knows it), `-> usize where result <= buf.len` (the body
  proves it, the caller knows it), `fn last[N: usize where N > 0]`, struct
  fields that every value keeps (`head: usize where head < CAP`, `start:
  usize where start <= end`), and named refinements (`type Digit = u8
  where self <= 9`), in the checker's fact language
  ([docs/safety.md](docs/safety.md#refinements-in-types))

```
fn clamp_to_u8(x: i32) -> u8 {
	if x < 0 {
		return 0
	}
	if x > 255 {
		return 255
	}
	return u8(x) // proven: 0 <= x <= 255 here
}

fn distance(a: u64, b: u64) -> u64 {
	if a >= b {
		return a - b // proven: b <= a
	}
	return b - a // proven: a < b
}

fn count_rises(xs: []u32) -> u32 {
	var n: u32 = 0
	for i in 1..xs.len {
		if xs[i - 1] < xs[i] { // proven: 1 <= i < xs.len
			n = n +% 1
		}
	}
	return n
}
```

## Using the compiler

```sh
cargo build
target/debug/lode run program.lode        # build, run, exit with its status
target/debug/lode build program.lode -O2  # write ./program
target/debug/lode build program.lode --emit=ir
target/debug/lode build program.lode --stack-usage  # frames, worst-case stack
target/debug/lode build program.lode -g   # with debug information, for gdb
target/debug/lode check program.lode
target/debug/lode check program.lode --targets=all  # for each target (see `lode targets`)
target/debug/lode fmt program.lode        # rewrite in canonical form
target/debug/lode fmt --check std/        # list non-canonical .lode files, exit 1 if any
```

The canonical format is described in
[docs/syntax.md](docs/syntax.md#formatting).

`-g` (for `build` and `run`) adds DWARF debug information: source lines
for every function, the standard library's included, and the functions
by their Lode names. In gdb, `break main.main` (or
`break std/os.write_all`), `break program.lode:12`, `bt`, `next` and
`step` work. Variables and types aren't described yet, and at `-O1` and above
only the functions are, at their declarations: LatticeFoundry's passes
drop the instructions' lines ([docs/backend.md](docs/backend.md#debug-information)).
Without `-g` the executable is unchanged.

## Working on the compiler

`cargo test` runs unit tests, the integration tests in `tests/`, and the
programs in `tests/programs/`; each program declares its expected exit status,
standard output or errors in its first comment lines, and can give its
standard input there too (`// stdin: text`).

CI ([`.github/workflows/ci.yml`](.github/workflows/ci.yml)) runs on x86-64
Linux for every push to `master` and every pull request: `cargo fmt --check`,
`cargo clippy --all-targets -- -D warnings`, `cargo test`, and
`lode fmt --check` over `std/` and `tests/programs/` (except
`unsupported.lode`, which the parser rejects on purpose), and `lode check
--targets=x86_64-linux,aarch64-linux` over the test programs. It also builds
`tests/programs/hello_world.lode` at `-O2`, checks it prints `hello world` in
exactly two system calls, and reports its size in the job summary.

The compiler depends on released versions of
[LatticeFoundry from crates.io](https://crates.io/crates/latticefoundry). It's
updated only once the LatticeFoundry changes Lode needs are released. Lode never
builds against a local LatticeFoundry checkout.

## License

MIT. See [LICENSE](LICENSE).
