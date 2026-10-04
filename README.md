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

That program is 655 bytes and makes exactly two system calls, `write` and
`exit`. `io.print` is ordinary Lode code in [`std/`](std/), down to the
`syscall` in `std/os`.

What works:

- functions, `let`/`var` (`var x: u32` assigned later),
  `if`/`while`/`loop`/`for`, `break`/`continue`, `const`
- integer types (`i8`..`i64`, `u8`..`u64`, `isize`, `usize`), `bool`, `str`
- arrays (`[4]u8`, `[0; 16]`, `[[1, 2], [3, 4]]`) and slices (`[]u8`),
  read-only except as an `inout` parameter; an array is passed where a slice
  is expected; array constants (`const DAYS: [12]u8 = [31, 28, ...]`) in
  read-only data, whose elements' range the checker knows
- structs (`struct Point { ... }`, `Point{x: 1, y: 2}`, `p.x`, `ps[i].x += 1`)
  with value semantics: `let q = p` copies, and structs and arrays are passed
  and returned by value; `==` compares structs and arrays field by field
- enums with payloads (`Shape.circle(p, 2)`) and C-style enums
  (`enum Color: u8 { red = 1 ... }`), exhaustive `match`, and optionals
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
- packages: `import "std/..."`, `pub`, `pkg.name`
- `unsafe` blocks and functions, raw pointers (`*u8`, `s.ptr` of a string,
  array or slice), the `syscall` intrinsic
- output: `io.print` for strings, `io.print_u64` and `io.print_i64` for
  integers (and `io.eprint...` for standard error), which ignore errors, and
  `io.stdout().write(s)`, which throws an `os.Error`
- the proof rules from [docs/safety.md](docs/safety.md): plain
  `+ - * / % <<`, conversions like `u8(x)` and indexing `a[i]` must be proven
  safe. The checker follows value ranges and relations between variables,
  struct fields and lengths through the program, narrowing on conditions, early returns and
  `for` loops. `+% -% *% <<%` wrap and `+| -| *|` saturate. Every binary
  operator has an assignment form with the same rules: `x += 1`, `x +%= 1`,
  `flags |= bit`.

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
target/debug/lode check program.lode
target/debug/lode fmt program.lode        # rewrite in canonical form
target/debug/lode fmt --check std/        # list non-canonical .lode files, exit 1 if any
```

The canonical format is described in
[docs/syntax.md](docs/syntax.md#formatting).

## Working on the compiler

`cargo test` runs unit tests, the integration tests in `tests/`, and the
programs in `tests/programs/`; each program declares its expected exit status,
standard output or errors in its first comment lines.

CI ([`.github/workflows/ci.yml`](.github/workflows/ci.yml)) runs on x86-64
Linux for every push to `master` and every pull request: `cargo fmt --check`,
`cargo clippy --all-targets -- -D warnings`, `cargo test`, and
`lode fmt --check` over `std/` and `tests/programs/` (except
`unsupported.lode`, which the parser rejects on purpose). It also builds
`tests/programs/hello_world.lode` at `-O2`, checks it prints `hello world` in
exactly two system calls, and reports its size in the job summary.

The compiler depends on released versions of
[LatticeFoundry from crates.io](https://crates.io/crates/latticefoundry). It's
updated only once the LatticeFoundry changes Lode needs are released. Lode never
builds against a local LatticeFoundry checkout.

## License

MIT. See [LICENSE](LICENSE).
