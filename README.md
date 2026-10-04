# Lode

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

That program is 1,049 bytes and makes exactly two system calls, `write` and
`exit`. `io.print` is ordinary Lode code in [`std/`](std/), down to the
`syscall` in `std/os`.

What works:

- functions, `let`/`var`, `if`/`while`/`loop`, `break`/`continue`, `const`
- integer types (`i8`..`i64`, `u8`..`u64`, `isize`, `usize`), `bool`, `str`
- packages: `import "std/..."`, `pub`, `pkg.name`
- `unsafe` blocks and functions, raw pointers (`*u8`), the `syscall`
  intrinsic
- the proof rules from [docs/safety.md](docs/safety.md): plain
  `+ - * / % <<` and conversions like `u8(x)` must be proven safe. The checker
  follows value ranges and relations between variables through the program,
  narrowing on conditions and early returns. `+% -% *% <<%` wrap and `+| -|`
  saturate.

```
fn clamp_to_u8(x: i32) -> u8 {
	if x < 0 {
		return 0
	}
	if x > 255 {
		return 255
	}
	return u8(x)          // proven: 0 <= x <= 255 here
}

fn distance(a: u64, b: u64) -> u64 {
	if a >= b {
		return a - b      // proven: b <= a
	}
	return b - a          // proven: a < b
}
```

## Using the compiler

```sh
cargo build
target/debug/lode run program.lode        # build, run, exit with its status
target/debug/lode build program.lode -O2  # write ./program
target/debug/lode build program.lode --emit=ir
target/debug/lode check program.lode
```

## Working on the compiler

`cargo test` runs unit tests and the programs in `tests/programs/`; each one
declares its expected exit status or errors in its first comment lines.

The compiler depends on released versions of
[LatticeFoundry from crates.io](https://crates.io/crates/latticefoundry). It's
updated only once the LatticeFoundry changes Lode needs are released. Lode never
builds against a local LatticeFoundry checkout.

## License

MIT. See [LICENSE](LICENSE).
