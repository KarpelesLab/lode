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

The compiler in `src/` is a scaffold. It compiles a small subset of the
language to static x86-64 Linux executables:

- functions, `let`/`var`, `if`/`while`/`loop`, `break`/`continue`
- integer types (`i8`..`i64`, `u8`..`u64`, `isize`, `usize`) and `bool`
- arithmetic with the proof rules from [docs/safety.md](docs/safety.md): plain
  `+ - * / % <<` must be proven safe from known value ranges; `+% -% *% <<%`
  wrap and `+| -|` saturate; `u8(x)` conversions must be proven to fit

There's no standard library yet (so no I/O): a program reports its result
through `main`'s return value, which becomes the exit status.

```
package main

fn fib(n: u32) -> u32 {
	if n < 2 {
		return n
	}
	return fib(n -% 1) +% fib(n -% 2)
}

fn main() -> u8 {
	return u8(fib(10))    // error: cannot prove that this `u32` value fits in `u8`
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
