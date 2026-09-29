# Lode

Lode is a programming language in the design stage: the best of Rust, Zig and
Go, each pushed to its limit.

- Memory safety and data-race freedom at compile time, without lifetime
  annotations
- No undefined behavior and no hidden crash paths in safe code
- No runtime: a hello world compiles to a single `write` syscall
- Compile-time evaluation for generics, per-target code and formatting
- Green threads, channels and structured concurrency, all opt-in
- From 8-bit microcontrollers and kernels to servers and wasm

The compiler backend is [LatticeFoundry](https://github.com/KarpelesLab/latticefoundry).

There is no compiler yet. The design is in [docs/](docs/README.md), starting
with the [concept](docs/concept.md).

## License

MIT. See [LICENSE](LICENSE).
