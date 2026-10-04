# Roadmap

What the compiler does next, in order. Each milestone is a usable step: it
ends with tests, docs updated to match, and nothing half-done. The design
itself is in the other documents; this one is only about order.

## Done

- **M1: Scaffold and hello world** (2026-09-29 to 10-04). Functions,
  integers, `bool`, `str`, constants, control flow, packages, `unsafe`, the
  `syscall` intrinsic, a standard library written in Lode (`std/os`,
  `std/io`), and the flow-sensitive proof checker (ranges and relations).
  Hello world: 1,049 bytes, 2 syscalls.

## Next

- **M2: Arrays, slices and proven indexing.** The core promise of
  [safety.md](safety.md#proof-obligations): `a[i]` compiles only when the
  checker proves `i < a.len`.
  - fixed-size arrays `[N]T`, array literals, element assignment
  - slices `[]T` as views (parameters and locals; an array is passed where a
    slice is expected)
  - `for i in a..b` and `for x in xs`, with the facts they give
  - lengths as terms in the fact language (`i < xs.len`)
- **M3: Structs.** Value semantics, field access and assignment, passing and
  returning by value.
- **M4: Enums, `match`, optionals.** Sum types with exhaustive `match`, and
  `?T` with `if let`, `else` and `??`.
- **M5: Errors.** `throws`, `try`, `catch`, error sets, `defer`/`errdefer`.
  `io.stdout().write` becomes the checked way to write.
- **M6: Methods and parameter conventions.** `fn T.name(self)`, `inout`,
  `sink`.
- **M7: Generics and traits** (and `comptime`, which they're built on).

Later, in no fixed order yet: refinements in signatures, the allocator
context and heap types, globals with `Atomic`/`Mutex`, stack bounds (LF
already reports stack usage), green threads, other targets through
`comptime`, `lode fmt`, and self-hosting.
