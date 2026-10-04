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
- **M2: Arrays, slices and proven indexing** (2026-10-04). Arrays `[N]T`,
  read-only slices `[]T`, `for` over ranges and elements, and `a[i]` that
  compiles only when the checker proves it in bounds, with lengths as terms
  in the fact language (`i < xs.len`).
- **M3: Structs** (2026-10-04). Nominal structs with value semantics: literals,
  field access and assignment, passing and returning structs and arrays by
  value, derived `==`, and fields of struct locals as terms in the fact
  language.
- **M4: Enums, `match`, optionals** (2026-10-04). Sum types with payloads,
  C-style enums with values, exhaustive `match` (the first warning: `_` over
  an enum of the same package), and `?T` with `none`, `if let`,
  `let ... else` and `??`. Enums and optionals are values in memory, like
  structs, with derived `==`.

Alongside the milestones (2026-10-04): `lode fmt`, `lode build
--stack-usage`, CI on GitHub Actions, lowering only the functions `main`
reaches, and decimal integer output (`io.print_u64`, `io.print_i64`). Hello
world is now 655 bytes, still 2 syscalls. The checker keeps facts through
loops: bounds every iteration keeps survive at the loop head, and after a
loop, the facts at its exits ([safety.md](safety.md#facts-through-loops)).

## Next

- **Checker: filling buffers.** A buffer must be filled before use
  (`[0; 21]`), even when only the part that's written is ever read. The
  options are in [memory.md](memory.md#uninitialized-buffers); the choice is
  open.
- **M5: Errors.** `throws`, `try`, `catch`, error sets, `defer`/`errdefer`.
  `io.stdout().write` becomes the checked way to write.
- **M6: Methods and parameter conventions.** `fn T.name(self)`, `inout`,
  `sink`.
- **M7: Generics and traits** (and `comptime`, which they're built on).

Later, in no fixed order yet: refinements in signatures, the allocator
context and heap types, globals with `Atomic`/`Mutex`, the rest of stack
bounds (the bound in the binary, profiles that require one; `--stack-usage`
already reports it), green threads, other targets through `comptime`, and
self-hosting.
