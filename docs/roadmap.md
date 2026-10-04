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
- **M5: Errors** (2026-10-04). `throws(E)` with an enum of errors, `try`,
  `catch` (a block, a fallback value, or `_`), `match` on `ok` and `err`,
  `throw`, `defer` and `errdefer`, and the `.variant` short form wherever
  an enum is expected. An unhandled call is an error. A result is an enum
  in the caller's storage: no unwinding. `io.write` is the checked way to
  write, throwing an `os.Error`. Not yet: inferred error sets, conversion
  between error sets, error return traces
  ([errors.md](errors.md#in-the-compiler-today)).
- **M6: Methods and parameter conventions** (2026-10-04). `inout`, `sink`
  and `set` parameters, passed with `&x` (or `&p.x`, `&a[i]`), with the
  exclusivity rule checked per expression; `inout` slices whose elements
  the callee assigns (an in-place sort); `var x: T` assigned later, with
  definite assignment. Methods (`fn T.name(self)`, `inout self`,
  `sink self`) and associated functions (`T.new()`) on structs and enums,
  declared in the type's package. `io.write(fd, s)` became
  `io.stdout().write(s)`, a method of `io.File`
  ([memory.md](memory.md#parameter-conventions-in-the-compiler-today),
  [types.md](types.md#methods)).

Alongside the milestones (2026-10-04): `lode fmt`, `lode build
--stack-usage`, CI on GitHub Actions, lowering only the functions `main`
reaches, and decimal integer output (`io.print_u64`, `io.print_i64`). Hello
world is now 655 bytes, still 2 syscalls. The checker keeps facts through
loops: bounds every iteration keeps survive at the loop head, and after a
loop, the facts at its exits ([safety.md](safety.md#facts-through-loops)).
Slicing `a[i..j]` compiles only when the checker proves
`0 <= i <= j <= a.len`, and `&a[i..j]` passes part of an array to an
`inout` slice ([types.md](types.md#in-the-compiler-today)).

## Next

- **Checker: filling buffers.** A buffer must be filled before use
  (`[0; 21]`), even when only the part that's written is ever read. The
  options are in [memory.md](memory.md#uninitialized-buffers); the choice is
  open.
- **M7: Generics and traits** (and `comptime`, which they're built on).
  The proposal, split into steps M7a to M7e, is in
  [generics.md](generics.md#implementation-plan).

Later, in no fixed order yet: refinements in signatures, the allocator
context and heap types, globals with `Atomic`/`Mutex`, the rest of stack
bounds (the bound in the binary, profiles that require one; `--stack-usage`
already reports it), green threads, other targets through `comptime`, and
self-hosting.
