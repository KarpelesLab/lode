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
- **M7a: Generic functions over the built-in traits** (2026-10-04).
  `fn max[T: Ordered](sink a: T, sink b: T) -> T` with the bounds `Eq`,
  `Ordered`, `Copy`, `Integer`, `Unsigned` and `Signed`; bodies checked
  once against their bounds, with facts about integer type parameters
  ([safety.md](safety.md#values-of-a-type-parameter)); a `T` without
  `Copy` moved, never copied; type arguments written (`max[u32](a, b)`)
  or inferred from the arguments and the expected type; one instance per
  set of type arguments `main` reaches (`src/mono.rs`). std gains
  `std/math` (`min`, `max`, `clamp`, `abs`), `std/slices` (`sort`,
  `is_sorted`), and `io.print_int`, which replaces `print_u64` and
  `print_i64` ([generics.md](generics.md#m7a-in-the-compiler)).
- **M7b: Generic structs and enums, value parameters, generic methods**
  (2026-10-04). `struct Pair[A, B]` and `enum Either[L, R]`, instantiated
  per arguments (`Pair[u8, bool]`), which literals and calls infer; value
  parameters (`[N: usize]`) that size arrays and are terms for the
  checker, so `[N]T` indexing is proven once for every `N`; methods that
  name the type's parameters (`fn Pair[A, B].swap`), add bounds, or have
  their own; recursive generic types rejected. std gains `std/buf`
  (`StackBuf[N]`, which `io.print_int` uses for its digits) and `std/vec`
  (`ArrayVec[T, N]`) ([generics.md](generics.md#m7b-in-the-compiler)).
- **M7d: Compile-time evaluation and target selection** (2026-10-04). A
  tree-walking evaluator runs constants' values, calls included (`const
  CRC_TABLE: [256]u32 = make_crc_table()`), with the program's semantics,
  checking what the prover didn't prove as it runs, within step and
  memory budgets (`@comptime_budget(n)`); functions a constant calls are
  checked on demand. `target` describes the target, `if comptime` picks
  declarations and statements by it, `compile_error` stops what can't be
  compiled, and `lode check --targets=...` checks for several targets in
  one run (x86_64-linux is built; aarch64-linux, wasm32, thumbv7m and avr
  are checked). `std/os` is Linux-only, with the system call numbers of
  x86-64 and AArch64 ([generics.md](generics.md#m7d-in-the-compiler)).

Alongside the milestones (2026-10-04): `lode fmt`, `lode build
--stack-usage`, CI on GitHub Actions, lowering only the functions `main`
reaches, and decimal integer output (now `io.print_int`). Hello
world is now 655 bytes, still 2 syscalls. The checker keeps facts through
loops: bounds every iteration keeps survive at the loop head, and after a
loop, the facts at its exits ([safety.md](safety.md#facts-through-loops)).
Slicing `a[i..j]` compiles only when the checker proves
`0 <= i <= j <= a.len`, and `&a[i..j]` passes part of an array to an
`inout` slice ([types.md](types.md#in-the-compiler-today)).

## Next

- **Checker: filling buffers.** A buffer must be filled before use
  (`[0; 21]`), even when only the part that's written is ever read. The
  options are in [memory.md](memory.md#uninitialized-buffers): option 3's
  type, `StackBuf[N]`, exists, and stops filling once fields can be
  private.
- **M7c and M7e: the rest of generics and traits**: user traits and
  `impl` (M7c), and format strings with `comptime` parameters (M7e). The
  proposal is in [generics.md](generics.md#implementation-plan).

Later, in no fixed order yet: refinements in signatures, the allocator
context and heap types, globals with `Atomic`/`Mutex`, the rest of stack
bounds (the bound in the binary, profiles that require one; `--stack-usage`
already reports it), green threads, building for the other targets
(`lode check` already checks for them), and self-hosting.
