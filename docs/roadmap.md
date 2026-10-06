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
- **M7c: Traits and `impl` blocks** (2026-10-05). `trait` declarations
  with required and default methods, associated functions, types and
  constants, and supertraits; `impl Trait for Type { ... }` for structs,
  enums and primitives, conditional ones for generic types
  (`impl[A: Ordered] Ordered for Pair[A]`), in the trait's or the type's
  package, one per trait and type; `impl Ordered` for structs and enums,
  so `slices.sort` sorts them. Bounds name user traits, generic bodies
  call their methods, and calls are dispatched statically, at run time and
  at compile time. std gains `io.Writer`, implemented by `io.File` and
  `buf.StackBuf[N]`, and `std/encoding` (the `Encoding` trait, `Utf8`,
  `Ascii`) ([generics.md](generics.md#m7c-in-the-compiler)).
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
- **M7e: Format strings** (2026-10-05). `io.print("x = {}\n", x)`: the
  format string is a `comptime` parameter, read when compiling by ordinary
  Lode in `std/io`, and the arguments a pack (`[..A: Format]`, `args:
  ..A`), each written by its `io.Format` impl. A placeholder without an
  argument, an argument without a placeholder, a brace alone or an
  argument that isn't `Format` is an error at the call, pointing into the
  format string. The language gains `comptime` parameters, packs,
  `comptime let`, `comptime for`, `match comptime`, `compile_error` with
  values and `compile_error_at`, and trait methods with generic
  parameters of their own. `io.print_int` is gone: `io.print("{}", n)`,
  and `io.print("{}", s)` for a `str` known only at run time
  ([generics.md](generics.md#m7e-in-the-compiler)). That ends M7:
  generics, traits and compile-time code.

Alongside the milestones (2026-10-04): `lode fmt`, `lode build
--stack-usage`, CI on GitHub Actions, lowering only the functions `main`
reaches, and decimal integer output (`io.print_int`, then `{}`). After
optimizing (2026-10-05), the blocks inlining leaves are merged and the
functions it leaves without callers are dropped: hello world is now 577
bytes, still 2 syscalls, and the test programs 27% smaller. The checker
keeps facts through loops: bounds every iteration keeps survive at the
loop head, and after a loop, the facts at its exits
([safety.md](safety.md#facts-through-loops)).
Slicing `a[i..j]` compiles only when the checker proves
`0 <= i <= j <= a.len`, and `&a[i..j]` passes part of an array to an
`inout` slice ([types.md](types.md#in-the-compiler-today)).

**Refinements** (2026-10-06): facts in signatures and types, in the
checker's fact language ([safety.md](safety.md#refinements-in-types)).
Parameters (`i: usize where i < buf.len`, proven by callers, known in the
body), results (`-> usize where result <= buf.len`, proven at each
`return`, known by callers), a function's value parameters (`[N: usize
where N > 0]`), struct fields, which every value of the struct keeps (a
first form of invariants, [memory.md](memory.md#struct-invariants)), and
named refinements (`type Digit = u8 where self <= 9`). In compile-time
code, what isn't proven is checked as it runs. std uses them: `File.read`
returns `n where result <= buf.len`, and `StackBuf`, `ArrayVec` and
`print`'s buffer keep their bounds without checking them again (64 bytes
less in every program that prints).

**M8a: Resource types, destruction and moves** (2026-10-06,
[allocation.md](allocation.md#m8a-in-the-compiler)). `fn T.deinit(sink
self)` runs at every exit of a value's scope, in reverse order and
interleaved with `defer`; a type with one isn't `Copy`, and every value
that isn't `Copy` moves, with use-after-move errors on every path and drop
flags for the variables moved on some paths. Pattern bindings read in
place, temporaries are destroyed at the end of their statement, and a
`defer` may move a variable. `Clone` and `x.clone()`, `pub let` fields,
and in std: `std/mem`, `os.Fd` (closed by its `deinit`), `os.open`,
`os.close`, and `ArrayVec` of any type. Code without resource types is
unchanged: hello world is still 577 bytes and two system calls.

**M8b: The allocator context, the root allocator and `Box`** (2026-10-06,
[allocation.md](allocation.md#m8b-in-the-compiler)). `uses alloc` on
functions and trait methods, checked at every call; `with alloc = h { }`
in them; handles of the root and of any allocator. With no allocator but
the root, the context costs nothing (no hidden parameter, zero-sized
handles); otherwise `uses alloc` functions take the handle in context, and
calls through a handle are dispatched over the program's allocator types.
Raw pointers to any type, as fields, with `read`, `write`, `destroy`,
`cast` and `addr`; `size_of` and `align_of`; `unsafe trait` and `unsafe
impl`; `static` globals in `unsafe` code; `AllocError` built in, and
`Clone` that may allocate. std gains `os.mmap`, `munmap`, `mremap` and
`os.PageAllocator`, and `std/alloc`: `Allocator`, `Handle`, `Heap` (size
classes, the root) and `Box[T]`, with `b.value` as a place and chains
destroyed by a loop. M8a's two leaks are gone: a value built into an
aggregate before a failed `try`, and a `set` parameter assigned before a
`throw`, are destroyed once. Programs that don't allocate are unchanged:
hello world is still 577 bytes and two system calls.

## Next

- **M8: Allocation and heap types** (decided 2026-10-06 as the milestone
  after refinements). The proposal is [allocation.md](allocation.md), in
  four steps: M8a, resource types, `deinit` and moves for every type, and
  field visibility (done); M8b, `uses alloc`, `with`, the root allocator
  and `Box[T]` (done); M8c, views returned from functions (rule 2 of
  [memory.md](memory.md#views)), `List[T]`, `String` and `mem.view`; M8d,
  error-set unions, the `oom` policy, arenas and counted allocators (which
  make `alloc.handle` safe). The prelude (`Box` without an import) is
  decided, not placed yet. Its open questions are in
  [allocation.md](allocation.md#7-decisions).
- **Checker: filling buffers.** A plain array must be filled before use
  (`[0; 21]`), even when only the part that's written is ever read.
  `StackBuf[N]`, option 3 of
  [memory.md](memory.md#uninitialized-buffers), doesn't fill its storage
  (private fields and an `@uninit` field). Option 2, for plain arrays, may
  come later.
- **After M7**, in the order of [generics.md](generics.md#after-m7), with
  the allocator context moved first as M8: `dyn Trait`; `Send`/`Sync` with
  the concurrency work; `Str[E]`; error-set unions with generic errors
  (M8d brings explicit unions); code sharing for small targets; reflection
  (a derived `Format`). Format specs (`{:x}`, widths) come with `Format`'s
  next step. `print` makes one `write` per call since 2026-10-06.

Later, in no fixed order yet: refinements inside other types (`[N]Digit`,
`?Digit`) and on a struct's value parameters, globals with
`Atomic`/`Mutex`, the rest of stack bounds (the bound in the binary,
profiles that require one; `--stack-usage` already reports it), green
threads, building for the other targets (`lode check` already checks for
them), and self-hosting.
