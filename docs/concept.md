# Lode — Concept

New programming language, yet another.

## Name

**Status:** Decided

**Lode**: a vein of metal ore in rock, as in "the mother lode". It keeps the
metallurgy theme of its backend, LatticeFoundry (Rust itself is named after
iron oxide).

- Command: `lode` (`lode build`, `lode fmt`, `lode check`)
- Source file extension: `.lode` (`.lo` is taken by libtool objects)
- Repository: [github.com/KarpelesLab/lode](https://github.com/KarpelesLab/lode)

## Positioning

**Status:** Decided

**The best of Rust, Zig and Go, each pushed to its limit.**

Each of these languages gets something important right, and each stops short
of taking it all the way. Lode takes the idea and takes it further.

| From | We take | Where it stops short | Pushed to the limit in Lode |
| --- | --- | --- | --- |
| **Rust** | Memory safety and data-race freedom at compile time | Lifetime annotations; panics on index, overflow (debug) and `unwrap` | Safety without lifetimes ([memory.md](memory.md)); **no implicit crash paths at all** ([safety.md](safety.md)) |
| **Rust** | Sum types, exhaustive `match`, traits | | The same, plus generics checked at the definition site |
| **Zig** | `comptime` as the one mechanism for generics, conditional code and formatting | Dead branches for other targets go unchecked and rot | `if comptime` plus multi-target checking in one command ([comptime.md](comptime.md)) |
| **Zig** | No hidden control flow, no hidden allocation, explicit allocators | Passing an allocator to every call is noisy | Allocator as an implicit, declared context: `uses alloc` ([memory.md](memory.md#allocation)) |
| **Zig** | Error sets, `try`, error return traces | | Typed `throws`, with the same zero-cost return-value implementation ([errors.md](errors.md)) |
| **Go** | Readability, one obvious way, enforced formatting | `gofmt` is optional in practice | The formatter is part of the compiler ([syntax.md](syntax.md)) |
| **Go** | Packages by full URL, minimal version selection, build info in binaries | | The same, plus an audit of `unsafe` and FFI across the dependency tree ([packages.md](packages.md)) |
| **Go** | One tool: build, test, fmt, cross-compile with no setup | | The same, down to 8-bit targets and wasm ([backend.md](backend.md)) |
| **Go** | Easy concurrency | Needs a runtime and GC; data races are possible | Structured concurrency with no runtime and no data races ([concurrency.md](concurrency.md)) |
| **all three** | Small, fast native code | A trivial program still pays for startup code it never asked for (Go, Rust: a lot; Zig: a little) | **Pay only for what you use**, see below |

### Pay only for what you use

A hello world is not simple once compiled in most of these languages. To avoid
penalizing a language for its formatting library, we measure three variants
each: the formatted print, a direct write through the standard library, and
the most direct write the language offers.

Measured on Linux x86-64, 2026-09-29, go 1.26.5, rustc 1.98.0, zig 0.15.1.
All builds are size-optimized and stripped. Syscalls are counted after
`execve`. Sources and the script are in [`bench/hello/`](../bench/hello).

| Language | Variant | Binary size | Syscalls |
| --- | --- | --- | --- |
| Go (`-ldflags='-s -w'`) | `fmt.Println` | 1.59 MB | ~275 |
| | `os.Stdout.Write` | 1.41 MB | ~280 |
| | `syscall.Write(1, ...)` | 1.23 MB | ~255 |
| Rust (`opt-level=z`, LTO, `panic=abort`, stripped) | `println!` | 292 KB (static: 1.13 MB) | 65 (static: 36) |
| | `stdout().write_all` | 291 KB (static: 1.13 MB) | 65 (static: 36) |
| | `extern "C" write` | 289 KB (static: 1.13 MB) | 65 (static: 36) |
| Zig (`-OReleaseSmall -fstrip`) | `print` through a buffered writer | 10.2 KB | 6 |
| | `File.stdout().writeAll` | 10.2 KB | 6 |
| | `posix.system.write` | 4.8 KB | 6 |
| **Lode target** | any of the above | **a few hundred bytes** | **2: `write`, `exit_group`** |

What this shows:

- **Formatting is not the cost in Go or Rust.** Removing it saves little.
  The cost is the fixed startup: Go's runtime (scheduler threads, GC, over a
  hundred `rt_sigaction` calls) and Rust's `std` startup: `poll` to check that
  fds 0-2 are open, reading `/proc/self/maps` for the stack guard, a
  `sigaltstack` for stack-overflow reporting, signal setup, plus glibc's own
  initialization.
- **Zig is already close**, and its comptime formatting costs only about 5 KB.
  Its 6 syscalls are: `arch_prctl` (thread-local storage setup), two
  `prlimit64` (raising the stack limit), `rt_sigaction(SIGPIPE)`, `write`,
  `exit_group`. None of the first four were asked for by this program.

The rule for Lode goes one step past Zig: **nothing is in the binary or runs
at startup unless the program's code reached it.**
- No thread-local storage setup unless something uses thread-locals.
- No stack-limit changes. With [stack bounds](safety.md#stack-bounds) the
  compiler knows how much stack the program needs, and only asks for more when
  it doesn't fit.
- No signal handlers the program didn't ask for. SIGPIPE behavior is a
  decision of the program's I/O code, not of startup.
- No runtime initialization, no pre-linked formatting engine, no panic or
  unwind machinery (there isn't any).

Every feature must be designed so that its cost disappears when it isn't used.
This is a requirement on the language (comptime formatting, no panics) *and* on
the backend (LatticeFoundry's static linker with no libc, and minimal ELF
layout for the byte count). `bench/hello/run.sh` stays as a regression
benchmark, and a Lode row is added as soon as there is a compiler.

## Goals

* Memory safety by design ([memory.md](memory.md))
* No undefined behavior and no implicit crash paths in safe code. Every way a
  program can fail is explicit in the types ([safety.md](safety.md)). This
  replaces the original "impossible to write code that crashes", which cannot
  be guaranteed in full (see safety.md for what remains).
* Strong compiler checks, as many as possible at compile time
* Small code gives a small executable: `print("hello world\n")` compiles to a
  single `write` syscall because the formatting is resolved at compile time
  ([comptime.md](comptime.md))
* No runtime: nothing runs before `main` or in the background unless the
  program started it. Runtime-like parts (green threads) are opt-in and
  layered ([What "no runtime" means](#what-no-runtime-means))
* Configurable optimization strategies (inlining, unrolling and so on) per
  target profile ([backend.md](backend.md))
* Able to write low-level code, legacy code (8-bit and so on) and kernels
* Better error handling than Go, without the cost of unwinding exceptions
  ([errors.md](errors.md))
* Native parallelism and threads, with data-race freedom
  ([concurrency.md](concurrency.md))
* Easy to read and follow
* Enforced formatting, using tabs ([syntax.md](syntax.md))
* Multi-architecture and multi-platform, including wasm
* No asm in the standard library. Syscalls are a language intrinsic
  ([safety.md](safety.md#the-trusted-boundary))
* Optimization for specific CPUs (SIMD and so on) with hints, including "do not
  optimize this" for constant-time crypto (`secret` types, [types.md](types.md))
* A project can reimplement low-level pieces (allocators, syscalls, even a
  whole os/arch) ([backend.md](backend.md), [memory.md](memory.md))

## What "no runtime" means

**Status:** Decided

Some features (green threads, a lazily initialized global) need code that
manages state across the program's life, and that is runtime-like. "No
runtime" doesn't forbid them. It means:

1. **Nothing runs before `main`**, and nothing runs after it returns, except
   what the program itself started.
2. **Nothing runs in the background uninvited.** No OS threads, signal
   handlers, timers or collectors that the program didn't start.
3. **Opt-in is visible in the source.** A runtime-like component (a scheduler,
   for example) is started by an explicit call, and it stops when that call
   returns.
4. **Each component is optional, layered and replaceable,** and only the parts
   the program reaches are linked
   ([pay only for what you use](#pay-only-for-what-you-use)).

Green threads are the main case ([concurrency.md](concurrency.md#green-threads-without-a-runtime)).

## Non-goals (for now)

- Garbage collection or any runtime component.
- A stable ABI for Lode-to-Lode dynamic libraries ([packages.md](packages.md)).
- CUDA/SIMT targets. The target model should not rule them out, but they do not
  shape v1.
- Inventing new thread-synchronization primitives in v1. Structured concurrency
  plus proven primitives come first.

## Where Lode could stand out

Rust, Zig and Go already exist. These are the ideas that would make Lode more
than a reskin, in order of how central they are:

1. **No UB and no implicit crash paths, while staying readable.** This rests on
   value semantics (no lifetimes) and compile-time proof obligations for
   indexing and arithmetic.
2. **First-class constant-time code** through `secret` types that the backend is
   required to respect.
3. **Static stack and memory bounds** for embedded targets.
4. **Pay only for what you use**, measured: hello world is one `write`.

## Backend

**Status:** Decided

Lode compiles through [LatticeFoundry](https://github.com/KarpelesLab/latticefoundry), our own compiler
backend framework. It grows alongside Lode and can be changed to fit what
Lode needs. See [backend.md](backend.md).

## Decisions so far

| Topic | Decision | Doc |
| --- | --- | --- |
| Name | Lode; command `lode`, extension `.lode` | this file |
| Positioning | The best of Rust, Zig and Go, each pushed to its limit | this file |
| Backend | LatticeFoundry | [backend.md](backend.md) |
| Formatting | Enforced, tabs | [syntax.md](syntax.md) |
| Include files | None; the compiler reads packages directly | [packages.md](packages.md) |
| Imports | Full git URL, except the standard library | [packages.md](packages.md) |
| External libraries | Go-style: native by default, FFI through an explicit interface, static builds possible | [packages.md](packages.md) |
| Build metadata | Binaries embed the list of compiled-in modules and their versions | [packages.md](packages.md) |
| Strings | UTF-8 by default; encoding is part of the string type; no implicit conversion | [strings.md](strings.md) |
| Shared / back-pointer data structures | Provided by the standard library (`unsafe` inside, safe API outside); user structs hold owning pointers only | [memory.md](memory.md#shared-and-back-pointer-structures-belong-to-the-standard-library) |
| Dead branches | A branch known false at compile time is removed, and may contain code that is invalid for the current target | [comptime.md](comptime.md) |
| Views | Returned views borrow from the parameters; no view fields in structs | [memory.md](memory.md#views) |
| Refinements | Lightweight refinements in types (`i < buf.len`), same fact language as the checker | [safety.md](safety.md#refinements-in-types) |
| Async | Green threads (stackful), scheduler as a library; no function coloring | [concurrency.md](concurrency.md#async-green-threads) |
| Globals | Mutable globals are `Atomic`/`Mutex` only, compiled down to plain globals when nothing runs concurrently; all globals initialized at compile time | [memory.md](memory.md#globals) |
| Methods | Types have methods (`fn Point.length(self)`) | [types.md](types.md#methods) |
| Operators | No user-defined operator overloading | [types.md](types.md#operators) |
| I/O | Separate blocking and green-thread implementations, chosen by type; hand-written single-thread non-blocking loops are first-class; all share `std/os` + `std/poll` | [concurrency.md](concurrency.md#io) |
| Thread placement | Dedicated and CPU-pinned threads are supported; the main thread can be reserved for foreign event loops; thread affinity (`uses main_thread`, `uses pinned`) is checked at compile time | [concurrency.md](concurrency.md#thread-placement-dedicated-threads-cpu-pinning-the-main-thread) |
| Channels and sync tools | Library types (no syntax): channels, `select`, `Mutex`, `Once`, cancellation; values move through channels; no panics on close/send | [concurrency.md](concurrency.md#channels-and-synchronization-tools) |
| Compiler | Written in Rust on LatticeFoundry first, self-hosted later | [backend.md](backend.md#compiler-implementation) |
