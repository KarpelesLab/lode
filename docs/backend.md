# Backend: LatticeFoundry

## Decision

**Status:** Decided

Lode compiles to [LatticeFoundry](https://github.com/KarpelesLab/latticefoundry) IR. LatticeFoundry
(LF) is our own compiler backend framework: a typed SSA IR, a verifier,
optimization passes, code generation, object files and a linker, in pure Rust.
It's not mature yet. It grows with Lode, and Lode's needs are allowed to
change it.

The frontend (the Lode compiler) is a separate project that uses LF as a
library, the same way LF's `lf-cc` C frontend does (see LF ROADMAP §6: frontends
live outside the framework library).

### LF is the bootstrap backend

**Status:** Decided (2026-09-29)

We considered skipping LF and emitting code directly for one platform, then
building a Lode backend from that. We keep LF, because it already has the
machinery any backend needs (SSA IR, verifier, register allocation, encoding,
ELF, linker, DWARF), and a backend written *in Lode* can't exist until the
language can express it.

- **Now:** LF is the backend of the Rust compiler. Lode depends on released
  LF versions from crates.io (first `0.0.0`, now `0.0.2`) and updates only to
  new releases. It never builds against a local LF checkout. Features Lode
  needs are tracked below; LF bugs Lode finds are reported as reproducible IR
  tests.
- **At self-hosting:** the Lode compiler's backend is written in Lode, as a port
  of LF's design (its IR design and tenets are documented). That's the
  "Lode-based LLVM". It also removes the need for a self-hosted compiler to
  call a Rust library.
- **Revisit if** LF's priorities keep diverging from Lode's, or if the IR can't
  grow what Lode needs. The fallback is a small direct backend for x86-64
  Linux, owned by this repository.

## Compiler implementation

**Status:** Decided

- The first Lode compiler is written in **Rust** and uses LatticeFoundry as a
  library. LF is also Rust, so there is no FFI boundary between them.
- It becomes **self-hosted** once Lode can express it well. Self-hosting is
  also the first large real program in Lode, and the best test of whether
  the language is pleasant to use.
- Until then, the Rust compiler is the bootstrap compiler. **Open:** after
  self-hosting, how is Lode bootstrapped from scratch? Keeping the Rust
  compiler maintained is expensive. The usual alternatives are a checked-in
  build of the compiler in a portable form (Zig uses a wasm build), or a
  bootstrap chain.
- Keep that eventual port in mind while writing the Rust compiler: plain data
  structures, arenas and indices (LF's style already) rather than Rust-specific
  patterns that won't translate.

**Current state:** the compiler in `src/` has a lexer, a parser, the
formatter (`lode fmt`), a checker (types, and the flow-sensitive proof checker
of [safety.md](safety.md#the-fact-language)), and lowering to LF IR of only
the functions `main` reaches. The `lode` command builds static x86-64 Linux
executables through LF's own linker. It also checks programs for AArch64
Linux, wasm32, Cortex-M (`thumbv7m`) and AVR (`lode check --targets=...`,
[comptime.md](comptime.md#keeping-dead-branches-from-rotting)), without
generating code for them yet. See the README for the supported subset.

## Why it fits

| LF property | What Lode gets from it |
| --- | --- |
| Semantics-first IR, poison + freeze, minimal UB (LF tenet T2, ir-design §5) | A clear target for "no UB": Lode's safe code must lower to IR with no UB-triggering ops, and that's checkable. |
| Verified refinement with `z3rs` (T3, B2) | Optimizations don't introduce the bugs the language promises to rule out. |
| One lattice engine: ranges, known bits, nullness (T4, B8) | Removing leftover checks in explicit fallback code. (The *acceptance* check stays in the frontend, see [safety.md](safety.md#the-checker-must-be-predictable).) |
| Arbitrary-width `Int(width)` | `uN`/`iN` types map directly. |
| Cost/resource lattice (B9) | Stack bounds and code-size-driven optimization profiles. |
| Content-addressed IR (T5, B7) | Package caching and incremental builds. |
| Static linking with no libc | The "hello world is one `write`" goal, and static builds by default. |
| `--lto` whole-program merge | Cross-package inlining, needed for comptime-expanded code to shrink. |

## What Lode needs from LatticeFoundry

Specific bugs and needs are filed as
[LatticeFoundry issues](https://github.com/KarpelesLab/latticefoundry/issues).
The first list was tracked in
[LF #3](https://github.com/KarpelesLab/latticefoundry/issues/3), closed
2026-10-04: everything on it shipped in LF `0.0.2`. Using each feature from
Lode is now Lode's own work.

### Available in LF `0.0.2`

| Need | In LF | For Lode |
| --- | --- | --- |
| Building, verifying, optimizing and linking from a frontend | since `0.0.0` | Used by the compiler |
| `Syscall` (Linux ABI, up to 6 arguments, raw `-errno` result) | `0.0.0` | Used: the `syscall` intrinsic, `std/os` |
| Correct `i8`/`i16` comparisons, `switch`, division, `cond_br` | `0.0.0` | Used (found by Lode's tests) |
| Packed segments: no page padding in the file ([LF #2](https://github.com/KarpelesLab/latticefoundry/issues/2)) | `0.0.1` | Hello world went from 4,108 to 1,049 bytes |
| Volatile loads/stores, atomics (`atomic_rmw`, `cmpxchg`), fences with C11 orderings | `0.0.2` | Next: `Atomic[T]`, `Mutex[T]` globals, MMIO |
| Stack usage per function and call-graph worst case (`StackReport::worst_case_depth`) | `0.0.2` | Used: `lode build --stack-usage` ([stack bounds](safety.md#stack-bounds)) |
| Stack probes (on by default) | `0.0.2` | Overflow reliably hits the guard page |
| `secret` values, `declassify`, constant-time verifier | `0.0.2` | [`secret[T]`](types.md#secret-types) |
| Context save/restore/switch with full register state, signal preemption (`lf_ctx_preempt`), opt-in yield points | `0.0.2` | [Green threads](concurrency.md#preemption) |
| Targets: wasm32, Cortex-M (Thumb-2, soft-float, Intel HEX), AVR (separate address spaces, own linker) | `0.0.2` | Checked for, not built yet: `lode check --targets`; `std/os` is per target (Linux only) |
| SIMD vectors (SSE2, NEON, scalar fallback) | `0.0.2` | SIMD types |
| PE/COFF and Mach-O objects, Win64 calling convention, raw binary / Intel HEX | `0.0.2` | Windows and macOS layers |
| Shared libraries and position-independent code (`--shared`, `--pie`) | `0.0.2` | C-ABI libraries |
| DWARF debug info with source lines (`-g`) | since `0.0.0` | Lode doesn't emit line numbers yet |

### Still open

- **6502 and Z80** targets, for the legacy goal. Not started in LF; file an
  issue when Lode needs them.
- **AArch64 position-independent code**: in progress in LF.

### Resolved open questions in LF, from Lode's side
- **Exceptions / unwinding:** Lode doesn't need unwinding. Errors are return
  values ([errors.md](errors.md)).

## Optimization profiles

**Status:** Proposed

The same program can target a flash-limited Cortex-M, a Threadripper or wasm.
The right inlining, unrolling and vectorization choices differ completely, so
they come from a **profile**, not from scattered flags:

```
profile embedded_small {
	optimize = size
	inline = minimal           // only when it shrinks the code
	unroll = never
	stack_bound = required     // see safety.md
	oom = error
}

profile server {
	optimize = speed
	inline = aggressive
	cpu = native               // or an explicit feature list
}
```

- Built-in profiles cover the common cases. A project can define its own.
- The profile is visible to comptime code (`target.profile`), so a library can
  pick an algorithm, for example a table-based versus a loop-based CRC.
- **Per-function hints** override the profile: `@inline(always|never)`,
  `@optimize(size|speed|none)`, `@cold`. `secret` types are the principled
  version of "don't optimize this crypto code". `@optimize(none)` is the blunt
  one.
- LF's cost lattice (B9) should model code size, latency and energy as one
  cost, with the profile setting the weights, rather than using magic
  thresholds.

**Open:** can a single build mix profiles (a firmware whose hot loop is compiled
for speed and the rest for size)? Per-function hints may be enough.

## Custom os/arch layers

**Status:** Proposed

The standard library's lowest layer (`std/os`) is chosen by `target.os`. A
project can supply its own implementation of that layer: syscalls, the root
allocator, thread creation and program entry. This is how a kernel, a
bootloader or firmware on a platform we don't know about gets a working `std`
subset without forking the compiler. The layer's interface is a trait-like
contract checked at compile time. **Its exact shape is Open.**
