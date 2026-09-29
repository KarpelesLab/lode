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
  LF versions from crates.io (first: `0.0.0`) and updates only to new
  releases. It never builds against a local LF checkout. Features Lode needs are tracked
  below; LF bugs Lode finds are reported as reproducible IR tests.
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

**Current state:** a scaffold in `src/`: lexer, parser, checker (types and a
first version of the proof-obligation checker, using value ranges of
literals, immutable bindings and types, without narrowing on conditions yet),
and lowering to LF IR. The `lode` command builds static x86-64 Linux
executables through LF's own linker. See the README for the supported subset.

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

This is a living list, roughly in the order Lode will need it. Anything marked
*unknown* needs to be checked against LF's current state.

### Needed for the first working compiler
- [ ] A stable-enough Rust API for building IR from a frontend (LF already
  exposes it for `lf-cc`).
- [x] Building IR from a frontend, verifying, optimizing, and linking a static
  executable: works for the compiler scaffold.
- [x] **A syscall intrinsic** (Linux syscall ABI), in LF `0.0.0`: `Syscall`
  takes a number and up to six `i64`/`ptr` arguments and returns the raw
  kernel result. It's a full memory clobber that is never removed or
  reordered. Lode's `syscall` intrinsic lowers to it; `std/os` uses it for
  `write`.
- [x] Correct comparisons on `i8`/`i16`. The x86-64 encoder compared narrow
  values as 32-bit, so leftover upper register bits (e.g. after an `i8` add
  that wrapped) gave wrong results. C code never hit it because C promotes to
  `int` first. Fixed in LF's `SetccCmp` encoding, with a regression test.
- [ ] **Smaller executables:** LF's linker starts each segment on a new page
  in the file, so a hello world with 12 bytes of string data is 4,108 bytes
  of which about 3 KB is padding. Merging read-only data into the code
  segment, or placing segments without page-aligning their file offsets
  (only `offset ≡ vaddr (mod page)` is required), would bring it to about
  1.1 KB.
- [ ] The same width issue in LF's `switch` lowering (it always compares 64
  bits). Lode doesn't emit `switch` yet; needed for `match`.
- [ ] Volatile load and store, atomics and fences in the IR.
- [ ] Debug info (DWARF) with source positions from a non-C frontend. LF has
  DWARF with `-g`.

### Needed for the safety story
- [ ] **Stack usage per function**, exposed after register allocation and frame
  layout, so the frontend can compute call-graph bounds
  ([safety.md](safety.md#stack-bounds)).
- [ ] **Constant-time preservation** ([types.md](types.md#secret-types)): a way
  to mark values as secret in the IR. Passes must not introduce branches or
  memory accesses that depend on them, and instruction selection must avoid
  variable-time instructions. This fits LF's bet B10 ("provenance & effects in
  the type system"). A narrow `secret` taint might be a practical first step
  toward it.
- [ ] Guard-page or stack-probe support for defined stack-overflow aborts.

- [ ] **Preemption support for green threads**
  ([concurrency.md](concurrency.md#preemption)): a trampoline that saves and
  restores the complete register state (including vector registers) from a
  signal or interrupt context. Also optional yield-point insertion in loops
  whose cost isn't bounded, driven by the cost lattice (B9).

### Needed for target reach
- [ ] **wasm32** target.
- [ ] **32-bit ARM (Cortex-M, Thumb-2)** for embedded, including no-FPU
  soft-float.
- [ ] **8-bit targets** (AVR first? 6502 / Z80 for the legacy goal). These stress
  every assumption: 16-bit pointers, multiple address spaces (AVR program
  memory versus data), no hardware multiply. LF's `Ptr(addrspace)` is reserved
  for exactly this.
- [ ] SIMD vector types (`Vector(T, n)`, planned in LF with the first SIMD target).
- [ ] Output formats other than ELF: PE/COFF (Windows), Mach-O (macOS), raw
  binary / Intel HEX (firmware). LF lists Windows and macOS formats as a
  non-goal for now.
- [ ] Shared-library output, for C-ABI libraries
  ([packages.md](packages.md#shared-libraries)).

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
