# Packages, imports and linking

## No include files

**Status:** Decided

The compiler reads packages directly. There are no headers, no preprocessor and
no textual inclusion. The build machine is assumed strong enough to parse
dependencies, and LatticeFoundry's content-addressed IR (tenet T5) makes caching
parsed and checked packages straightforward.

## Packages and modules

**Status:** Proposed

Go's vocabulary, which is proven:

- A **package** is a directory of source files that share a namespace.
- A **module** is a versioned tree of packages with a manifest at its root
  (`lode.mod`, name Open).
- Visibility: `pub` exports from a package. Everything else is private to the
  package.
- No import cycles between packages.

## The standard library in the compiler today

**Status:** Implemented subset

- `import "std/x"` loads every `.lode` file in the directory `x` under the
  standard library root, which is `$LODE_STD` if set and otherwise the `std/`
  directory of the compiler's source tree. Each file must declare
  `package x`. Imports are followed transitively; a cycle is an error.
- Other imports (anything outside `std/`) aren't supported yet.
- Only `pub` items can be used from another package, as `pkg.name`, and
  only `pub` methods: `pkg.Type.new()`, `value.method()`. A `pub trait` is
  used as `pkg.Trait` in a bound or an `impl`; an `impl`'s methods are as
  visible as its trait.
- Linker symbols are `<import path>.<name>` (`std/io.print`), and
  `<import path>.<Type>.<name>` for a method (`std/io.File.write`); the
  program's own package uses its name (`main.main`). An instance of a
  generic function adds its type arguments: `std/math.max[u32]`; a method
  of a generic type has the type's after the type's name:
  `std/buf.StackBuf[64].push`. A method of an `impl` names its trait after
  it: `std/io.File.write_bytes<std/io.Writer>`; a trait's default method
  has the trait's name and the type:
  `std/io.Writer[std/buf.StackBuf[16]].write`.
- So far there are seven packages: `std/os`, `std/io`, `std/math`,
  `std/slices`, `std/buf`, `std/vec` and `std/encoding`.
- `std/os` is the Linux system calls, for x86-64 and AArch64 (see
  [Per-target code](#per-target-code)):
  - `write` (one `write` system call) and `write_all(fd, b: []u8)` (all of
    the bytes, retrying), which return a negative error number on failure.
  - `read(fd, data: *u8, len: usize) -> isize` (one `read` system call,
    `unsafe` like `write`): the number of bytes read, 0 at the end of the
    input, or a negative error number.
  - `exit(code: i32) -> never` ends the process at once with status `code`
    (its low 8 bits). It's the `exit_group` system call, so it ends every
    thread, not only the calling one. No `defer` or `errdefer` body runs, in
    the function or its callers. Output isn't lost: there's no buffer, every
    write is a system call. It returns
    [`never`](types.md#never-in-the-compiler-today), so the code after a call
    can't be reached and needs no `return`. The checker doesn't know what a
    system call does, so an endless `loop {}` follows `exit_group` in its
    body: it never runs, and costs one jump.
  - `abort() -> never` ends the process because it can't go on
    ([errors.md](errors.md#what-is-not-an-error)): `exit(134)`, the status a
    shell shows for a process killed by `SIGABRT`. No signal is raised, so
    there's no core dump.
  - `Error`, the errors std reports, from the error numbers `write` and
    `read` can give: `bad_fd` (`EBADF`), `broken_pipe` (`EPIPE`), `no_space`
    (`ENOSPC`, `EDQUOT`), `io` (`EIO`, or a result the kernel never gives),
    and `other(errno)` for any other number. `error(n)` converts a failed
    call's result to an `Error`.
- `std/io`:
  - `File`, an open file: a struct holding its file descriptor,
    `File{fd: i32}`. It doesn't close the file (there's no way to open one
    yet). `stdin()`, `stdout()` and `stderr()` return the standard ones.
  - `File.read(self, inout buf: []u8) throws(os.Error) -> usize` reads into
    `buf` once and returns the number of bytes read: 0 only at the end of
    the input (or for an empty `buf`), and possibly fewer than `buf.len`
    before it, as a pipe or a terminal gives what it has. An interrupted
    call (`EINTR`) is retried. `let n = try io.stdin().read(&buf)`.
  - `File.read_full(self, inout buf: []u8) throws(os.Error) -> usize` reads
    until `buf` is full or the input ends, so it returns less than
    `buf.len` only at the end of the input. If it throws, the bytes read
    before the error are in `buf`, but their count is lost.
  - There's no slicing yet (`buf[0..n]`), so a program can't pass the first
    `n` bytes of a buffer it read to `write_bytes` without a pointer and
    `unsafe` (tests/programs/stdin_cat.lode).
  - `File.write(self, s: str) throws(os.Error)` writes all of `s`, or
    throws the error that stopped it. It's the checked way to write:
    `try io.stdout().write(s)`.
  - `File.write_bytes(self, b: []u8) throws(os.Error)` writes raw bytes the
    same way, such as a buffer the program filled:
    `io.stdout().write_bytes(buf)`.
    `write(s)` is `write_bytes(s.bytes())`.
  - `File.write_buf[N: usize](self, b: buf.StackBuf[N]) throws(os.Error)`
    writes the bytes written in a `StackBuf`, the same way.
  - `Writer`, a trait for what bytes are written to:
    `write_bytes(inout self, b: []u8) throws(os.Error)`, required, and
    `write(inout self, s: str) throws(os.Error)`, a default that calls it.
    `File` implements it with its own `write_bytes`, and so does
    `buf.StackBuf[N]`, which throws `os.Error.no_space` when it's full,
    after writing what fits. Generic code takes any of them:
    `fn greet[W: io.Writer](inout w: W) throws(os.Error)`. A `File`'s own
    `write` comes first in `f.write(s)`; `io.Writer.write(&f, s)` calls the
    trait's.
  - `print(s: str)` and `eprint(s: str)` write a string to standard output
    and standard error.
  - `print_int[T: Integer](n: T)` writes an integer of any type in decimal
    to standard output, with a `-` if it's negative, and `eprint_int` to
    standard error: `io.print_int(x)`, or `io.print_int[u64](5)` for a
    literal, which doesn't tell the type. Each call makes one `write` system
    call, of digits built in a plain `[21]u8`: a `buf.StackBuf[21]` made
    each program printing integers 640 bytes larger at `-O2`, since
    `push_front` isn't inlined, its error result goes through memory, and
    the written part is checked again before the write. They're a stopgap
    until `print("{}", n)` ([generics.md](generics.md#format-strings)).
  - `print` and the others but the `File` methods ignore output errors:
    they're for output that isn't worth failing over.
- `std/math`, generic:
  - `min(a, b)`, `max(a, b)` and `clamp(x, lo, hi)` for any `Ordered` type
    (the integers, `bool`, and the structs and enums with an
    `impl Ordered`). Their parameters are `sink`, so they need no
    `Copy`.
  - `abs(x)` for any integer type. It saturates: `abs` of a signed type's
    smallest value is its largest.
- `std/slices`, generic:
  - `sort(inout xs: []T)`, smallest first, for an `Ordered + Copy` element
    type: a heapsort, with no allocation and a constant stack. `&a` sorts
    an array, `&a[i..j]` part of one.
  - `is_sorted(xs: []T) -> bool`.
- `std/buf`, fixed-capacity byte buffers:
  - `StackBuf[N: usize]`, a buffer of at most `N` bytes written at either
    end, stored in place (on the stack for a local). The bytes written so
    far are `bytes[start..end]`, and only those are read.
  - `StackBuf[N].new()` makes an empty one that `push` fills from the
    front of its storage; `StackBuf[N].new_end()` one that `push_front`
    fills from the back, such as for digits, last first. Both still fill
    the storage with zeros once
    ([memory.md](memory.md#uninitialized-buffers)).
  - `push(inout self, b: u8) throws(Error)` writes `b` after the bytes
    written, `push_front` before them; each throws `buf.Error.full` when
    there's no room at that end.
  - `len(self) -> usize` and `get(self, i: usize) -> ?u8` (byte `i` of the
    written part, `none` past it) read it; `io.File.write_buf` writes it.
- `std/vec`, fixed-capacity vectors:
  - `ArrayVec[T: Copy, N: usize]`, a list of at most `N` elements of type
    `T`, stored in place: no allocation. Its slots are `[N]?T`, so it needs
    no value to fill the empty ones with; `T` must be `Copy` to make them
    `none`.
  - `ArrayVec[T, N].new()`, `len(self) -> usize`,
    `push(inout self, v: T) throws(Error)` (`vec.Error.full` when it holds
    `N` elements), `pop(inout self) -> ?T`, `get(self, i: usize) -> ?T`, and
    `put(inout self, i: usize, v: T) -> bool`, which replaces element `i`.
  - `var v = vec.ArrayVec[u16, 8].new()`, or `var v: vec.ArrayVec[u16, 8] =
    vec.ArrayVec.new()`.
- Every access in `std/buf` and `std/vec` is proven. Without refinements,
  each method checks the bound it relies on (`end <= N`), since the
  fields are visible and could have been changed.
- `std/encoding`, character encodings over bytes, beside the built-in
  `str` ([strings.md](strings.md)):
  - `Encoding`, a trait with an associated type `Rune` (`Copy + Eq`), an
    associated constant `MAX_LEN: usize`, and the associated functions
    `decode(bytes: []u8) -> ?Decoded[Rune]` (the first rune and its length
    in bytes), `encode(r: Rune, set out: [MAX_LEN]u8) -> usize` and
    `validate(bytes: []u8) -> bool` (a default).
  - `Decoded[R]`, a rune and its length: `rune: R`, `len: usize`.
  - `Utf8` (`Rune` is `u32`, `MAX_LEN` 4; overlong forms, surrogates and
    values above U+10FFFF are invalid) and `Ascii` (`u8`, 1). An encoding
    is a type, never a value: `encoding.Utf8.decode(b)`. They're enums of
    one variant, since structs without fields aren't supported yet.
  - `count[E: Encoding](bytes: []u8) -> ?usize`, the number of runes, or
    `none` if `bytes` isn't valid in `E`.

## Per-target code

**Status:** Decided ([generics.md](generics.md#decisions), question 6);
implemented (M7d)

A package holds the code of every target. A package-level `if comptime`
picks the declarations compiled for the target, rather than file names
(Go's `os_linux.go`):

```
if comptime target.os == .linux {
	if comptime target.arch == .x86_64 {
		const SYS_WRITE = 1
	} else if comptime target.arch == .aarch64 {
		const SYS_WRITE = 64
	}
	pub fn write_all(fd: i32, b: []u8) -> isize { ... }
} else {
	compile_error("std/os: unsupported target")
}
```

- Every file is parsed for every target; only the branches the target
  takes are checked.
- The conditions use only `target`, literals, comparisons, `&&`, `||` and
  `!`, since they're evaluated before the package's names are known.
- A `compile_error` reached among a package's declarations ends the check
  there: "std/os: unsupported target" is the one error a program using
  `std/io` gets for wasm32.
- `std/os` is like that: Linux only, with the system call numbers of x86-64
  and AArch64. Only x86-64 Linux can be built today; `lode check
  --targets=aarch64-linux` checks the other.
- `lode check --targets=all` checks a program for every target the
  compiler knows, in one run, so the branches for other targets don't
  rot unseen. CI checks the test programs for both Linux targets.

## Imports

**Status:** Decided

```
import "std/io"                               // standard library: short path
import "github.com/author/project/sub"        // everything else: full URL
import yaml "github.com/someone/yaml"         // rename
```

The full URL reduces typosquatting, because you see exactly where code comes
from. It doesn't eliminate it (`github.com/gorila/mux` still looks plausible),
which is why the points below matter.

## Versions and supply chain

**Status:** Proposed

- **Minimal version selection** (as in Go): builds are reproducible without a
  lock-file solver, and upgrading is always an explicit action.
- A **checksum file** next to the manifest pins the content hash of every
  dependency version. A force-pushed tag is detected and refused.
- **Open:** do we run a public checksum database and module proxy (like
  `sum.golang.org` / `proxy.golang.org`)? Without one, a deleted repo breaks
  every build that depends on it, and first fetches are trust-on-first-use.
- Vanity import paths (`example.com/pkg` that redirect to a repository), via
  Go's `<meta>` tag approach. **Open.**
- `lode audit` lists every dependency, its version, and whether it contains
  `unsafe` or FFI code ([safety.md](safety.md#the-trusted-boundary)).

## Build metadata in binaries

**Status:** Decided

Every binary embeds the list of compiled-in modules and their versions (and
content hashes), in a dedicated section. `lode version -m <binary>` reads it
back. This is the same idea as `go version -m`.

This answers the tracking argument for shared libraries: to find which
binaries use a vulnerable version of a module, scan the binaries. The data can
also be exported as an SBOM.

On targets where every byte counts (embedded), the section can be stripped into
a separate file by profile choice.

## External libraries (FFI)

**Status:** Decided: Go-style

- Native Lode code by default. Static builds are the default.
- Calling C goes through an explicit interface, and every foreign call is
  `unsafe`. The package wrapping it provides the safe API.
- C declarations are imported through the build (reading a C header via
  LatticeFoundry's `lf-cc` frontend), not by textual inclusion. **Open:** is that
  worth the complexity, or should C declarations be written by hand at first?
- Bindings declare **thread affinity** when a foreign library needs it:
  `uses main_thread` (UI toolkits such as AppKit) or `uses pinned` (libraries
  with thread-local state, such as OpenGL contexts). The compiler checks every
  call site ([concurrency.md](concurrency.md#checking-thread-affinity-at-compile-time)).
- Windows and macOS have no stable raw syscall ABI. There, the os layer must
  call the system libraries (`kernel32`, `libSystem`) through FFI. This is part
  of the target's os layer, not of user code.

## Shared libraries

**Status:** Proposed

The original concept weighed the trade-off:

- In favor: shared pages in memory, one update fixes every program, license
  models (LGPL).
- Against: DLL hell, no inlining across the boundary, version-dependent ABIs
  (why Rust's dylibs go mostly unused), and C headers that inline code into
  callers (a hybrid that's hard to track).

Proposal:

1. **Producing C-ABI shared libraries** (`.so`, `.dll`) is supported, so Lode
   can provide libraries to other languages. The exported API uses C types
   only. LatticeFoundry can output shared libraries since `0.0.2`
   ([backend.md](backend.md#available-in-lf-002)); Lode doesn't use it yet.
2. **Consuming C shared libraries** works through FFI, as above.
3. **Lode-to-Lode dynamic linking with a Lode ABI** is a **non-goal** for
   now. Embedded build metadata covers the tracking use case. Revisit later if
   a stable ABI subset emerges naturally.
