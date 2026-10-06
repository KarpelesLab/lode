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
  package, a struct's fields included: `pub name: T` exports a field
  ([types.md](types.md#structs)).
- No import cycles between packages.

## The standard library in the compiler today

**Status:** Implemented subset

- `import "std/x"` loads every `.lode` file in the directory `x` under the
  standard library root, which is `$LODE_STD` if set and otherwise the `std/`
  directory of the compiler's source tree. Each file must declare
  `package x`. Imports are followed transitively; a cycle is an error.
- Other imports (anything outside `std/`) aren't supported yet.
- Only `pub` items can be used from another package, as `pkg.name`, and
  only `pub` methods: `pkg.Type.new()`, `value.method()`, and only `pub`
  fields: `value.field`, and literals of structs whose fields are all
  `pub`. A `pub trait` is
  used as `pkg.Trait` in a bound or an `impl`; an `impl`'s methods are as
  visible as its trait.
- Linker symbols are `<import path>.<name>` (`std/os.write_all`), and
  `<import path>.<Type>.<name>` for a method (`std/io.File.write`); the
  program's own package uses its name (`main.main`). An instance of a
  generic function adds its type arguments: `std/math.max[u32]`; a method
  of a generic type has the type's after the type's name:
  `std/buf.StackBuf[64].push`. A method of an `impl` names its trait after
  it: `std/io.File.write_bytes<std/io.Writer>`; a trait's default method
  has the trait's name and the type:
  `std/io.Writer[std/buf.StackBuf[16]].write`. An expansion of a function
  with `comptime` parameters or a pack is numbered:
  `std/io.print$3[u32, str]`.
- So far there are eight packages: `std/os`, `std/io`, `std/mem`,
  `std/math`, `std/slices`, `std/buf`, `std/vec` and `std/encoding`.
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
    the function or its callers. Output isn't lost: nothing stays in a buffer
    between calls (each `io.print` writes its output before it returns). It returns
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
    and `other(errno)` for any other number (`other(2)` is `ENOENT`).
    `error(n)` converts a failed call's result to an `Error`.
  - `Fd`, a file descriptor the value owns (M8a,
    [allocation.md](allocation.md#m8a-in-the-compiler)): its `deinit`
    closes it, so it's closed once, when the `Fd` is destroyed. It isn't
    `Copy`: it moves. Its number is `pub let fd: i32`, read everywhere,
    set only in `std/os`; `io.File.from_fd(f.fd)` reads and writes it,
    and that `File` is valid only while `f` is. `unsafe fn Fd.own(fd: i32)`
    takes a descriptor over.
  - `open(path: str, flags: u32, mode: u32) throws(Error) -> Fd` opens a
    file (`openat` from the working directory, with `O_CLOEXEC` added).
    `flags` joins `O_RDONLY`, `O_WRONLY` or `O_RDWR` with `O_CREAT`,
    `O_EXCL`, `O_TRUNC`, `O_APPEND` and `O_CLOEXEC`; `mode` gives a new
    file's permissions (`0o644`). The path is copied to a stack buffer of
    `PATH_MAX` (4096) bytes for its trailing 0 (`@uninit`, so not filled
    first): a longer path throws `other(36)` (`ENAMETOOLONG`), and one
    with a 0 byte `other(22)` (`EINVAL`).
  - `close(sink f: Fd) throws(Error)` closes `f` and reports the kernel's
    error (`EIO` from a write that failed late, on some file systems). The
    descriptor is closed either way. Destroying an `Fd` closes it too, and
    ignores the error.
- `std/io`:
  - `File`, an open file: a struct holding its file descriptor in a
    private field. It doesn't own the descriptor, and doesn't close it: it's
    plain data, `Copy`. `stdin()`, `stdout()` and `stderr()` return the
    standard ones, and `File.from_fd(fd: i32)` any other, such as the
    descriptor of an `os.Fd` that owns it (`io.File.from_fd(f.fd)`).
  - `File.read(self, inout buf: []u8) throws(os.Error) -> usize where
    result <= buf.len` reads into
    `buf` once and returns the number of bytes read: 0 only at the end of
    the input (or for an empty `buf`), and possibly fewer than `buf.len`
    before it, as a pipe or a terminal gives what it has. An interrupted
    call (`EINTR`) is retried. `let n = try io.stdin().read(&buf)`.
  - `File.read_full(self, inout buf: []u8) throws(os.Error) -> usize where
    result <= buf.len` reads
    until `buf` is full or the input ends, so it returns less than
    `buf.len` only at the end of the input. If it throws, the bytes read
    before the error are in `buf`, but their count is lost.
  - Both results are refined ([safety.md](safety.md#refinements-in-types)):
    after `let n = try io.stdin().read(&buf)`, `buf[..n]` is proven with no
    check (tests/programs/stdin_cat.lode).
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
  - `print[..A: Format](comptime fmt: str, args: ..A)` writes the format
    string `fmt` to standard output, each `{}` replaced by the next
    argument: `io.print("x = {}, name = {}\n", x, name)`. `{{` and `}}`
    write a brace. A `str` known only at run time is printed with
    `io.print("{}", s)`. The format is read when compiling: a `{}` without
    an argument, an argument without a `{}`, an unclosed `{`, a `}` alone
    and an argument whose type isn't `Format` are errors at the call
    ([generics.md](generics.md#m7e-in-the-compiler)). Each `print` is one
    `write` system call. A format that's only text is written as it is,
    with no buffer: `io.print("hello world\n")` is that `write` and no
    formatting code. Any other format is put together in a buffer of
    `io.PRINT_BUF_SIZE` (256) bytes on the stack, not filled first
    (`@uninit`), and written at the end; a
    print longer than that is written 256 bytes at a time, each time the
    buffer is full. `eprint` writes to standard error the same way.
  - `write_fmt[W: Writer, ..A: Format](inout w: W, comptime fmt: str, args:
    ..A) throws(os.Error)` writes a format string to any `Writer`, and
    throws the error that stopped it: `try io.write_fmt(&f, "{} items\n",
    n)`, or into a `buf.StackBuf`.
  - `Format`, a trait for what `{}` writes:
    `format[W: Writer](self, inout w: W) throws(os.Error)`. Every integer
    type writes itself in decimal, with a `-` if it's negative (its digits
    built in a plain `[21]u8`, then one `write_bytes`: a `buf.StackBuf[21]`
    made each program printing integers 640 bytes larger at `-O2`), `bool`
    as `true` or `false`, and `str` as it is. Other types implement it:
    `impl io.Format for Point { fn format[W: io.Writer](self, inout w: W)
    throws(os.Error) { try io.write_fmt(&w, "({}, {})", self.x, self.y) }
    }`. A generic function that prints a `T` bounds it: `[T: Integer +
    io.Format]`.
  - `print` and `eprint` ignore output errors: they're for output that
    isn't worth failing over. `write_fmt` and the `File` methods report
    them.
- `std/mem`, for values that own resources (M8a,
  [allocation.md](allocation.md#partial-moves-and-patterns)): a value that
  isn't `Copy` moves, and nothing is moved out of an element, a part of a
  variable, or a place passed `inout`. These take a part out by putting
  another value in its place:
  - `swap[T](inout a: T, inout b: T)` exchanges two values.
  - `replace[T](inout place: T, sink v: T) -> T` puts `v` in `place` and
    returns the old value: `mem.replace(&p.name, v)`.
  - `take[T](inout place: ?T) -> ?T` takes an optional's value and leaves
    `none`: `mem.take(&slots[i])`. The built-in `opt.take()` does the same.
  - `destroy[T](sink x: T)` destroys `x` now, and `forget[T](sink x: T)`
    ends it without destroying it (its `deinit` never runs: a leak, which
    is safe).
  - `swap`, `take` and `forget` are implemented by the compiler: they're
    declared `@intrinsic`, which only the standard library can do, and
    their empty bodies aren't used.
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
    end, stored in place (on the stack for a local). Its fields are
    private: the bytes written so far are `bytes[start..end]`, and only
    those are read. It isn't `Eq`.
  - `StackBuf[N].new()` makes an empty one that `push` fills from the
    front of its storage; `StackBuf[N].new_end()` one that `push_front`
    fills from the back, such as for digits, last first. Neither writes
    the storage: it's `@uninit`
    ([memory.md](memory.md#uninitialized-buffers)).
  - `push(inout self, b: u8) throws(Error)` writes `b` after the bytes
    written, `push_front` before them; each throws `buf.Error.full` when
    there's no room at that end.
  - `len(self) -> usize` and `get(self, i: usize) -> ?u8` (byte `i` of the
    written part, `none` past it) read it; `write_to(self, fd: i32) ->
    isize` writes it to a file descriptor as `os.write_all` does (0 or a
    negative error number), and `io.File.write_buf` calls it.
- `std/vec`, fixed-capacity vectors:
  - `ArrayVec[T, N: usize]`, a list of at most `N` elements of type `T`,
    stored in place: no allocation. Its slots are `[N]?T`, so it needs no
    value to fill the empty ones with (`[none; N]` works for an optional
    of any type). `T` can be any type since M8a: an element that isn't
    `Copy` is moved in and out, and the elements left are destroyed with
    the vector.
  - `ArrayVec[T, N].new()`, `len(self) -> usize`,
    `push(inout self, sink v: T) throws(Error)` (`vec.Error.full` when it
    holds `N` elements), `pop(inout self) -> ?T` (with `mem.take`),
    `get(self, i: usize) -> ?T`, which copies and so needs `T: Copy`, and
    `put(inout self, i: usize, sink v: T) -> bool`, which replaces element
    `i` and destroys the old one.
  - `var v = vec.ArrayVec[u16, 8].new()`, or `var v: vec.ArrayVec[u16, 8] =
    vec.ArrayVec.new()`.
- Every access in `std/buf` and `std/vec` is proven. Their fields are
  private, so only their own methods change them, and their refinements
  keep the bounds the methods rely on (`StackBuf`: `start <= end`, `end <=
  N`; `ArrayVec`: `count <= N`), so no method checks them again
  ([memory.md](memory.md#struct-invariants)).
- `std/encoding`, character encodings over bytes, beside the built-in
  `str` ([strings.md](strings.md)):
  - `Encoding`, a trait with an associated type `Rune` (`Copy + Eq`), an
    associated constant `MAX_LEN: usize`, and the associated functions
    `decode(bytes: []u8) -> ?Decoded[Rune]` (the first rune and its length
    in bytes), `encode(r: Rune, set out: [MAX_LEN]u8) -> usize` and
    `validate(bytes: []u8) -> bool` (a default).
  - `Decoded[R]`, a rune and its length: `pub rune: R`, `pub len: usize`.
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
