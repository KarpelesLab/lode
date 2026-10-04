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
  only `pub` methods: `pkg.Type.new()`, `value.method()`.
- Linker symbols are `<import path>.<name>` (`std/io.print`), and
  `<import path>.<Type>.<name>` for a method (`std/io.File.write`); the
  program's own package uses its name (`main.main`).
- So far there are two packages, `std/os` and `std/io`.
- `std/os` is the Linux x86-64 system calls:
  - `write` (one `write` system call) and `write_all` (all of a string,
    retrying), which return a negative error number on failure.
  - `Error`, the errors std reports, from the error numbers `write` can
    give: `bad_fd` (`EBADF`), `broken_pipe` (`EPIPE`), `no_space`
    (`ENOSPC`, `EDQUOT`), `io` (`EIO`, or a result the kernel never gives),
    and `other(errno)` for any other number. `error(n)` converts a failed
    call's result to an `Error`.
- `std/io`:
  - `File`, an open file: a struct holding its file descriptor,
    `File{fd: i32}`. It doesn't close the file (there's no way to open one
    yet). `stdout()` and `stderr()` return the standard ones.
  - `File.write(self, s: str) throws(os.Error)` writes all of `s`, or
    throws the error that stopped it. It's the checked way to write:
    `try io.stdout().write(s)`.
  - `print(s: str)` and `eprint(s: str)` write a string to standard output
    and standard error.
  - `print_u64(n: u64)` and `print_i64(n: i64)` write an integer in decimal
    to standard output, and `eprint_u64` and `eprint_i64` to standard error.
    Smaller integer types convert implicitly. Each call makes one `write`
    system call. They're a stopgap until `print("{}", n)`
    ([comptime.md](comptime.md#format-strings)).
  - `print` and the others but `File.write` ignore output errors: they're for
    output that isn't worth failing over.

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
