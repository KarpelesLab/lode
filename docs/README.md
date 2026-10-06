# Lode documentation

Design documents for Lode. Nothing here is final. Each section starts with
a **Status:** line:

- **Decided**: agreed on. Changing it needs a deliberate discussion.
- **Proposed**: the current best idea, written down so it can be argued with.
- **Open**: not decided yet. The options are listed.

Sections on what the compiler does today are **Implemented** (or
**Implemented subset**, when only part of the design is there). A design
the compiler already follows says so after its status: "Proposed; implemented
in the compiler".

The syntax in the code examples is provisional (see [syntax.md](syntax.md)).
The examples show semantics. They are not a grammar.

## Index

| Document | Covers |
| --- | --- |
| [concept.md](concept.md) | Positioning (best of Rust, Zig and Go), goals, non-goals, decisions so far |
| [safety.md](safety.md) | The core guarantee: no undefined behavior and no hidden crash paths; proof obligations; `unsafe` |
| [syntax.md](syntax.md) | Provisional syntax, lexical rules, enforced formatting |
| [types.md](types.md) | Primitive types, integers and arithmetic, composite types, generics, traits, `secret` |
| [memory.md](memory.md) | Memory model: value semantics, parameter conventions, allocation |
| [errors.md](errors.md) | Error handling: `throws`, `try`, `catch`, cleanup |
| [comptime.md](comptime.md) | Compile-time evaluation, conditional compilation, target queries |
| [generics.md](generics.md) | Proposal for M7: generic functions and types, traits, dispatch, the `comptime` they need |
| [allocation.md](allocation.md) | Proposal for M8: resource types and destruction, the allocator context, `Box`, `List`, `String` |
| [strings.md](strings.md) | Strings, encodings, runes |
| [packages.md](packages.md) | Packages, imports, versions, FFI, build metadata |
| [concurrency.md](concurrency.md) | Threads, data-race freedom, structured concurrency |
| [backend.md](backend.md) | LatticeFoundry as the backend, optimization profiles, what we need from it |
| [roadmap.md](roadmap.md) | What the compiler implements next, in order |
