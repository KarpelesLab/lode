# Allocation and heap types (M8)

This is the design proposal for milestone M8 ([roadmap.md](roadmap.md)):
types that own resources, the allocator context, and the first heap types.
It builds on what's already written: value semantics, parameter conventions,
[Copies](memory.md#copies), [Destruction](memory.md#destruction),
[Allocation](memory.md#allocation) and [Views](memory.md#views) in
memory.md; [`Copy` and moves](generics.md#copy-and-moves-in-generic-code) in
generics.md; [error sets](errors.md#error-sets); and the proof checker of
[safety.md](safety.md). Each section lists the options, the trade-offs and a
recommendation. The decisions only the user can make are collected at the
end, in [Decisions](#7-decisions).

Everything here is **Proposed** unless a section says otherwise. M8a is
implemented (2026-10-06): resource types, destruction and moves, with
what the compiler does in [M8a in the compiler](#m8a-in-the-compiler).
M8b is implemented (2026-10-06): the allocator context, the root
allocator and `Box`, in [M8b in the compiler](#m8b-in-the-compiler).
M8c is implemented (2026-10-06): views returned from functions, `List`
and `String`, in [M8c in the compiler](#m8c-in-the-compiler). M8d is
implemented (2026-10-07): error-set unions, the `oom` policy and counted
allocators, in [M8d in the compiler](#m8d-in-the-compiler). That
completes M8.

## Starting point

**Status:** What the compiler did before M8a

- Every concrete type is plain data and `Copy`: integers, `bool`, views,
  arrays, structs, enums, optionals. Nothing owns a resource, nothing is
  destroyed, and a concrete value never moves.
- A type parameter without the bound `Copy` is moved, never copied
  (M7a, `Checker::consume` in `src/sema/generic.rs`). Moving out of a
  `let`, a `var` or a `sink` parameter makes it unassigned, through the
  definite-assignment state the checker already keeps. Copying an element
  or a read-only parameter of such a type is an error. So generic code
  already follows the rules move-only types need.
- `defer` and `errdefer` run at every exit of their block (end, `return`,
  `throw`, a failed `try`, `break`, `continue`), in reverse order
  (`run_defers` in `src/lower.rs`). `os.exit` runs none of them.
- Raw pointers exist only to integers (`*u8`), only `unsafe` code uses
  them, and a struct can't hold one. Struct fields are private to their
  package unless marked `pub` (decided and implemented 2026-10-06).
- `uses` is a reserved word, rejected by the parser. `where` writes a
  refinement ([safety.md](safety.md#refinements-in-types)), including
  refinements of struct fields that every value of the struct keeps.
- `std/os` wraps `read`, `write`, `exit_group`. There's no `mmap`.
- Views are never returned, except a `str` with static storage. A slice of
  a `var` array can't be kept in a local, only passed to a function
  ([memory.md](memory.md#views)).

## Principles

**Status:** Proposed

1. **An owning value has one owner.** It moves instead of copying. It's
   destroyed exactly once, by its owner, at a point the source shows.
2. **No hidden control flow beyond destruction.** Destruction runs where
   scopes end, like `defer`. Nothing else runs implicitly.
3. **Nothing allocates behind the caller's back.** A function that doesn't
   declare `uses alloc` can't allocate, directly or through what it calls.
4. **An allocator outlives everything it allocated.** This is the one new
   safety obligation of M8, and the hardest one
   ([Allocators that end](#allocators-that-end-arenas-and-fixed-buffers)).
5. **Pay only for what you use.** A program that doesn't allocate links no
   allocator code and passes no hidden parameter. Hello world stays 577
   bytes and two system calls.
6. **The checker stays specified and decidable.** Destruction, moves and
   view borrows are flow analyses over one function, like definite
   assignment. No lifetimes, no solver.

## 1. Resource types and destruction

### Which types own resources

**Status:** Implemented (M8a); raw pointer fields in M8b

A type **needs destruction** when it declares a `deinit`, or has a field or
payload that needs destruction (an array or optional of one too). Such a
type is not `Copy`. That's the automatic rule generics.md already states:
"a struct, enum or array is `Copy` when its parts are and it has no
`deinit`".

A type that holds a raw pointer field ([The unsafe toolkit](#the-unsafe-toolkit))
is not `Copy` either, even without a `deinit`: copying the pointer would
share what it points to. Its author writes the `deinit` or a `Clone` impl,
or neither (a type that is moved and never destroyed, which is safe, only
leaky).

Existing code is unaffected: before M8a, no type needed destruction.

### Declaring destruction

**Status:** Recommended answer kept (question 1); implemented (M8a)

Options:

1. **A method with a reserved name**, `fn File.deinit(sink self)`, as
   memory.md has it. Declared in the type's package like any method.
2. **A trait**, `impl Drop for File { fn deinit(sink self) }`, as Rust.

A trait adds nothing here. Nobody writes a bound `T: Drop` (every `T` may
need destruction, and generic code destroys `T` values without a bound),
and coherence already allows one method of a name per type.

**Recommendation: 1.** Rules:

- `fn T.deinit(sink self)`, no other parameters, no result. It can't throw
  and can't `uses alloc`: destruction happens at scope ends, also in
  functions that neither throw nor allocate. A type whose cleanup can fail
  (a file whose `close` reports an error) offers a `close(sink self)
  throws(E)` method; its `deinit` does the same cleanup and ignores the
  error.
- Inside `deinit`, `self` is a value whose own `deinit` doesn't run again.
  When the body ends, the fields not moved out are destroyed, in reverse
  declaration order. So `deinit` only releases what the fields don't
  release themselves.
- A type without a `deinit` whose fields need destruction gets one from the
  compiler: the fields, in reverse order.
- `deinit` can't be called directly. `mem.destroy(sink x: T)` ends a value
  early (it's an empty function: the value is destroyed when the parameter's
  scope ends).

### When destruction runs

**Status:** Implemented (M8a), with the choices of
[M8a in the compiler](#m8a-in-the-compiler)

- At the end of the scope that owns the value, in reverse order of
  declaration, **interleaved with `defer`**: one stack per block. A `defer`
  written after `let f = open(...)` runs before `f` is destroyed.
- At every exit that leaves the scope, exactly where `defer` bodies run
  today: the block's end, `return`, `throw`, a failed `try`, a `break` or
  `continue` that leaves it. A `return` destroys after computing its value,
  and the returned value is moved out, not destroyed.
- **Not** on a call to a `never` function. `os.exit` and `os.abort` end the
  process without running `defer`s, and they don't destroy anything either.
  So safety can't depend on a `deinit` running: leaking is safe, as in Rust.
  (`mem.forget(sink x: T)` is safe for the same reason.)
- **Temporaries** (a call's result that isn't bound, as in
  `print_len(make_list())`) are destroyed at the end of the statement, in
  reverse order of creation. A view of a temporary can't be kept: that's
  already the rule for slices of temporaries.
- **Assignment** destroys the old value after the new one is computed:
  `x = make()`, `p.name = s`, `xs[i] = v` (the last for an `inout` slice or
  a container's element).
- A `set` argument of a type that needs destruction must be unassigned at
  the call (declared without a value, or moved from). Destroying it at the
  call would make "as before the call" in a `catch` block mean two things.

### Moves

**Status:** Implemented (M8a), with drop flags (question 2)

The M7a rule extends from type parameters to every type that isn't `Copy`,
unchanged: keeping a value (storing it, returning it, passing it `sink`,
binding it by a pattern, taking it out with `??`) moves it out of a `let`,
a `var` or a `sink` parameter, which is unassigned until assigned again.
Keeping an element, a read-only parameter or an `inout` one is an error.
`consume` already does this for `Ty::Param`; it only needs `is_copy` to
return `false` for the new types.

A variable moved on some paths and not others needs a decision at the
scope's end. Options:

1. **Drop flags** (Rust): a hidden `bool` per such variable, cleared by the
   move, tested at the scope's exits. Destruction stays at the scope's end on
   every path.
2. **Destroy at the join**: where the paths meet, destroy the value on the
   path that didn't move it. No flag, but destruction moves earlier than
   the scope's end, on one path only.

Option 2 is wrong for guards: with `let g = m.lock()` and `if c { mem.destroy(g) }`,
the lock would be released at the `if`'s end on the other path too, before
the rest of the block runs.

**Recommendation: 1.** Only variables moved on some paths get a flag; it's
a local the optimizer folds away when the paths are known. At `-O0` it
costs a byte and a test.

### Partial moves and patterns

**Status:** Implemented (M8a), but `match &x`

- **No partial moves out of a struct local** (`let n = p.name` where `name`
  needs destruction is an error). `mem.replace(&p.name, v)` and
  `mem.take(&p.name)` (for a type with a default, or an optional) cover the
  need. Tracking moved fields per local is the expensive part of Rust's
  move checker, and rarely needed.
- `opt.take()` on an `inout` optional (built in, like `??`) gives the value
  and leaves `none`: the basic step for walking `?Box[Node]` chains.
- **Pattern bindings are projections**: in `match t { node(l, r) => ... }`,
  `l` and `r` read the scrutinee in place, like a default parameter. They
  can be read, compared and passed to default parameters without a move.
  Keeping one (returning it, passing it `sink`) moves it out, and that's
  allowed only when the scrutinee is a value the code may consume: a
  temporary (`match list.pop()`), or a `let`, `var` or `sink` local, which
  is then moved as a whole; the payload fields not kept are destroyed at
  the arm's end. `match &x` makes the bindings `inout` projections.

### Explicit copies

**Status:** Implemented (M8a), with `uses alloc throws(AllocError)` in
M8b; `clone()` kept as the name (question 9)

memory.md: "Copying them is explicit: `x.copy()`, which can allocate and
therefore can throw." That needs a trait:

```
trait Clone {
	fn clone(self) uses alloc throws(AllocError) -> Self
}
```

- Derived, like `Eq`, for a type whose parts are all `Clone` and that has
  neither a `deinit` nor a raw pointer field. Such types write the impl
  (`List[T: Clone]`, `String`).
- `Copy` types are `Clone` (the copy).
- The name: memory.md says `copy()`. `clone()` avoids pairing the implicit
  `Copy` with an explicit `copy()` that means something else (it allocates,
  it throws). See question 9.

### `defer` and `errdefer`

**Status:** Implemented (M8a)

Today a `defer` body can't move a variable declared outside it. Cleanup
of a resource type needs exactly that: `errdefer os.close(fd) catch _ {}`,
where `close` takes the descriptor `sink`. The rule becomes: a `defer` (or
`errdefer`) body may consume an outer variable if the variable is definitely assigned at every
exit the body runs at. The checker already has that state for drop flags.

```
fn open_both(a: str, b: str) throws(os.Error) -> Pair[os.Fd, os.Fd] {
	let fa = try os.open(a)
	errdefer os.close(fa) catch _ {}     // fa is assigned at every error exit below
	let fb = try os.open(b)
	return Pair{first: fa, second: fb}   // success: errdefer doesn't run, fa moves out
}
```

A `try g(fa)` after the `errdefer`, where `g` takes `fa` `sink`, would be an
error: on that `try`'s error exit, `fa` is already gone.

### Parameter conventions

**Status:** Implemented (M8a); unchanged where not said

- Default: read-only, passed by address, no copy (already).
- `inout`: the callee may replace the value; `x = v` in the callee
  destroys the caller's old value.
- `sink`: the caller's variable is moved from; the callee owns the value
  and destroys it unless it moves it on. In memory, the callee's copy on
  entry is the move itself (no change in lowering).
- `set`: see above (the argument must be unassigned).
- Exclusivity is unchanged. `xs.push(xs.len)` stays an error, like
  `p.scale(p.x)`; `let n = xs.len` first.

### Generics

**Status:** Implemented (M8a)

- Generic code destroys `T` values at scope ends like any other values,
  with no bound needed. `mono` instantiates the destruction for each
  concrete type: nothing for a `Copy` type, a call to its `deinit` (or
  generated destruction) otherwise.
- `needs_deinit[T]()` (compile-time `bool`) lets containers skip the loop
  over elements, though the optimizer removes an empty loop anyway.
- `ArrayVec[T: Copy, N]` can drop its `Copy` bound once optionals of
  non-`Copy` values are destroyed (done in M8a).
- A type argument still can't be a view, so `List[str]` is not a type:
  `List[String]`, or a list of indices into a buffer. memory.md's example
  `-> List[str]` changes accordingly.

### Field visibility

**Status:** Decided (2026-10-06): option 1 with `pub let`, implemented
([types.md](types.md#structs); `pub let` in M8a)

A type that keeps an invariant (a `List`'s pointer, length and capacity, an
owned file descriptor) needs fields that code outside the package can't
change, or even build: `File{fd: 1}` in another package would make a second
owner of descriptor 1, closed twice. Options:

1. **Private by default**, like every other item: a field is visible only
   in its package unless marked `pub`. A struct with a field that isn't
   `pub` can't be built by a literal outside its package.
2. **Visible by default, with `priv`** for fields that keep an invariant.
3. **`unsafe` fields**: writable only in `unsafe` code.

**Recommendation: 1, plus `pub let`**: a field marked `pub let` can be read
everywhere and assigned only in its package. `List` exposes
`pub let len: usize` and `pub let cap: usize`, so `xs.len` is a field read,
and a term for the checker, everywhere. Option 1 changes existing code:
std's structs and the test programs whose fields are used from another
package gain `pub`. It's mechanical.

### Linear types

**Status:** Open (memory.md); recommendation below

A linear type has no `deinit`: reaching a scope's end with such a value
alive is a compile error, so every path must consume it (`tx.commit()` or
`tx.rollback()`). The analysis is the one destruction needs (which values
are alive at each exit), so the checker side is small.

The cost is in generics. `List[T]` destroys its elements in its own
`deinit`, so `T` can't be linear unless generic code says it never destroys
a `T` implicitly (Rust's long-running `?Leak` discussion). Every generic
container would have to be checked against it, or linear types couldn't be
type arguments at all.

**Recommendation: not in M8.** Leave room: no `T: Drop` bound and no
`Destroy` trait that would get in the way. Revisit with a use case, likely
with transactions or channels' senders.

### Destroying recursive structures

**Status:** Implemented (M8b) for chains through a struct's field

memory.md requires the generated destruction of a self-recursive owning
type to be iterative, for [stack bounds](safety.md#stack-bounds).

- **Chains** (a type whose recursion goes through one field, as
  `next: ?Box[Node[T]]`): the generated destruction is a loop that takes
  `next`, frees the node, and continues with what it took. Constant stack.
- **Trees** (recursion through several fields): there's no general
  iterative form without memory or pointer reversal. The generated
  destruction recurses, and `--stack-usage` names it as the cause of a
  missing bound. The `Tree[T]` of std (memory.md) uses an explicit work
  list or rotations.

### In the proof checker

**Status:** Implemented (M8a)

A `deinit` sees only `self` and globals, so the destruction at a scope's
end changes no facts about the locals still alive. The checker treats it
like a `defer` body: nothing to forget.

## 2. The allocator context

### `uses alloc`

**Status:** Implemented (M8b)

```
fn read_lines(f: File) uses alloc throws(LineError | AllocError) -> List[String] { ... }
```

- `uses alloc` comes after the parameters and before `throws`.
- A call to a function that `uses alloc` needs the context: the caller
  declares `uses alloc`, or the call is inside a `with alloc = ...` block.
- `with` is only allowed in a function that declares `uses alloc` itself.
  So the rule "a function without `uses alloc` doesn't allocate" holds
  through every call it makes, not only the direct ones. Interrupt handlers
  and real-time code rely on it.
- Destruction doesn't need the context: a container frees through the
  allocator it remembers ([Who frees](#who-frees-containers-remember-their-allocator)).
  So a function without `uses alloc` can destroy a `List`, but never grow
  one.
- Not inferred: it's part of the signature, visible and greppable, like
  `throws(E)`. The error for a missing one has a fix ("add `uses alloc` to
  `f`").
- Trait methods: as generics.md says, `uses alloc` is part of a trait
  method's signature; an impl may use fewer contexts, never more.
- `main` declares `uses alloc` to get the root allocator. Without it, the
  program has none.

### `with alloc = x`

**Status:** Implemented (M8b); handles of the root, of a `static`
allocator, or (`unsafe`) of any allocator; a counted allocator given as
it is, `with alloc = arena` (M8d)

```
fn summarize(path: str) uses alloc throws(Error | AllocError) -> Summary {
	var arena = try alloc.Arena.new()      // its pages come from our allocator
	with alloc = arena.handle() {
		let words = try split_words(path)  // allocates in the arena
		return count(words)                // Summary is plain data
	}
}
```

- `x` is an `alloc.Handle`: a reference to an allocator that is safe to
  keep ([Allocators that end](#allocators-that-end-arenas-and-fixed-buffers)).
- The block is an ordinary block: `defer`, destruction and every exit work
  as in any block. The context goes back to the outer one when it ends.
- `uses task` and the cancellation context
  ([concurrency.md](concurrency.md#green-threads-without-a-runtime)) use
  the same mechanism later. Nothing here is specific to allocation but the
  name and the root.

### The `Allocator` trait

**Status:** Implemented (M8b), with `resize` and `free` `unsafe`, and
`AllocError` built in; `grow` added in M8c

```
pub unsafe trait Allocator {
	fn alloc(self, size: usize, align: usize) throws(AllocError) -> *u8
	fn resize(self, p: *u8, old: usize, new: usize, align: usize) -> bool  // in place, or false
	fn free(self, p: *u8, size: usize, align: usize)
	fn grow(self, p: *u8, old: usize, new: usize, align: usize) throws(AllocError) -> *u8  // M8c
}

pub enum AllocError {
	out_of_memory
}
```

- The size is passed to `free`, as in Zig, so an allocator needs no header
  per allocation.
- The methods take `self` read-only: one allocator is reached through many
  containers at once. Its state changes through `unsafe` code inside it,
  which is why implementing the trait is `unsafe` (`unsafe impl`): the
  author promises the usual contract (fresh, aligned, non-overlapping
  memory; `free` only of what it gave).
- A size that overflows (`n * size_of[T]()`) is `out_of_memory` too: no
  other variant is needed.
- `grow` (M8c) moves a block to a larger one and keeps its bytes, in place
  or not; a growing `List` calls it. Its default is `resize`, or else
  `alloc`, a copy and `free`. The page allocator and the heap's large
  blocks override it with `mremap` that may move: the kernel moves the
  pages, without copying the bytes, so a list growing past 2 KiB costs one
  system call per doubling. A value moves by its bytes, so moving a list's
  elements this way is a move of each.
- `align` is a power of two. The fact language can't say "power of two",
  so the trait could take its base-2 logarithm instead (`align_log2: u8
  where align_log2 < 64`, a refinement). Open.

### Who frees: containers remember their allocator

**Status:** Recommended answer kept (question 4); implemented (M8b,
`Box`)

A value allocated in one `with` block can be destroyed, or grown, under
another context. Options:

1. **The container stores its allocator** (Rust's `Vec<T, A>`, Zig's
   "managed" `ArrayList`): one word per container, a pointer to the
   allocator. Freeing and growing go to the right allocator wherever the
   value ends up.
2. **The container doesn't**; `deinit` and growth use the context. Smallest
   layout (Zig's "unmanaged" containers), but a value that crosses a `with`
   is freed by the wrong allocator: undefined behavior, which safe code must
   not have.
3. **The allocator is found from the address** (a header per allocation, or
   a lookup by address range). Costs on every allocation or free.

**Recommendation: 1.** And the word disappears when it can: when no `with`
is reachable from `main`, every allocation comes from the root allocator,
and the stored allocator is zero-sized ([Lowering](#lowering-the-context)).
`Box[T]` is then one pointer, as a `?Box[Node]` link should be.

### Allocators that end: arenas and fixed buffers

**Status:** Decided (question 5): counted allocators; implemented (M8d),
with the choices of [M8d in the compiler](#m8d-in-the-compiler)

Option 1 above stores a pointer to the allocator in every container. If
the allocator is destroyed first (an arena local whose function returns, a
fixed buffer on the stack), the container frees into, or grows from, freed
memory. A value made in an arena can leave the `with` block in many ways:
returned, assigned to an outer variable, pushed into an outer list through
`inout`, stored in a `Mutex` global, sent on a channel. Options:

A. **Region check**: the `with` block of an allocator that can end is
   checked so that no value that needs destruction leaves it: no
   assignment, `inout`, `set` or `sink` of such a type to a place declared
   outside the block, no return of one. The holes are globals and channels,
   reached through any function called inside: the function storing into a
   `Mutex[List[String]]` doesn't know where its argument was allocated.
   Closing them needs the allocator's kind in types or effects.
B. **The allocator in the type**: `List[T, A]`, with `A` defaulting to the
   root. An arena's handle is a view, so `List[T, ArenaRef]` is a view, and
   the [view rules](memory.md#views) keep it from escaping. Sound with no
   new rule, but a function returns `List[T]` or `List[T, ArenaRef]`, not
   "a list in whatever allocator is in context": it gives up `with alloc =
   arena` around existing code, the main point of the context.
C. **Counted allocators**: an allocator that can end lives in a control
   block (on its parent allocator's memory) with a count of its live
   allocations. `alloc` adds one, `free` takes one. Destroying the arena's
   owner (`Arena` itself) releases its chunks only when the count is zero;
   otherwise the last `free` does. A handle into a counted allocator is
   always valid. Costs: an increment and a decrement per allocation (atomic
   only when the program has threads, by the
   [downgrade rule](memory.md#downgrading-when-theres-no-concurrency)), and
   an arena's memory may outlive the arena when values from it escape (a
   leak of those values' arena, never a dangling pointer). It can't work
   for a buffer on the stack, which ends with its frame whatever the count.
D. **Unchecked**, as in Zig. Not an option for safe code.

**Recommendation: C for M8.** It keeps the context model whole, needs no
new check, and composes: an arena made inside an arena counts as an
allocation of its parent. Then:

- `alloc.Handle` is what `with` takes. Safe ways to get one: the root
  allocator, a `static` allocator (it never ends), and `.handle()` of a
  counted allocator (`alloc.Arena`, or `alloc.Counted[A]`, which wraps any
  user allocator `A` in a counted control block).
- `arena.reset()` reuses the memory only when nothing from it is alive, and
  returns `false` otherwise.
- A **fixed buffer** (an allocator over a given array) can be the root
  allocator over a `static` array, which is what firmware without a heap
  wants, or an allocation of its parent. A fixed buffer over a stack array
  is not available in safe code in M8. Option A could allow it later for a
  `with` block that calls only functions the checker can see don't store
  into globals or channels; that's future work.

### The root allocator

**Status:** Implemented (M8b), but `@root_allocator`

- `std/os` gains `mmap`, `munmap` and `mremap` (`unsafe`, like `read` and
  `write`), and `os.PageAllocator`: each allocation is its own mapping,
  rounded up to pages; `resize` is `mremap` without moving.
- `std/alloc` gains `alloc.Heap`, a small general allocator in Lode: size
  classes (16 to 2048 bytes, powers of two), a free list per class, carved
  from 64 KiB chunks of the page allocator; larger allocations go straight
  to the page allocator. Not thread-safe in M8: there are no threads yet.
  With threads, it takes a lock (a borrow flag when nothing runs
  concurrently, per memory.md's downgrade rule).
- The root is `alloc.Heap` unless the program chooses another
  (`@root_allocator(os.PageAllocator)` in the main package, or a project's
  own, which covers the [custom os layer](backend.md#custom-osarch-layers)).
  It's a `static`, initialized at compile time: it maps its first chunk on
  the first allocation, so nothing runs before `main`.
- At the end of `main`, values are destroyed like anywhere else, which may
  cost `munmap` calls. `os.exit` skips that. Whether a profile should let
  `main`'s last destructions of memory-only values be skipped is **Open**.

### Lowering the context

**Status:** Recommended answer kept (question 6); implemented (M8b),
with the choices of [M8b in the compiler](#m8b-in-the-compiler)

Options:

1. **A hidden parameter**: each function that `uses alloc` takes one more
   argument, the `alloc.Handle` in context. `with` passes another one. A
   function without `uses alloc` doesn't have it.
2. **A global** (thread-local) "current allocator", saved and restored by
   `with`. No parameter, but a thread-local needs setup before `main` on
   some targets, a `with` has to restore it on every exit, green threads
   would have to swap it, and it's a mutable global that memory.md
   doesn't allow.
3. **Instantiation by context**: each `uses alloc` function is compiled once
   per allocator type that reaches it, like a generic. Static calls
   everywhere, but code size multiplies with every arena type, for every
   function between `main` and the allocation.

**Recommendation: 1**, with two whole-program rules that make it cost
nothing in the common case. The program is linked whole, after `mono`, so
the set of handles a `with` can install is known:

- **No `with` reachable from `main`**: the context is always the root
  allocator. The hidden parameter is not passed, `alloc.Handle` and the
  allocator stored in containers are zero-sized, and an allocation is a
  direct call into the root allocator, inlined like any call.
- **Otherwise**: a handle is one pointer to the allocator's control
  block, whose first word says which allocator type it is. A call
  through a handle is a `match` over the allocator types the program
  installs (closed-world dispatch): direct calls, no function pointers, no
  `dyn` needed first, and an exact [stack bound](safety.md#stack-bounds)
  (the worst of the cases). With one type, the `match` is gone.

The cost when a program does use `with`: one register per call to a
`uses alloc` function, and one word per container.

### Out of memory

**Status:** Implemented (M8d), as proposed here, with the choices of
[M8d in the compiler](#m8d-in-the-compiler)

memory.md proposes a program-level policy: `oom = error` (the default)
propagates `AllocError`; `oom = abort` makes allocating functions not throw
`AllocError` from the caller's point of view. The question left Open: can
the same library compile under both?

Yes, with this rule: **under `oom = abort`, `AllocError` is an empty
enum.** The root allocator aborts (`os.abort()`, status 134) instead of
returning the error. Then:

- `throws(AllocError)` alone throws nothing: the call returns `T`, and
  `try` on it compiles to nothing. A `try` or `catch` on a call that can't
  throw is allowed, without a warning, when the reason is the policy.
- `throws(ParseError | AllocError)` is `throws(ParseError)`.
- Library code is written once, for `oom = error`, with `try`. An
  application under `oom = abort` may leave out `try` on calls whose only
  error is `AllocError`; that code doesn't compile under `oom = error`,
  which is the application's choice.

This needs **error-set unions**, which the compiler doesn't have. The
minimal form, without inference:

- `throws(A | B)` names a union of error enums. Its value is a compiler-made
  enum with one variant per member (`.alloc(e)`), so `match` on it works as
  today, and `e` is matched by member type: `err(e: AllocError) => ...`
  (pattern syntax Open).
- `try` converts a call's error into the caller's when the caller's set
  contains it: `AllocError` into `ParseError | AllocError`, and
  `A | B` into `A | B | C`. Anything else is converted by hand, as today.
- A member that is an empty enum is dropped from the set; a set with no
  members means "doesn't throw".

Inferred sets (`throws` alone, errors.md) can come later on top of this.

Where the policy is set: the main package, as `@oom(abort)` in its file
with `main`, so the source says it, rather than a command-line flag that
changes what compiles (question 6).

## 3. Heap types

### The unsafe toolkit

**Status:** Implemented (M8b); `mem.view` and `mem.view_str` in M8c

Heap types are written in Lode, in std, with `unsafe` inside and a safe API
outside, as memory.md decides for shared structures. They need:

- `*T` for any `T` (today only integers), as a struct field (holding and
  comparing a pointer stays safe), with `p + n` counted in elements.
- In `unsafe` code: `p.read() -> T` (moves the value out of the memory),
  `p.write(sink v: T)` (moves it in, without destroying what was there),
  `p.destroy()` (destroys the value in place), `p.cast[U]()`, and
  `mem.view(p, n) -> []T` and an `inout` form, which make a slice of
  memory. A view made that way borrows from the function's parameters (the
  [view rule](#views-into-heap-types)), which the `unsafe` author promises
  is true.
- `size_of[T]()` and `align_of[T]()`, constant in each instance. The layout
  is LatticeFoundry's, known only when lowering, so they're not available
  to compile-time evaluation in M8.
- Memory an allocator returns isn't initialized. Only `unsafe` code holds it
  until it writes it, so the safe rule (every variable assigned before use)
  is unchanged.

### `Box[T]`

**Status:** Implemented (M8b); in the prelude, so `Box` needs no import
([Decision 11](#7-decisions))

An owning pointer: one `T` on the heap (memory.md,
[Owning pointers are values](memory.md#owning-pointers-are-values)).

```
let b = try Box.new(Point{x: 1, y: 2})   // uses alloc throws(AllocError)
let x = b.value.x                         // the boxed value, as a place
var c = try Box[u32].new(0)
c.value += 1                              // a var Box's value can change
bump(&c.value)                            // inout
let p = c.into_inner()                    // sink self -> T, frees the box
```

- `b.value` is the boxed `T` as a place: read like a field, assigned and
  passed `inout` when `b` is a place that can change. Nothing is implicit:
  `b.x` and `b.length()` are errors, with the fix `b.value.x`. Syntax
  Open (`b.value` or Zig's `b.*`).
- `Box[T]` needs destruction (it frees). It's `Clone` when `T` is.
- Recursive types through `Box` are allowed ([generics.md](generics.md#generic-types)).
  The generated destruction of a chain is a loop
  ([above](#destroying-recursive-structures)).
- `Box[dyn Trait]` waits for `dyn` (generics.md).

### `List[T]`

**Status:** Implemented (M8c), as `std/list`'s `List`, in the prelude; but
`insert` and `remove`, and the projection for `ArrayVec` and `StackBuf`
([M8c in the compiler](#m8c-in-the-compiler))

A growable array: a pointer, a length, a capacity, and the allocator it
came from.

```
pub struct List[T] {
	ptr: *T
	pub let len: usize where len <= cap
	pub let cap: usize
	alloc: alloc.Handle
}
```

API sketch:

| Method | Signature | Notes |
| --- | --- | --- |
| `new` | `fn List[T].new() -> List[T]` | Allocates nothing; remembers the context's allocator only at the first allocation. Doesn't need `uses alloc`. |
| `with_capacity` | `(n: usize) uses alloc throws(AllocError) -> List[T]` | |
| `push` | `(inout self, sink v: T) uses alloc throws(AllocError)` | Grows by doubling (`resize` in place first) |
| `push_within` | `(inout self, sink v: T) -> ?T` | No allocation: gives `v` back when full |
| `pop` | `(inout self) -> ?T` | |
| `insert`, `remove` | `(inout self, i: usize where i <= self.len, sink v: T) uses alloc throws(AllocError)`, `(inout self, i: usize where i < self.len) -> T` | Proven indexes, no `?` |
| `reserve` | `(inout self, n: usize) uses alloc throws(AllocError)` | |
| `truncate`, `clear` | `(inout self, n: usize)`, `(inout self)` | Destroys the removed elements |
| `get` | `(self, i: usize) -> ?T` where `T: Copy` | |
| `as_slice` | `(self) -> []T` | A view borrowing from `self` |
| `clone` | `(self) uses alloc throws(AllocError) -> List[T]` where `T: Clone` | |

`List.new()` not needing `uses alloc` lets a function that doesn't allocate
make an empty list and pass it to one that does. That `new` records the
context only on its first allocation follows from storing the allocator
with the memory.

**Indexing and slicing.** generics.md decides that no operator is
overloaded, and that's kept: `xs[i]` on a `List` means exactly `xs[i]` on
a slice of its elements. Options:

1. **Methods only**: `xs.as_slice()[i]`, and an `inout` view for
   `xs[i] = v`. Verbose for the most common container.
2. **A sealed projection**: a trait in std that only std implements
   (`Contiguous[T]`, name Open; sealed like `Integer`), whose impl gives the
   compiler a pointer and a length. For a value of such a type, the
   compiler treats `xs[i]`, `xs[i..j]`, `xs[i] = v`, `&xs[i..j]`, passing
   `xs` where a slice is expected (`&xs` for an `inout` one, as
   `slices.sort(&xs)`), and `for x in xs` as those operations on the view.
   No user code runs on `xs[i]`, and the meaning is the slice's.

**Recommendation: 2**, for `List[T]`, `ArrayVec[T, N]` and `StackBuf[N]`
(question 8). `xs.len` is the field (`pub let`), so `for i in 0..xs.len {
xs[i] }` is proven as for a slice.

**Views and growth.** `let s = xs.as_slice()` (or `for x in xs`) views the
list's memory, and `xs.push(v)` may move that memory. The
[view rules](memory.md#views) already forbid it: rule 2 says a returned
view borrows from the arguments, and the caller can't mutate or destroy
what it borrows from while the view is in use. `xs.push(v)` passes `xs`
`inout`, which is a mutation:

```
var xs = List[u32].new()
try xs.push(1)
let s = xs.as_slice()
try xs.push(2)              // error: `xs` is viewed by `s`, which is used below
io.print("{}\n", s[0])
```

This is what M8 must implement of rule 2; see
[Views into heap types](#views-into-heap-types).

### `String`

**Status:** Implemented (M8c), as `std/string`'s `String`, in the
prelude, with the differences in [M8c in the compiler](#m8c-in-the-compiler)
and [strings.md](strings.md#string)

An owned, growable UTF-8 string: strings.md's `String[utf8]`, named
`String` until `Str[E]` and `String[E]` exist (the step after M7 in
generics.md). It's a `List[u8]` that is always valid UTF-8, so its bytes
aren't a `Contiguous` projection (`s[i] = b` could break that).

| Method | Signature |
| --- | --- |
| `new` | `fn String.new() -> String` |
| `from` | `(s: str) uses alloc throws(AllocError) -> String` |
| `push_str` | `(inout self, s: str) uses alloc throws(AllocError)` |
| `push` | `(inout self, r: u32 where r <= 0x10FFFF) uses alloc throws(AllocError)` (a rune; surrogates checked or `?`, Open) |
| `as_str` | `(self) -> str`, a view borrowing from `self` |
| `len` | `pub let len: usize` (bytes) |
| `clear`, `truncate` | `truncate(inout self, n: usize) -> bool` (`false` if `n` isn't a character boundary) |

- `io.Format` for `String` writes its bytes; `io.Writer` for `String`
  appends, so `io.write_fmt(&s, "{} items", n)` builds a string, once
  `Writer`'s error type can be `AllocError` (it's `os.Error` today; a union
  `os.Error | AllocError`, or `Writer` gaining an associated `Error` type).
- `Eq` (bytes) and `Ordered` (bytes, which for UTF-8 is code point order).
- `String.from_bytes(sink b: List[u8]) -> ?String` (validates, no copy).

### `Map[K, V]`

**Status:** Proposed for after M8

A hash map needs a `Hash` trait (derived like `Eq`), a hash function
(SipHash-1-3 by default, against flooding; a faster one by choice), and an
answer for `get` on non-`Copy` values, which can't return a view in an
optional. Not part of M8; `List` and `String` come first.

### `Eq` on heap types

**Status:** Proposed; not in M8c

Generics' question 4 recommends that `Eq` is only ever derived. A derived
`==` on `List` would compare pointers. Recommendation: a type with a raw
pointer field gets no derived `Eq`, and std may write `impl Eq` for such a
type (`List[T: Eq]`, `String`, `Box[T: Eq]`), comparing the contents. User
types holding std containers then derive it.

### Views into heap types

**Status:** Implemented (M8c), with liveness found forward (the errors are
at the use after the change), in
[memory.md](memory.md#views-in-the-compiler-today)

Today a function can't return a view (except static `str`), and a slice of
a `var` array can only be passed to a function, never kept. `as_slice` and
`as_str` need rule 2: "A returned view borrows from the parameters. The
caller can't mutate or destroy what the view came from while the view is in
use." Proposed implementation, per function:

- **In the callee**: a function returning a view returns one that comes
  from a view parameter, from a parameter that owns memory (any non-`Copy`
  type), from a projection of one, or with static storage (today's rule
  for `str`). In `unsafe` code, a view made by `mem.view` counts as coming
  from all parameters.
- **In the caller**: a view local records the places its value borrows
  from: for a call, every argument that is a view or owns memory (the
  conservative rule memory.md states). A borrowed place can't be assigned,
  passed `inout` or `set`, moved, or destroyed (its scope can't end) while
  a view of it is **live**: used later on some path. Liveness is computed
  backwards over the function, as for any variable. It's not lexical: a
  view stops borrowing after its last use.
- The simpler rules of today (a slice of a `var` array can't be kept) are
  replaced by these; every program accepted today stays accepted.
- Views stay out of struct fields, so nothing crosses a function boundary
  but parameters and results: no lifetimes.

## 4. Proof checker

**Status:** Implemented (M8c) as recommended: `xs.len` is a term, `len <=
cap` a fact, no refinements of `inout` results, and `push_within` returns
`?T`; but `insert` and `remove`

- `xs.len` and `xs.cap` of a `List` local are integer fields of a struct
  local, which are already terms. With the sealed projection, `xs[i]`'s
  obligation is `i < xs.len`, discharged as for a slice: `for i in
  0..xs.len { xs[i] }` and `if i < xs.len { xs[i] }` need nothing new.
- The field refinement `len <= cap` is a fact about every `List`, so
  `xs.cap - xs.len` is proven.
- After `xs.push(v)` (`inout self`), the checker forgets what it knew about
  `xs`, as for any `inout` place. To keep `xs.len >= 1` after it, a result
  refinement would have to name the `inout` parameter's value on return
  (`-> () where self.len >= 1`). The fact language can say that (today a
  result's refinement must name `result`, so a function returning nothing
  can't have one), but not "one more than before" (no `old`). **Open:** whether to allow refinements
  on `inout` parameters' final values in M8; `reserve(n)` then `n` calls
  to `push_within` with a proof that none fails would need `old`, which
  the fact language doesn't have. M8 recommends without: `push_within`
  returns `?T`.
- `insert` and `remove` take refined indexes (`where i < self.len`), which
  the caller proves, so they don't return optionals.
- Refined element types (a `List[Digit]`, with `type Digit = u8 where
  self <= 9`, whose elements have the fact) need named refinements as type
  arguments, which aren't implemented: today `Digit` can't be part of
  another type.
- The checker learns nothing about heap contents beyond element types:
  elements have no facts, like array elements today.

## 5. Code size: pay only for what you use

**Status:** Implemented (M8a to M8d); the reference program is
`tests/programs/list_numbers.lode`, 12,330 bytes at `-O2`

- **No `uses alloc` reachable from `main`**: no allocator, no hidden
  parameter, no `mmap`. Hello world is unchanged: 577 bytes, `write` and
  `exit`. A test checks that its symbols contain nothing from `std/alloc`.
- **No type that needs destruction**: no destruction code, no drop flags.
  Destruction of a value whose type has nothing to release is nothing, at
  every level, including `-O0`.
- **Allocation without `with`**: no hidden parameter, direct calls into
  the root allocator, containers without the allocator word. Only the
  allocator's parts that are reached are linked: a program that never
  frees links no free lists, one that never grows links no `resize`.
- **With `with`**: one register per call to a `uses alloc` function, one
  word per container, a `match` over the program's allocator types per
  allocation, and the count of a counted allocator.
- Drop flags exist only for variables moved on some paths, and fold away
  when the paths are known.
- CI records the size of a reference program (a `List[u32]` filled from
  standard input and printed) next to hello world's, so changes to the
  allocator show up.

## 6. Implementation plan

**Status:** Proposed

Four steps, each shippable with tests, std changes and docs. Sizes are
rough estimates of compiler code (the compiler is about 35,000 lines). Each
step's tests run under `cargo test`; the ones about system calls use
`strace`-style counts as `tests/print_writes.rs` does.

### M8a: resource types, destruction and moves

**Status:** Implemented (2026-10-06): see
[M8a in the compiler](#m8a-in-the-compiler)

- Field visibility: `pub let`. (Private by default, `pub`, and literals
  of structs with private fields only in their package are done: std and
  tests have `pub` where fields are used across packages.)
- `fn T.deinit(sink self)`: declaration rules, generated destruction,
  `needs_deinit`, `is_copy` false for types that need destruction.
- Moves for every non-`Copy` type (`consume` beyond `Ty::Param`), pattern
  bindings as projections, `opt.take()`, `mem.swap`, `mem.replace`,
  `mem.take`, `mem.destroy`, `mem.forget`.
- Destruction at every exit, interleaved with `defer` (the `defers` stack
  in `src/lower.rs` gains the owned locals), drop flags, temporaries,
  assignment, `set` arguments; `defer` and `errdefer` that consume.
- Instances: `mono` substitutes and instantiates destruction per type.
- About 2,000 to 2,500 lines.
- **std gains:** `os.Fd`, an owned file descriptor closed by its `deinit`,
  with `os.open`, `os.close(sink fd) throws(os.Error)` (`io.stdout()` stays
  a plain, non-owning handle); `std/mem`; `ArrayVec[T, N]` without
  `T: Copy`. **Tests:** destruction order (a type whose `deinit` prints),
  every exit kind, conditional moves, use after move, `close` counted in
  system calls, `errdefer` consuming.

### M8a in the compiler

**Status:** Implemented (2026-10-06)

What M8a does, and the choices made where the proposal left room:

- **`pub let` fields** are read everywhere (with their refinements as
  facts) and assigned, passed with `&` or changed by an `inout self`
  method only in their package; a struct with one is built by a literal
  only there ([types.md](types.md#structs)). `os.Fd` has `pub let fd`.
- **`deinit`.** `fn T.deinit(sink self)` on a struct or an enum: `sink
  self` and nothing else, no result, no `throws`, not `unsafe`, no
  generic parameters or bounds of its own (every instance is destroyed).
  Each is an error otherwise. Calling it directly is an error too. In its
  body, `self` can't be moved; when the body ends, the fields that aren't
  `Copy` are destroyed, last first (for an enum, the variant's payload),
  as a `defer` registered first. A type with a `deinit` isn't `Copy`, nor
  is what holds one (a field, a payload, an element, an optional).
- **What can't hold a resource.** A constant's type must be `Copy` (a
  constant is copied where it's used), and so must an error type (`catch
  v` and `catch _` drop the error). A `catch` statement whose call
  returns a value that isn't `Copy` is an error: on success, the value
  would be lost.
- **Moves** extend M7a's to every type that isn't `Copy`: keeping a value
  read from a `let`, a `var` or a `sink` parameter moves it, and the
  variable is unassigned until assigned again, on every path, loops
  included ("`f` is used after it was moved (on some path to here)").
  Keeping a read-only, `inout` or `set` parameter, or an element, is an
  error that says which type isn't `Copy` and why ("`Fd` has a `deinit`:
  its values are moved, never copied"). In the typed tree, the kept value
  is a `Move` of the variable, which clears its drop flag.
- **No partial moves.** Keeping a field moves the whole variable, which
  is allowed only when the rest of it is `Copy` and no `deinit` holds it:
  `return t.n` from a `Tagged{n: Fd, tag: u32}` is fine, from a `Two{a:
  Fd, b: Fd}` it's an error with the fix (`mem.replace(&t.a, v)`). So
  M7b's `fn Pair[A, B].into_first(sink self)` needs `B: Copy` now. A part
  of a temporary moves the temporary the same way (`f().n`).
- **Pattern bindings read in place.** A binding of `match` or `if let`
  whose type isn't `Copy`, and the variable of `for x in xs`, are
  projections: reading them needs nothing, and keeping one moves what it
  reads, which must be a value the code may consume (a `let`, `var` or
  `sink` variable, or a temporary scrutinee). Moving or changing that
  value makes the bindings unusable after, right from the change: for a
  `for` element, a change of the list or the slice it goes over, or of
  what that slice views ([memory.md](memory.md#views-in-the-compiler-today)).
  A `for` element can't be kept
  (it's an element). `let ... else` moves the optional's value into its
  new variable, which owns it. A `match` on another place that isn't
  `Copy` (`match p.opt`) reads it in place too.
- **Destruction** runs at every exit of a block, where `defer` bodies run,
  interleaved with them in reverse order: lowering's stack of `defer`s
  holds the variables that own a value (`TStmt::Drop`). A `return`
  computes its value first. A call of a `never` function destroys
  nothing. An assignment computes the new value, then destroys the old
  one (a local, a field, an element, an `inout` parameter's value). The
  elements of an array are destroyed first to last, the fields of a
  struct last to first.
- **Drop flags.** A variable gets one when it may be unassigned where it's
  destroyed or assigned: moved anywhere, declared without a value, a `set`
  parameter, or a temporary. That's a little more than "moved on some
  paths": a variable always moved has one too, and the optimizer folds it
  (at `-O2`, nothing of it is left). At `-O0` it's a byte and a test.
- **Temporaries.** A value that isn't kept (a call's result passed to a
  read-only parameter, a field read from it, a method called on it, a
  statement's value, a side of `==`) is stored in a hidden local and
  destroyed when its statement ends, or at an exit before. The ones made
  in a `while` condition are destroyed when the next one is made, and the
  last after the loop. A `match` or `if let` on a value that isn't a
  variable owns it until the statement ends.
- **`set` arguments** that aren't `Copy` must not hold a value: a variable
  that does on every path is an error. One that holds a value on some
  paths only keeps the old value, which leaks.
- **`defer` that moves.** A `defer` or `errdefer` body may move a variable
  declared outside it; at each exit it runs at (the block's end, `break`,
  `continue`, `return`, and for `errdefer` only `throw` and a failed
  `try`), the variable must be assigned, or it's an error at that exit.
  After the exit, it's unassigned. A variable the body only uses is
  checked the same way, and so is one used or moved by an earlier
  `defer` that a later one moves (the later one runs first): reading a
  variable moved after the `defer` read freed memory
  ([memory.md](memory.md#views-in-the-compiler-today)).
- **Instances.** `mono` makes the destruction of each concrete type that's
  destroyed: its `deinit`'s instance, or a function made for it
  (`main.Pair[main.Fd, u8].$destroy`) that destroys its parts. For an
  instance whose type needs no destruction, the checker's moves,
  temporaries and destructions are removed: code without resource types
  is unchanged (each program of tests/programs is byte for byte the same,
  or smaller, below).
- **A `sink` parameter in memory** that the callee never changes (no
  assignment, no `&`, no `inout self` call on it) is read in place, like a
  read-only one, without the copy on entry: the caller's value moves in,
  or can't change during the call (exclusivity). Several programs are
  smaller for it.
- **`Clone`** is a built-in trait, beside `Eq` and `Copy`: a `Copy` type's
  clone is the copy (`T: Copy` implies `T: Clone`); a struct, an enum, an
  optional or an array without a `deinit` whose parts are `Clone` gets one
  that `mono` makes (`$clone`), cloning each part; any other type writes
  `impl Clone for T { fn clone(self) -> T }` (an impl for a `Copy` type is
  an error). `x.clone()` reads `x` in place. Generic code bounds `T:
  Clone`.
- **The compile-time evaluator** runs moves, `mem` and `clone()` as they
  run in a program, but destroys nothing: a value made while compiling
  holds no resource, and the only effects a `deinit` could have there are
  its failures.
- **The proof checker** forgets what it knew of a variable that's moved
  (it's unassigned), as it does for any assignment. Destruction changes
  no facts about the variables still alive: a `deinit` sees only `self`.
  A `deinit`'s body is checked like any method's.
- **std.** `std/mem` (`swap`, `replace`, `take`, `destroy`, `forget`;
  `swap`, `take` and `forget` are `@intrinsic`, implemented by the
  compiler, which only the standard library can declare); `os.Fd`,
  `os.open`, `os.close(sink f) throws(os.Error)` and the `O_*` flags;
  `vec.ArrayVec[T, N]` of any `T`
  ([packages.md](packages.md#the-standard-library-in-the-compiler-today)).
  `io.File` stays a non-owning handle: `io.stdout()` is one, and
  `io.File.from_fd(f.fd)` reads and writes an `os.Fd`.
- **Sizes.** Hello world is still 577 bytes and two system calls at
  `-O2`. Of the 89 runnable programs, 85 are byte for byte the same at
  `-O0` and `-O2`, and 4 are smaller (`generic_methods`,
  `generic_optionals`, `std_containers`, `trait_ordered`: 96 to 450
  bytes less), from the `sink` parameters read in place.
- **`opt.take()`** on an optional that can be changed gives its value and
  leaves `none`, as `mem.take(&opt)` does. **`needs_deinit[T]()`** is a
  `bool` known in each instance: whether destroying a `T` does anything.
- **Not done in M8a.** `match &x` (bindings that are `inout`
  projections), raw pointer fields (M8b). A value built into a literal or
  into a call's arguments before a `try` in the same expression fails
  leaked, as did a `set` parameter the callee assigned before it threw:
  their `deinit` didn't run, which is safe. M8b destroys both, once.

### M8b: the allocator context, the root allocator and `Box`

**Status:** Implemented (2026-10-06): see
[M8b in the compiler](#m8b-in-the-compiler)

- Parser and checker: `uses alloc` on functions and trait methods, the
  check at calls, `with alloc = h { }` (only in `uses alloc` functions).
- Lowering: the hidden parameter; the whole-program rule that drops it and
  makes handles zero-sized when no `with` is reachable; closed-world
  dispatch otherwise; the root allocator installed for a `main` that
  `uses alloc`.
- The unsafe toolkit: `*T`, pointer fields, `read`, `write`, `destroy`,
  `cast`, `mem.view`, `size_of`, `align_of`.
- `Box[T]` and `b.value`, and the generated loop for chains.
- About 2,500 lines.
- **std gains:** `os.mmap`, `munmap`, `mremap`, `os.PageAllocator`;
  `std/alloc` with `Allocator`, `AllocError`, `Handle`, and `Heap`
  (size classes); `Box`. **Tests:** a linked list of a million nodes built
  and destroyed with a constant stack, `--stack-usage` bounded, hello world
  size and syscalls unchanged, a function without `uses alloc` calling one
  with it rejected.

### M8b in the compiler

**Status:** Implemented (2026-10-06)

What M8b does, and the choices made where the proposal left room:

- **`uses alloc`** comes after the parameters, before `throws`: `fn
  read(f: File) uses alloc throws(AllocError) -> T`. A call of a function
  that declares it, in one that doesn't, is an error with the fix ("`f`
  allocates (`uses alloc`), so it's only called by a function that
  declares `uses alloc`"). A trait's method declares it too, and an
  impl's may leave it out, not add it. A `deinit` can't declare it, and a
  constant's value can't call such a function. `uses` takes only `alloc`.
- **`with alloc = h { ... }`** is only allowed in a function that declares
  `uses alloc`, with `h` an `alloc.Handle`. It's an ordinary block:
  `defer`, destruction and every exit work as in any block, and the
  context is the outer one again after it. A `defer` body runs in the
  context it's written in, also at an exit from inside a `with` block.
- **Handles** (`std/alloc`). `alloc.current()` (`uses alloc`, and
  `unsafe` since M8d) is the context's; `alloc.root()` the root allocator's; and `unsafe
  alloc.handle(a)` one of the allocator `a`, a struct or an enum: its
  caller promises that `a` outlives what it allocates and doesn't move,
  which a `static` does. Counted allocators came with M8d. `h.alloc(size, align)` and `h.resize(...)` declare `uses
  alloc` too, so a function without it allocates through no handle
  either; `h.free(...)` doesn't, as destruction needs no context.
- **`Allocator`** is an `unsafe trait` (`unsafe impl` implements one, and
  only one): `alloc(self, size, align) throws(AllocError) -> *u8`, and
  `resize` and `free`, which are `unsafe fn`: their caller promises the
  block is one the allocator gave. `AllocError` (`out_of_memory`) is built
  in, like `Ordering`: usable without an import.
- **Lowering.** The program's allocator types are the root's and each
  type an `alloc.handle(a)` in the instances `main` reaches makes a handle
  of. With the root's only, `alloc.Handle` has no fields (a box is one
  pointer), a `uses alloc` function takes no hidden parameter, and a call
  through a handle is a direct call of the root's method, with `alloc.ROOT`
  as `self`. Otherwise a handle is two words, its type's number among the
  allocator types and its address; a `uses alloc` function takes the
  address of the handle in context as a last hidden parameter, which
  `main` makes the root's and `with` replaces; and a call through a handle
  calls a function `mono` makes (`std/alloc.Handle.$alloc`) that tests the
  number and calls the type's method directly. This is a little finer
  than "no `with` reachable" (`with alloc = alloc.root()` adds no type),
  and the handle isn't the proposal's one pointer to a control block
  whose first word is the type: control blocks come with counted
  allocators (M8d).
- **The root allocator** is `alloc.ROOT`, a `static` of type `alloc.Heap`,
  all zeros, in `.bss`: nothing runs before `main`, and its first
  allocation maps its first chunk. A block of at most 2048 bytes is of
  the smallest size class that holds it (16 to 2048 bytes, powers of
  two), aligned to its size, from the class's list of freed blocks (last
  in, first out) or else carved from the current 64 KiB chunk; a larger
  one is a mapping of its own (`os.PageAllocator`), unmapped when it's
  freed. `resize` keeps a block in its class, or remaps a large one in
  place. Chunks are never unmapped. There's one heap: its methods change
  `ROOT` in place, and an allocator built on it calls them directly
  (`alloc.ROOT.alloc(size, align)`, in `unsafe` code). `@root_allocator`
  isn't there yet: the root is always the heap.
- **std/os** gains `mmap`, `munmap` and `mremap` (`unsafe`, with the
  system call numbers of x86-64 and AArch64), `PAGE_SIZE`, and
  `PageAllocator` (`map`, `unmap`, `remap`). Its `Allocator`
  implementation is in `std/alloc`, the trait's package: `std/alloc`
  imports `std/os`, which can't import it back.
- **Raw pointers** point to any type but a view: `*T` can be a struct
  field, a payload field, an element or an optional's value. Holding,
  copying and comparing one, and `p.addr()`, are safe; `p.read()` (moves
  the value out), `p.write(v)` (moves `v` in, destroying nothing),
  `p.destroy()`, `p.cast[U]()`, `p + n` (`n` elements) and
  `mem.from_addr[T](a)` are `unsafe`. A struct or an enum holding a raw
  pointer (or an array or an optional of one) isn't `Copy`, `Eq` or
  derived `Clone`: its author writes what it needs. `s.ptr` works for
  arrays and slices of any type. `size_of[T]()` and `align_of[T]()` are
  `usize`s LatticeFoundry's layout gives each instance, not known when
  compiling. `mem.view` comes with M8c, which returns views.
- **`static NAME: T = value`**, `pub` or not: a global, initialized when
  compiling like a constant, of a `Copy` type a constant can have. Every
  use is `unsafe` (memory.md: a plain mutable global is only for `unsafe`
  code): read, assigned (in its package), passed with `&`, or a method's
  receiver. It's in `.bss` when its value is all zeros, otherwise in
  `.data`; a constant can't read one.
- **`Box[T]`** is `alloc.Box`, a struct of `ptr: *T` and `alloc: Handle`:
  `alloc.Box.new(v) uses alloc throws(AllocError)` (`v` is destroyed if
  it fails), `b.into_inner()` (the value, the box freed), and a `deinit`
  that destroys the value and frees it through the box's handle.
  `b.value` is the boxed value as a place, which the box's variable makes
  changeable or not (`var b`): `b.value.x = 1`, `bump(&b.value)`. Moving
  out of it is an error (`into_inner`, or `mem.replace(&b.value, v)`),
  and `b.x` and `b.f()` are errors whose help is `b.value.x`. It's
  `Clone` when `T` is (`impl[T: Clone] Clone for Box[T]`), and never
  `Eq` yet.
- **Chains.** A struct without a `deinit` with exactly one field of type
  `?Box[Self]` is destroyed by a loop: it destroys the other fields, takes
  the link, reads the node out of its box, frees the box through its
  handle, and goes on with the node's link. No function on the way
  destroys a box of the struct, so the call graph has no cycle and the
  program has a stack bound, at `-O0` too. A million nodes are destroyed
  with the same stack as one. Other recursive types (two links, an enum)
  still recurse.
- **`Clone`** declares `uses alloc throws(AllocError)`: `x.clone()` of a
  type parameter needs both (`try x.clone()` in a `uses alloc` function).
  A type with an `impl Clone` has its impl's signature, which may leave
  both out; a derived clone allocates and throws when a part's does.
  Where generic code expects a result and the instance's clone can't
  fail, `mono` makes it give `ok` (a copy, or the impl's `clone` made to
  throw).
- **M8a's destruction gaps are closed.** (1) While an array literal, a
  struct literal, a variant or a call's `sink` arguments are built, the
  parts already built that need destruction are registered like a
  `defer`, until the value is complete: an early exit in a later part (a
  failed `try`, a `throw` after `??`, a `catch` block that leaves)
  destroys them once. A literal returned in memory is built aside first
  when one of its parts may leave, so the exit doesn't destroy what the
  error was written over. (2) In a function that throws, a `set`
  parameter of a type that isn't `Copy` is destroyed when the function
  leaves with an error, if it was assigned (its drop flag says): the
  caller's variable isn't assigned then.
- **Sizes.** Hello world is still 577 bytes and two system calls at
  `-O2`. Of the 94 programs that ran before M8b, 93 are byte for byte the
  same at `-O0` and `-O2`; `clone_mem`, whose generic clone now throws,
  changed its source (8,978 bytes at `-O2`, from 7,282). Importing
  `std/alloc` and declaring `uses alloc` in a program that doesn't
  allocate changes nothing. A program that boxes a `u32` is 2,872 bytes at
  `-O2`, with two system calls (`mmap` of one chunk, `exit`) and a stack
  bound of 368 bytes; `alloc_chain.lode` (a million boxes) is 6,496
  bytes, `box.lode` 15,911 and `alloc_with.lode` (another allocator, so
  handles and a hidden parameter) 12,024.
- **Not done in M8b.** `mem.view` (M8c); `@root_allocator`; counted
  allocators, so `alloc.handle` is `unsafe` (M8d); the iterative
  destruction of chains through an enum. The prelude came just after.
- **The prelude** (Decision 11), after M8b: `Box` names `alloc.Box`
  without an import, in every package, unless a local, an item of the
  package or an import of that name hides it. Loading `std/alloc` into
  every program would load `std/os`, which compiles only for Linux, and
  break `lode check --targets` for programs that don't allocate; so the
  prelude is lazy: the loader loads `std/alloc` only for a package whose
  tokens may use `Box` (an identifier not after a `.`, in a file that
  doesn't import a package as `Box`, in a package that doesn't declare
  `Box`). The scan is conservative (a local named `Box` counts) and the
  same for every target. A program that doesn't name `Box` loads and
  builds exactly as before: hello world is 577 bytes, and checks for
  `wasm32` and `avr`. One that does, checked for those, gets `std/os:
  unsupported target`. The rules are in
  [packages.md](packages.md#the-prelude); the table, one line per name, is
  `src/prelude.rs`, where `List` and `String` go when M8c adds them.

### M8c: views from functions, `List` and `String`

**Status:** Implemented (2026-10-06): see
[M8c in the compiler](#m8c-in-the-compiler)

- Rule 2 of views: returned views, the borrow sets of view locals,
  liveness, the errors at mutations; today's simple rules removed.
- The sealed projection: `xs[i]`, slicing, `&xs`, `for`, `xs.len` terms on
  `List`, `ArrayVec` and `StackBuf`.
- `impl Eq` for types with pointer fields (std only).
- About 2,500 to 3,000 lines (rule 2 is most of it).
- **std gains:** `List[T]`, `String`, `Clone`, `io.Format` and `io.Writer`
  for them; `fn String.as_str`, `fn List.as_slice`; `slices.sort(&xs)` on a
  list. **Tests:** the growth example above rejected, `as_slice` kept
  across reads, proven indexing over `xs.len`, a word-count program reading
  standard input, `mremap` growth counted in system calls.

### M8c in the compiler

**Status:** Implemented (2026-10-06)

What M8c does, and the choices made where the proposal left room:

- **Rule 2 of views** ([memory.md](memory.md#views-in-the-compiler-today),
  where the exact rule is). Functions return slices and `str`s that borrow
  from their read-only and `inout` parameters. Each view local has roots,
  the variables it may view: for a call, every argument that can lend
  storage and isn't passed `sink` or `set` (the conservative rule), so the
  caller needs nothing from the callee but its signature. A change of a
  root (assigned, passed `&`, an `inout self` receiver, moved) makes the
  views of it unassigned, as a move does, in the checker's
  definite-assignment state: using one afterwards, on some path, is an
  error at the use that points at the change. That's the proposal's rule
  ("a borrowed place can't change while a view of it is live") found
  forward, not by a backward liveness pass: a change followed by a use is
  exactly a change while the view is live. The error is at the use,
  rather than at the change; the message names both. A loop whose body
  adds roots to a view declared before it is checked again, as one that
  moves a variable is (`Checker::loop_body`), so a change in one iteration
  reaches the next one's use. In one expression, exclusivity counts a view
  as using its roots. `src/sema/views.rs` has it all.
- **Today's simple rules are gone.** A slice of a `var` array can be kept,
  and the array changed after the slice's last use; a `str` that borrows
  from a parameter can be returned. The static-`str` rule is the case of a
  view with no roots. Two rules stay: a view can't be kept from a
  temporary, or copied out of an `inout` slice (its elements change
  during the call). Two are new: a view can't borrow from a variable of a
  deeper block than its own (before, a `var` slice could keep a view of a
  `let` array of an inner block after the block ended: a bug), and a
  `defer` body can only use views of what can't change (read-only
  parameters, `let` variables of `Copy` types). Every other program
  accepted before is still accepted.
- **Roots are whole variables**, not places: changing `p.tag` stops a view
  of `p.rows`. Places would need the paths exclusivity uses; nothing
  needed them yet.
- **`mem.view(p, n)` and `mem.view_str(p, n)`** (`unsafe`, `@intrinsic`)
  make a slice or a `str` of memory; their result borrows from every
  parameter that can lend. A function that throws still can't return a
  view (its result would hold one in memory).
- **The projection** (Decision 8). Rather than a sealed trait, the
  compiler knows `std/list`'s `List` (as it knows `alloc.Box`): for a
  value of it, `xs[i]`, `xs[i..j]`, `for x in xs`, `xs` where a slice is
  expected, and `&xs` or `&xs[i..j]` where an `inout` slice is expected,
  are those operations on `TExprKind::Elements(xs)`, the slice of its
  `len` elements from its `ptr`, read from the list once. Its length is
  the term `xs.len` when `xs` is a variable or a field of one, so `for i
  in 0..xs.len { xs[i] }` and `if i < xs.len { xs[i] }` are proven as for
  a slice. `xs[i] = v` changes an element of a `var` list (destroying the
  old one); an element isn't moved out (`mem.replace(&xs[i], v)`), as an
  array's. Inference sees a list's elements where a slice is expected:
  `slices.sort(&xs)`. `ArrayVec` (whose slots are `?T`) and `StackBuf`
  don't have the projection yet: a trait in std that says which fields
  are the pointer and the length would replace the compiler's knowledge
  of `List` when they do.
- **`List[T]`** (`std/list`) is `ptr: *T`, `pub let len: usize where len
  <= cap`, `pub let cap: usize` and the handle of its allocator. `new`
  allocates nothing and holds the root's handle; the first allocation
  takes the context's (`alloc.current()`), and growing and freeing go
  through the list's own handle after that, wherever the list is. It
  grows by doubling, at least to 4, with `Allocator.grow`. `push`,
  `push_within`, `extend` (`T: Copy`), `reserve`, `with_capacity`, `pop`,
  `get` (`T: Copy`), `as_slice`, `truncate`, `clear`, `Clone` for `T:
  Clone`; its `deinit` destroys the elements, first to last, and frees.
  After a call that changes it, the checker knows nothing of its fields
  (an `inout` place), so `push` checks `len < cap` again after growing:
  one comparison, which `grow` makes always true. `insert` and `remove`
  aren't there yet.
- **`String`** (`std/string`) is `pub let bytes: List[u8]`: its bytes are
  read everywhere (`s.bytes.len`, `s.bytes[i]`) and changed only in
  `std/string`, so the UTF-8 invariant needs no projection rule. Its
  length is `s.len()`, a method, rather than the proposal's `pub let
  len`, which would have duplicated `List`'s growth. `from`, `push_str`,
  `push` (a character, `false` for a surrogate or past `0x10FFFF`),
  `as_str` (with `mem.view_str`), `reserve`, `truncate` (at a character's
  start), `clear`, `Clone` and `io.Format`. It's an `io.Writer` that
  appends within its room, since a `Writer`'s methods can't declare
  `uses alloc`, and refuses bytes that aren't UTF-8;
  `string.write_fmt(&s, fmt, args...)` and `string.format(fmt, args...)`
  format twice, to count and then to write, and allocate in between. `==`
  and `Ordered` wait for `impl Eq` on types with pointer fields.
- **`Allocator.grow`**, a fourth method with a default (`resize`, or
  `alloc`, a copy and `free`), dispatched like the others
  (`std/alloc.Handle.$grow`); `Heap` and `os.PageAllocator` grow a large
  block with `mremap(MREMAP_MAYMOVE)`. Mappings are made top-down, so
  growing one in place almost never works: before `grow`, a list growing
  to 1 MiB made three system calls and a copy per doubling; now one
  `mremap` (tests/allocation.rs).
- **The prelude** has `List` and `String`.
- **Sizes.** Programs that don't use them are unchanged: each of the
  runnable programs of tests/programs is byte for byte the same at `-O0`
  and `-O2` as before M8c, and hello world is 577 bytes and two system
  calls. `list_numbers.lode` (a `List[u32]` from standard input, sorted
  and printed) is 12,330 bytes at `-O2`; a program pushing a million bytes
  into a `List[u8]` is 7,128 bytes and makes 11 memory system calls (one
  chunk, one mapping, eight `mremap`s and the `munmap`).
- **Not done in M8c.** `impl Eq` for types with pointer fields (so no
  `==` on `List` or `String`), `List.insert` and `remove`, the projection
  for `ArrayVec` and `StackBuf`, `String.from_bytes`, roots finer than
  variables, refinements of a returned view's length (`-> []T where
  result.len == self.len`), and narrowing a result's roots (`-> str from
  s`, still Open).

### M8d: error-set unions, the `oom` policy and arenas

**Status:** Implemented (2026-10-07): see
[M8d in the compiler](#m8d-in-the-compiler)

- `throws(A | B)`, conversion on `try`, matching by member type; empty
  members dropped.
- `@oom(abort)`: `AllocError` empty, the root allocator aborting, `try` on
  calls that can't throw allowed for that reason.
- Counted allocators: the count in the allocator interface, `alloc.Arena`,
  `alloc.Counted[A]`, a fixed buffer over a `static` array as root.
- About 1,500 lines.
- **std gains:** `Arena`, `Counted`, `FixedBuf`; `io.Writer` for
  `String` with a union error. **Tests:** the same library function
  compiled under both policies; an arena outliving its owner while a value
  from it is alive (freed by the last `free`, checked by counting `munmap`);
  `with` inside `with`.


### M8d in the compiler

**Status:** Implemented (2026-10-07)

What M8d does, and the choices made where the proposal left room:

- **Error-set unions.** `throws(A | B)` (two or more error types, each
  named once) is a union: an enum the compiler makes, with one variant
  per member, named as the member is shown (`ParseError`, `os.Error`),
  whose one payload field is the member's value. The variants are sorted
  by name, so `A | B` and `B | A` are the same type. A member can't be a
  type that depends on a type parameter yet. The rest is in
  [errors.md](errors.md#in-the-compiler-today): `try` converts a member,
  or a smaller union, into the caller's union (and nothing else); a
  member's value converts to the union where the union is expected
  (`throw ParseError.empty`); `.name` takes the variant of the one member
  that has it; `match` names a member by its type (`ParseError(p) =>`,
  `os.Error(e) =>`). The conversion is a `catch` that rethrows, which the
  checker writes: a union's tag, then the member's, so lowering and packed
  results are unchanged.
- **Unions are flat.** The proposal left open whether a union's value
  holds the member (`.alloc(e)`) or every member's variants side by
  side. It holds the member: two members can have variants of the same
  name (`os.Error.io` and a user's `io`), the conversion of a member is
  one tag, and code that handles one member passes its value on as it
  is. Matching a variant through a union is a `match` in a `match`.
- **`@oom(abort)`**, alone on a line in the main package, sets the
  policy; `@oom(error)` is the default, and setting it twice is an
  error, as is `@oom` in another package. With `abort`, `AllocError`
  never happens, but the checker sees the same types under both
  policies, so the same source checks the same way: `AllocError` keeps
  its variant, and making one (`throw .out_of_memory`) calls
  `alloc.out_of_memory()`, which writes `out of memory` to standard error
  and ends the process with status 134 (`os.abort()`). `crate::mono`
  applies the policy: a function that throws only `AllocError` doesn't
  throw; `try` and `catch` on a call of one are the call; where a result
  is still expected (a `match` on the call), it's always `ok`. So the
  "empty enum" of the proposal is an enum whose value is never made.
- **What `abort` allows.** A call that throws only `AllocError` may be
  left without `try` (`xs.push(5)`), and `try` drops `AllocError` from a
  union: `try` on a `throws(ParseError | AllocError)` call passes on
  `ParseError` from a `throws(ParseError)` function. A `try`, `catch` or
  `match` on a call that can't fail any more is allowed, without a
  warning. The union keeps its `AllocError` member (its value is never
  made), so a `match` on it has the same arms under both policies.
- **Counted allocators** (`std/alloc`). A **control block** holds an
  allocator `A` and what releasing it needs; it's on the memory of the
  allocator in context when it's made, in one block with a **count**
  before it: the live allocations, plus one for the owner. `alloc` adds
  one, `free` takes one; the last to end (the owner's `deinit`, or the
  last `free`) destroys `A` and frees the block. A handle of a counted
  allocator names its control block, an allocator type of the program
  like any other (`alloc.handle_at(p)`). `alloc.Counted[A]` is the owner
  of any allocator counted so; `alloc.Arena` is a counted bump
  allocator (chunks of 4 KiB, doubling to 1 MiB, from its parent; it
  gives back only its last block, `reset()` reuses its memory once
  nothing from it is alive). An arena made in an arena is one of its
  allocations. Each allocation through a counted handle costs an
  increment, each free a decrement and a test.
- **`with alloc = arena`.** The proposal's safe `arena.handle()` would
  be a `Copy` value that can outlive the arena: kept in a variable after
  the arena is destroyed, it would allocate from freed memory. So a
  handle of a counted allocator isn't a value safe code gets:
  `Arena.handle()` and `Counted.handle()` are `unsafe`, and so is
  `alloc.current()`. Safe code gives the counted allocator itself, a
  variable: `with alloc = arena { ... }`. The block borrows it, as a
  view borrows what it views ([memory.md](memory.md#views-in-the-compiler-today)):
  a call that allocates (`uses alloc`) after the arena changed or moved,
  on some path in the block, is an error that points at the change; so
  is a call that allocates while it changes or takes the arena (`f(&arena)`,
  `f(arena)`). A `defer` body in the block can't allocate from it (it
  runs at the block's exits, after the arena may have changed). Changing
  the arena after the block's last allocation is fine. What the block
  allocated keeps the arena's memory alive wherever it goes: returned,
  stored through `inout`, kept by a `defer`.
- **Containers keep a counted allocator alive** by their allocation:
  `List`, `String` and `Box` hold their allocator's handle with the
  memory they got from it, until they free it. A handle is only taken
  from the context inside `std` (`alloc.current()`, now `unsafe`) by a
  container that allocates through it at once.
- **Fixed buffers.** `alloc.FixedBuf` carves blocks from memory the
  caller gives (`unsafe fn FixedBuf.new(p, n) -> ?FixedBuf`, its state
  in the first 32 bytes). It's not counted: over a stack array it ends
  with its frame. `with alloc = f` is an error; `unsafe` code makes its
  handle, `alloc.handle(f)`, and promises that nothing it allocates
  outlives the buffer. Over a `static` array it never ends.
  `@root_allocator` (a fixed buffer as the root) isn't there yet.
- **Allocators built on others.** An allocator's methods don't declare
  `uses alloc`, so they take memory from their parent with `unsafe
  h.raw_alloc(size, align)`, which is `h.alloc` without the context.
- **std.** `alloc.Counted`, `Arena`, `FixedBuf`, `handle_at`,
  `Handle.raw_alloc`, `out_of_memory`; `string.print_to(f, fmt, args...)`
  (formats into a `String`, then one write) and `string.read_all(f, &out)`
  (reads a file to its end into a `List[u8]`), which throw
  `os.Error | AllocError`. `io.Writer` for `String` still doesn't
  allocate: a trait method can't declare `uses alloc` that its trait
  doesn't, and `io.Writer`'s methods don't.
- **Sizes.** Hello world is 577 bytes and two system calls at `-O2`.
  Every runnable program of tests/programs from before M8d is byte for
  byte the same at `-O0` and `-O2` (216 builds), including the ones that
  allocate: `list_numbers.lode` is 12,330 bytes. The same program (a
  list of squares, `tests/allocation.rs`) is 9,209 bytes under the
  default policy and 8,023 under `@oom(abort)` at `-O2`, where `push`
  returns nothing. `arenas.lode` is 45,760 bytes; destroying an arena
  while a list from it lives unmaps nothing, and the list's destruction
  unmaps the arena's chunk (checked under `strace`).
- **Not done in M8d.** Members of a union that depend on a type
  parameter; a union converted to another by `throw e` (only `try`
  converts); `io.Writer` for `String` with a union error;
  `@root_allocator`; inferred error sets.

After M8: `Map[K, V]`, linear types if wanted, `Box[dyn Trait]`, the region
check for stack buffers, refinements on `inout` results, allocation at
compile time (an evaluator heap whose values can't be a constant's value).

## 7. Decisions

**Status:** Decided 2026-10-06 by the user for 3 (with `pub let`), 5, 8 and
11; the others keep the recommended answer unless the user changes them.
M8a implements 1, 2, 3, 9 and 10 as written. M8b implements 4, and the
context's part of 6 with a handle of two words. The prelude implements
11, with `Box`, and M8c adds `List` and `String` to it; M8c implements 8
for `List`. M8d implements 5, the policy's part of 6, and 7.

1. **Destruction is a method, `fn T.deinit(sink self)`**, not a `Drop`
   trait; it can't throw or allocate
   ([Declaring destruction](#declaring-destruction)). *Recommended;
   implemented (M8a).*
2. **Conditional moves use drop flags**, so destruction is always at the
   scope's end ([Moves](#moves)). *Recommended; implemented (M8a).*
3. **Fields are private to their package by default**, with `pub` and
   `pub let` (read-only outside), and literals of structs with private
   fields only in their package ([Field visibility](#field-visibility)).
   *Decided; implemented* (`pub let` in M8a).
4. **Containers store their allocator**, a word that's zero-sized when the
   program never uses `with`
   ([Who frees](#who-frees-containers-remember-their-allocator)).
   *Recommended; implemented (M8b): zero-sized when the program has no
   allocator type but the root's.*
5. **Allocators that can end are counted** (option C): an arena's memory
   lives until its last allocation is freed; stack-backed buffers aren't
   `with` allocators in safe code
   ([Allocators that end](#allocators-that-end-arenas-and-fixed-buffers)).
   This is the main safety decision of M8. *Decided; implemented (M8d):
   `alloc.Counted[A]`, `alloc.Arena`; `alloc.FixedBuf` only through
   `unsafe` code.*
6. **The context is a hidden parameter** of `uses alloc` functions only,
   omitted when no `with` is reachable, and dispatched over the program's
   allocator types otherwise ([Lowering](#lowering-the-context)); **the
   `oom` policy is `@oom(abort)` in the main package**, default `error`
   ([Out of memory](#out-of-memory)). *Recommended; the context is
   implemented (M8b), the policy too (M8d).*
7. **Error-set unions `throws(A | B)` come in M8**, explicit, without
   inference ([Out of memory](#out-of-memory)). *Recommended; implemented
   (M8d).*
8. **`xs[i]` works on `List`** through a sealed, std-only projection to a
   slice, consistent with "no operator overloading" because it means
   exactly slice indexing ([`List[T]`](#listt)). *Decided; implemented
   (M8c) for `List`, which the compiler knows by name, as it knows `Box`.*
9. **The explicit copy is `x.clone()`** from a `Clone` trait, rather than
   memory.md's `x.copy()` ([Explicit copies](#explicit-copies)).
   *Recommended, weakly: a naming choice; implemented (M8a).*
10. **No linear types in M8** ([Linear types](#linear-types)).
    *Recommended; M8a has none.*
11. **A small prelude**: `Box`, `List`, `String`, `AllocError` and the
    built-in traits usable without an import, from `std/core`, rather than
    `list.List[u32]` everywhere. *Decided; `AllocError` is built in (M8b),
    `Box` is in the prelude, whose packages are loaded only by the
    programs that use their names ([packages.md](packages.md#the-prelude));
    `List` (`std/list`) and `String` (`std/string`) joined it with M8c.
    There's no `std/core`: each name comes from the package that declares
    it.*
