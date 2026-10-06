# Allocation and heap types (M8 proposal)

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

Everything here is **Proposed** unless a section says otherwise. Nothing is
implemented yet.

## Starting point

**Status:** Implemented (what the compiler does today)

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

**Status:** Proposed

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

Existing code is unaffected: no type needs destruction today.

### Declaring destruction

**Status:** Proposed

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

**Status:** Proposed

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

**Status:** Proposed

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

**Status:** Proposed

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

**Status:** Proposed

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

**Status:** Proposed

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

**Status:** Proposed; unchanged where not said

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

**Status:** Proposed

- Generic code destroys `T` values at scope ends like any other values,
  with no bound needed. `mono` instantiates the destruction for each
  concrete type: nothing for a `Copy` type, a call to its `deinit` (or
  generated destruction) otherwise.
- `needs_deinit[T]()` (compile-time `bool`) lets containers skip the loop
  over elements, though the optimizer removes an empty loop anyway.
- `ArrayVec[T: Copy, N]` can drop its `Copy` bound once optionals of
  non-`Copy` values are destroyed.
- A type argument still can't be a view, so `List[str]` is not a type:
  `List[String]`, or a list of indices into a buffer. memory.md's example
  `-> List[str]` changes accordingly.

### Field visibility

**Status:** Decided (2026-10-06): option 1, implemented
([types.md](types.md#structs)); `pub let` is still proposed

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

**Status:** Proposed

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

**Status:** Proposed

A `deinit` sees only `self` and globals, so the destruction at a scope's
end changes no facts about the locals still alive. The checker treats it
like a `defer` body: nothing to forget.

## 2. The allocator context

### `uses alloc`

**Status:** Proposed (memory.md); details proposed here

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

**Status:** Proposed

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

**Status:** Proposed

```
pub unsafe trait Allocator {
	fn alloc(self, size: usize, align: usize) throws(AllocError) -> *u8
	fn resize(self, p: *u8, old: usize, new: usize, align: usize) -> bool  // in place, or false
	fn free(self, p: *u8, size: usize, align: usize)
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
- `align` is a power of two. The fact language can't say "power of two",
  so the trait could take its base-2 logarithm instead (`align_log2: u8
  where align_log2 < 64`, a refinement). Open.

### Who frees: containers remember their allocator

**Status:** Proposed

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

**Status:** Open; recommendation below

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

**Status:** Proposed

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

**Status:** Proposed

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

**Status:** Proposed (memory.md); details proposed here

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

**Status:** Proposed

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

**Status:** Proposed

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

**Status:** Proposed

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

**Status:** Proposed

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

**Status:** Proposed

Generics' question 4 recommends that `Eq` is only ever derived. A derived
`==` on `List` would compare pointers. Recommendation: a type with a raw
pointer field gets no derived `Eq`, and std may write `impl Eq` for such a
type (`List[T: Eq]`, `String`, `Box[T: Eq]`), comparing the contents. User
types holding std containers then derive it.

### Views into heap types

**Status:** Proposed; rule 2 of [Views](memory.md#views), which is Decided

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

**Status:** Proposed

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

**Status:** Proposed

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

### M8b: the allocator context, the root allocator and `Box`

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

### M8c: views from functions, `List` and `String`

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

### M8d: error-set unions, the `oom` policy and arenas

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

After M8: `Map[K, V]`, linear types if wanted, `Box[dyn Trait]`, the region
check for stack buffers, refinements on `inout` results, allocation at
compile time (an evaluator heap whose values can't be a constant's value).

## 7. Decisions

**Status:** Decided 2026-10-06 by the user for 3 (with `pub let`), 5, 8 and
11; the others keep the recommended answer unless the user changes them.

1. **Destruction is a method, `fn T.deinit(sink self)`**, not a `Drop`
   trait; it can't throw or allocate
   ([Declaring destruction](#declaring-destruction)). *Recommended.*
2. **Conditional moves use drop flags**, so destruction is always at the
   scope's end ([Moves](#moves)). *Recommended.*
3. **Fields are private to their package by default**, with `pub` and
   `pub let` (read-only outside), and literals of structs with private
   fields only in their package ([Field visibility](#field-visibility)).
   *Decided:* private fields and `pub` are implemented; `pub let` is
   decided, to implement in M8a.
4. **Containers store their allocator**, a word that's zero-sized when the
   program never uses `with`
   ([Who frees](#who-frees-containers-remember-their-allocator)).
   *Recommended.*
5. **Allocators that can end are counted** (option C): an arena's memory
   lives until its last allocation is freed; stack-backed buffers aren't
   `with` allocators in safe code
   ([Allocators that end](#allocators-that-end-arenas-and-fixed-buffers)).
   This is the main safety decision of M8. *Decided.*
6. **The context is a hidden parameter** of `uses alloc` functions only,
   omitted when no `with` is reachable, and dispatched over the program's
   allocator types otherwise ([Lowering](#lowering-the-context)); **the
   `oom` policy is `@oom(abort)` in the main package**, default `error`
   ([Out of memory](#out-of-memory)). *Recommended.*
7. **Error-set unions `throws(A | B)` come in M8**, explicit, without
   inference ([Out of memory](#out-of-memory)). *Recommended.*
8. **`xs[i]` works on `List`** through a sealed, std-only projection to a
   slice, consistent with "no operator overloading" because it means
   exactly slice indexing ([`List[T]`](#listt)). *Decided.*
9. **The explicit copy is `x.clone()`** from a `Clone` trait, rather than
   memory.md's `x.copy()` ([Explicit copies](#explicit-copies)).
   *Recommended, weakly: a naming choice.*
10. **No linear types in M8** ([Linear types](#linear-types)).
    *Recommended.*
11. **A small prelude**: `Box`, `List`, `String`, `AllocError` and the
    built-in traits usable without an import, from `std/core`, rather than
    `list.List[u32]` everywhere. *Decided.*
