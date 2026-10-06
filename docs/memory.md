# Memory model

## Requirements

- Memory safety with no garbage collector and no runtime.
- No lifetime annotations in ordinary code. This is the main readability gap
  with Rust.
- Works for kernels and 8-bit targets, meaning explicit control over where
  memory comes from.
- Data-race freedom follows from the same rules ([concurrency.md](concurrency.md)).

## Chosen direction: mutable value semantics

**Status:** Proposed; parameter conventions implemented (see
[In the compiler today](#parameter-conventions-in-the-compiler-today))

This is the model of [Hylo](https://hylo-lang.org) (formerly Val) and, partly,
Swift. The core idea:

> Variables hold **values**, not references. Assigning or passing copies (or
> moves) the value. Two variables never observe each other's changes.

Mutation stays cheap because a function does not get a pointer. It gets
**temporary exclusive access** to the caller's value through a parameter
convention:

| Convention | Meaning | Rust analogue |
| --- | --- | --- |
| *(default)* `x: T` | Read-only access for the duration of the call | `&T` |
| `inout x: T` | Exclusive read/write access for the duration of the call | `&mut T` |
| `sink x: T` | Ownership moves into the callee | `T` by value |
| `set x: T` | The callee initializes `x` | out parameter |

```
fn push_twice(inout list: List[u32], v: u32) throws(AllocError) {
	try list.push(v)
	try list.push(v)
}

var l = List[u32].new()
try push_twice(&l, 7)   // the & marks the mutation at the call site
```

At the call site, `&` marks exclusive access (syntax Open). Mutation is visible
where it happens, which is good for readability.

**Why this removes lifetimes:** accesses can't escape the call they were
granted for, so the compiler never needs to track how long a reference lives
across functions. Exclusivity is checked locally: in one call, an argument
passed `inout` cannot overlap any other argument.

### Parameter conventions in the compiler today

**Status:** Implemented. `&` is provisional: the syntax is still Open.

```
fn split(v: u32, set hi: u32, set lo: u32) {
	hi = v / 10
	lo = v % 10
}

fn sort(inout xs: []u32) { ... }       // assigns xs[i]

var hi: u32                            // assigned by the call
var lo: u32
split(42, &hi, &lo)
var a: [4]u32 = [3, 1, 4, 1]
sort(&a)                               // a viewed as a slice it can change
```

- **Default** (`x: T`): read-only for the call. A value in memory is passed
  as the address of the caller's value.
- **`inout x: T`**: the callee reads and writes the caller's place. The
  argument is `&place`: a `var`, a parameter the function may change
  (`inout`, `sink`, `set`), or a field or an element of one (`&p.x`,
  `&a[i]`). An element's index is evaluated once, before the call. The place
  must have exactly the type `T`: there's no widening.
- **`inout xs: []T`**: a slice whose elements can be assigned (`xs[i] = v`).
  The argument is `&a` for a `var` array `a` (or a row, `&grid[i]`), or `&xs`
  for another `inout` slice, or part of one of them: `&a[i..j]`,
  `&xs[..mid]`. So an in-place algorithm works on a sub-range, and can
  recurse on its halves (`quicksort(&xs[..p])`). The slice itself can't be
  assigned, so its length doesn't change. It can't be copied into a local
  either, nor can a slice of it, since the copy would see the elements
  change. `for x in xs` over it reads each element when it gets to it. A
  `str` can't be `inout`.
- **`sink x: T`**: the value moves in. Every type today is plain data that's
  copied, so `sink` is a copy the callee may change, and the caller's
  variable is unchanged. It matters once types own resources: then the
  caller's variable is moved from, and the callee destroys the value.
- **`set x: T`**: the callee assigns `x`, whole, on every path that returns,
  and can't read it before. A `throw` doesn't need to assign it. The
  argument is `&x`, and `x` may be a `var` declared without a value
  (`var x: T`). After the call `x` is assigned, but only if the call
  succeeded: in a `catch` block and in a `match` arm for `err`, it's as
  before the call. A view can't be `set`.
- A `var` declared without a value must be assigned on every path before
  it's read. `let` always needs a value.
- `&` on a default or `sink` argument is an error, and so is an `inout` or
  `set` argument without `&`. `&` is only allowed in a call's arguments.

**Exclusivity.** In one expression (the expression of a statement, or a
condition), a place passed `inout` or `set`, with `&` or as the receiver of
a method that takes `inout self`, can't overlap anything else the
expression uses. Two places overlap when they're parts of the same variable,
unless at some step they go to different fields, or to elements at
different constant indexes:

| Expression | |
| --- | --- |
| `swap(&p.x, &p.y)`, `swap(&a[0], &a[1])` | Allowed: different fields, different constant indexes |
| `swap(&a[i], &a[j])` | Error, even where `i != j` is known |
| `fill(&a[..2], a[3])`, `two(&a[..2], &a[2..])` | Error: a slice overlaps every element and every other slice of its array |
| `swap(&x, &x)`, `add(&x, x)`, `p.scale(p.x)` | Error |
| `fill(&a, a.len)` | Allowed: a length is never changed through `&` |

The rule covers the whole expression, not only the call's arguments: an
argument in memory or a view is passed as an address into the caller's
storage, and what the checker knows about a variable read earlier in the
expression would be stale after the call changes it. It's stricter than
Swift's, which allows `add(&x, x)`; write `let k = x` first.

### In the checker

After a call, the checker forgets what it knew about each place passed
`inout` or `set`: a variable, or a struct field and the fields in it. Array
and slice elements have no facts, and a slice's length doesn't change. In a
loop, a variable passed with `&`, or a method's receiver, counts as assigned
([safety.md](safety.md#facts-through-loops)). In the callee, `inout`, `sink`
and `set` parameters are variables whose facts start from their type.

### Owning pointers are values

**Status:** Proposed

The rule is **no *non-owning* references in structs**. A pointer that *owns*
what it points to is just a value stored on the heap. It has exactly one owner,
it moves instead of copying, and it's freed with its owner. `Box[T]` is that
pointer:

```
struct Node[T] {
	value: T
	next: ?Box[Node[T]]
}
```

So any structure where every node has exactly one owner can be written in
ordinary safe code: singly linked lists, trees owned from the root, tries,
ASTs.

The compiler-generated `deinit` for a self-recursive owning type must be
**iterative**: unlink `next`, then loop. Recursive destruction of a long list
would use one stack frame per node, which overflows the stack and breaks
[stack bounds](safety.md#stack-bounds).

### Shared and back-pointer structures belong to the standard library

**Status:** Decided

Structures where a node is reached through more than one pointer (doubly
linked lists, parent pointers, graphs, intrusive lists) are exactly the ones
that are easy to get wrong. They are written **once, in the standard library**,
with `unsafe` inside and a safe API outside. User code uses them. It doesn't
reimplement them.

Candidates (the exact list is Open):

| Container | Covers |
| --- | --- |
| `Arena[T]` + `Handle[T]` | The general tool: nodes in one arena, typed generational handles as edges. A stale handle gives `none`, never undefined behavior. |
| `DList[T]` | Doubly linked list, O(1) insert and remove through cursors or handles |
| `Tree[T]` | Tree with parent links and sibling navigation (DOM, scene graphs, file trees) |
| `Graph[N, E]` | Directed graph with node and edge payloads, both directions of traversal |
| `LruCache[K, V]` | Hash map plus recency list, the classic "needs two pointers per entry" case |
| `IntrusiveList[T]` | Kernel-style lists where the link lives inside the element. **Open:** needs elements that don't move in memory. Maybe `unsafe` to insert, safe to traverse. |

API rules, so that the safe surface stays safe:

- **Positions are handles or cursors, never pointers.** A handle is a
  generational index: plain data, safe to store in structs and send between
  threads. A cursor is a *view* (see [Views](#views)) that borrows the
  container while it's in use, so the container can't change underneath it.
- **Mutation goes through the container:** `list.remove(h)`,
  `tree.move(h, new_parent)`. Invariants (such as "`prev.next == self`") are
  kept in one place.
- Removal gives back the value (`sink`), so ownership is never ambiguous.

The standard library's `unsafe` code is held to a higher bar than ordinary
`unsafe`:
- every `unsafe` block states the invariant it relies on
- property-based tests of each container against a simple reference model
- run under a checking interpreter (LatticeFoundry's IR/MIR interpreters are
  a starting point) that detects use-after-free and out-of-bounds in tests,
  Miri-style (**Open**: scope)

User code can still use `unsafe` pointers when nothing in the standard library
fits. That's the escape hatch, not the expected path.

This is the trade we make. Rust's borrow checker allows stored references at
the cost of lifetime annotations. We choose readability, and move the hard
structures into one audited place.

### Views

**Status:** Decided

Slices (`[]T`), string views and iterators are *views* into another value. A
view is a stored reference in disguise, so its use is restricted:

1. **Views can be parameters, locals and return values. They are never struct
   fields.** (This is Hylo's "projections".)
2. **A returned view borrows from the parameters.** The caller can't mutate or
   destroy what the view came from while the view is in use. There's no syntax
   for lifetimes: the rule is always the same.

```
fn trim(s: str) -> str { ... }       // the result borrows from s

let line = read_line()
let t = trim(line)
line.clear()                         // error: line is borrowed by t
print(t)
```

When a function takes several view parameters and returns a view, the result
is taken to borrow from **all** of them. That's conservative, and it's never
wrong. **Open:** do we need a way to narrow it (`-> str from s`) for the rare
function where that matters?

Iterators and parsers that hold their input are fine, as long as they live in
locals. They are views themselves. A parser that has to *outlive* its input
owns a copy or holds [handles](#shared-and-back-pointer-structures-belong-to-the-standard-library).
This rule also lets scoped threads use views without copying
([concurrency.md](concurrency.md#structured-concurrency)).

**In the compiler today:** views are parameters and locals, never fields,
and functions don't return them yet. A few built-in projections make a view
of another one: an array where a slice is expected, `s.bytes()`, the
`[]u8` of a `str`, and a slice `a[i..j]` of an array or a slice. A
projection views what its receiver views, so it obeys the same rules as the
receiver: kept in a local, passed to a function, never stored.

Until rule 2 is checked, the compiler keeps a view from seeing what it
views change with simpler rules:

- a slice kept in a local (`let s = a[i..j]`, or a `var` given one) may
  only view a `let` array, an array constant, or another read-only view.
  Of a `var` array, of a temporary, or of an `inout` slice, it can only be
  passed straight to a function;
- `for x in a[i..j]` views `a` for the whole loop, so the loop can't change
  the array `a` (an `inout` slice is read as the loop goes, as in
  `for x in xs`);
- `&a[i..j]` passes part of a `var` array or of an `inout` slice to an
  `inout` slice parameter, and the [exclusivity](#parameter-conventions-in-the-compiler-today)
  rule counts it as overlapping all of `a`.

A function can return a `str` whose storage is static, since it borrows
from nothing: rule 2 holds trivially, without the checks it needs in
general. The rule, checked per function:

- a string literal is static;
- the result of a call to a function returning a `str` is static (every
  such function obeys this rule);
- a local is static if every value it's ever given in the function is
  static (a literal, such a call, or a copy of a static local). A
  parameter never is: its string may live in the caller's storage.

Every `return` of a function returning a `str` must give a static value.
The rule doesn't follow control flow: `var s = "x"` assigned a parameter
anywhere makes every `return s` an error, even one before the assignment.
Returning a view that borrows from the parameters, and returning slices,
wait for rule 2 to be checked. A function that throws can't return a `str`
yet (its result would hold a view in memory).

## Copies

**Status:** Proposed (M8: [allocation.md](allocation.md#moves))

- Small plain types (integers, fixed arrays of them, structs of them) are
  implicitly copied.
- Types that own resources (heap memory, file handles) are **moved** by
  default. Copying them is explicit: `x.copy()`, which can allocate and
  therefore can throw.
- The last use of a variable moves instead of copying (the compiler knows).

### In the compiler today

**Status:** Implemented for arrays, structs, enums and optionals

- Every array, struct, enum and optional is a plain value, copied by `let`,
  by assignment and into array elements and fields. A `match` binds copies
  of the payload fields. Nothing owns resources yet, so a concrete type
  never moves.
- In a generic function, a type parameter without the bound `Copy` (and an
  optional or an array of one) is moved, never copied: keeping the value
  of a `let`, a `var` or a `sink` parameter moves it out, and the variable
  can't be used until it's assigned again; keeping an element or another
  parameter is an error ([generics.md](generics.md#copy-and-moves-in-generic-code)).
  So generic code already follows the rule move-only types will need.
- A default parameter is read-only for the duration of the call. Nothing can
  change the argument during the call, so an array or a struct is passed as
  the address of the caller's value, without a copy. An `inout` or `set`
  parameter is the caller's place itself (a scalar too: the callee loads
  and stores through its address), and a `sink` one in memory is copied on
  entry, since the callee may change it.
- A function returning an array or a struct writes the result straight into
  storage the caller provides: the new variable in `let p = make()`, or else
  a temporary. So `p = swap(p)` can't overwrite `p` while `swap` still reads
  it.

## Uninitialized buffers

**Status:** Decided: option 3; implemented (see
[In the compiler today](#in-the-compiler-today-1) below)

Every variable is assigned before use, and an array is assigned whole, so a
buffer that's filled piece by piece has to be filled first: `std/io`'s
integer output used to start with `var buf: [21]u8 = [0; 21]` and then only
ever read the part it wrote. For 21 bytes that costs nothing worth measuring; for
a 4 KiB read buffer, or a large array on a small embedded stack, it's a
`memset` per call that the optimizer may or may not remove, and the result
must not depend on the optimizer. The options:

1. **Keep filling** (today). Simple and obviously safe. The cost is the fill,
   and it's paid at `-O0` and whenever dead-store elimination doesn't see
   that every read follows a write.
2. **Track initialized element ranges in the checker.** `var buf: [N]T =
   undefined` (or `uninit`) starts with no initialized elements; the fact
   language gains one fact per such array, "elements `lo..hi` are written",
   with `lo` and `hi` terms plus constants, like the facts in
   [safety.md](safety.md#the-fact-language). `buf[i] = v` with `i == lo - 1`
   or `i == hi` grows the range; `buf[i]`, `buf[a..b]` and passing `buf`
   need a proof that what's read is inside it. It flows through `if` and
   loops with the existing rules (joins, loop heads). Costs: the checker
   gets more complex, only contiguous growth from one end or the other is
   understood (no scattered writes), and the rule has to be specified as
   exactly as the others. No runtime cost and no new types.
3. **A write-only buffer type in the standard library**, such as a
   `StackBuf(N)` that only allows `push_front`/`push_back` and hands out a
   slice of the part written so far. The initialized range is the type's
   private state (a length or a start index), kept right by `unsafe` code
   inside the type, so the checker doesn't change. Costs: it needs generics
   and methods (M6, M7), it carries a counter at run time (often in a
   register anyway), and code has to go through its API instead of plain
   indexing.
4. **Uninitialized but defined**: `undefined` gives elements an arbitrary but
   fixed value (the backend "freezes" it), so reading one is not undefined
   behavior. Cheapest to implement. Costs: a program can print or send
   whatever was on the stack before (an information leak, as with
   uninitialized buffers in C), and it hides bugs instead of rejecting them.

Decided (2026-10-06): 3. Types like `StackBuf` keep the written range in
private fields, and only their own package's code, which promises with
`unsafe` to read nothing else, can leave storage unwritten. Option 2 may
come later for code that wants plain arrays. Option 4 is not planned.

### In the compiler today

**Status:** Implemented

A struct field declared `@uninit` may be left unwritten:

```
pub struct StackBuf[N: usize] {
	@uninit bytes: [N]u8
	start: usize
	end: usize
}

pub fn StackBuf[N].new() -> StackBuf[N] {
	unsafe {
		return StackBuf{start: 0, end: 0}
	}
}
```

- The field is an array of integers, and private: it can't be `pub`
  ([types.md](types.md#structs)). So only the struct's package reads it.
- A literal may leave it out only in `unsafe` code (an `unsafe` block or
  an `unsafe fn`). Elsewhere, leaving it out is the usual missing-field
  error. The `unsafe` is a promise, stated in
  [safety.md](safety.md#the-trusted-boundary): the package never reads an
  element of it before writing it.
- A struct with an `@uninit` field isn't `Eq`, and neither is anything
  that holds one: `==` would compare the elements never written.
- Copying the struct (`let c = b`, passing or returning it) copies the
  unwritten elements too. That's defined: in LatticeFoundry, memory never
  written reads as poison, and poison stored somewhere is still poison.
  Only using it (a branch, an address, a divisor, output) is wrong, and
  the promise rules that out.
- In a function run while compiling, the elements left out are zeros.

`std/buf.StackBuf[N]` is option 3's type
([packages.md](packages.md#the-standard-library-in-the-compiler-today)):
bytes written at the back with `push`, or at the front with `push_front`,
only the written part `bytes[start..end]` is read (`get`, `len`,
`write_to`, and `io.File.write_buf` through it), and every access is
proven. `new` and `new_end` don't write the storage. `print`'s 256-byte
buffer is `@uninit` the same way. (`io.Format` for integers doesn't use a
`StackBuf`: it cost 640 bytes more than a plain `[21]u8`, which is still
filled, see
[packages.md](packages.md#the-standard-library-in-the-compiler-today).)

Without the fill, a program that prints a formatted value is 96 bytes
smaller at `-O2` (and `-O0`), and one using `StackBuf`s 380 to 820 bytes
smaller. Hello world, which has no buffer, is still 577 bytes and two
system calls.

Its written part, `bytes[start..end]`, is kept right by the refinements of
its fields, `start <= end` and `end <= N` ([Struct
invariants](#struct-invariants)); the `@uninit` storage has none. Every
method that changes `start` or `end` proves them, and every method that
reads them knows them, so none checks again.

## Struct invariants

**Status:** A first form is implemented (2026-10-06): the refinements of
struct fields

A type often keeps a fact about its fields: a ring buffer's `head < CAP`,
a vector's `count <= N`, a window's `start <= end`. Without a way to say
it, every function that relies on it had to check it again (`head % CAP`,
`if count > N { return none }`), which costs code and hides real bugs
behind fallbacks that can't run.

A field's refinement says it ([safety.md](safety.md#refinements-in-types)):

```
struct Ring {
	head: usize where head < CAP
	len: usize where len <= CAP
	data: [CAP]u32
}
```

- Every value of the struct keeps its fields' refinements. A literal
  proves them, and so does every assignment to a field, for each
  refinement that names it (`r.head = (r.head + 1) % CAP` is proven; `r.len
  += 1` needs `r.len < CAP` first). A field passed `&` must come back
  meeting them, which only a parameter with a refinement that proves it
  can promise.
- Wherever a field is read, they're facts: about the fields of a variable
  or a parameter (and the structs in it), relations included; for a value
  read from elsewhere (an element, a call's result), the field's own
  range.
- A refinement can relate two fields (`start <= end`), name constants and
  the struct's value parameters (`count <= N`). A refinement that relates
  fields is checked at each assignment, so fields that move together are
  changed in an order that keeps it at each step.

With private fields, only the struct's package can assign them, so the
proofs are all in that package; its users only read the facts. A field
can be `pub`, `@uninit` (no refinement: it's an array) and refined, in
that order: `pub head: usize where head < CAP`.

Not yet: refinements over elements (`[N]Index` is an error for now), and
invariants between a field and an array's contents (an empty slot means
`count < CAP`).

## Destruction

**Status:** Proposed. The M8 proposal works it out:
[allocation.md](allocation.md#1-resource-types-and-destruction).

Values are destroyed at the end of their scope in reverse order. A type can
define `fn deinit(sink self)`. Destruction is deterministic and visible in the
scope structure. Only `defer` and scope end run cleanup, so there is no hidden
control flow.

**Open:** "linear" types that *must* be consumed explicitly (for example a
transaction that must be committed or rolled back). This would be valuable, and
fits the model well.

## Allocation

**Status:** Proposed. The M8 proposal works it out, with the lowering of the
context and the safety of arenas:
[allocation.md](allocation.md#2-the-allocator-context).

- There is no global `malloc` that code can call behind the user's back.
  Anything that allocates takes an allocator.
- To keep call sites readable, the allocator is an **implicit context
  parameter**. Functions that allocate declare it (`uses alloc`), callers
  inherit their own, and it can be overridden for a scope:

```
fn build(names: []str) uses alloc throws(AllocError) -> List[str] { ... }

with alloc = arena {
	let l = try build(names)     // allocates in the arena
}
```

- The executable's root allocator comes from the target's os layer
  ([backend.md](backend.md)). A project can replace it, which covers the goal
  of reimplementing low-level pieces.
- A function without `uses alloc` provably doesn't allocate. That is useful in
  interrupt handlers and real-time code.

### Out of memory

Allocation returns `AllocError`. Because that is noisy for applications, a
**program-level policy** can turn it into a defined abort:

- `oom = error` (the default for libraries, kernels and embedded code):
  `AllocError` is propagated like any other error.
- `oom = abort` (opt-in for applications): allocating functions are no longer
  `throws(AllocError)` from the caller's point of view.

**Open:** can the same library be compiled under both policies without writing
it twice? (Probably yes, if `AllocError` is part of an inferred error set, see
[errors.md](errors.md).) [allocation.md](allocation.md#out-of-memory)
proposes yes: under `oom = abort`, `AllocError` is an empty enum, which
needs only explicit unions (`throws(A | B)`), not inference.

## Globals

**Status:** Decided (details Proposed)

Package-level state comes in three kinds:

```
const MAX_USERS = 1024                            // compile-time constant
let DEFAULT_NAME: str = "guest"                   // immutable, initialized at compile time
static requests: Atomic[u64] = Atomic.new(0)      // mutable: Atomic only
static config: Mutex[Config] = Mutex.new(Config.default())   // or Mutex only
```

- **Mutable globals must be `Atomic[T]` or `Mutex[T]`** (or `RwLock[T]`). A
  plain mutable global is only allowed in `unsafe` code, for kernels and
  drivers that manage their own synchronization.
- **Every global is initialized at compile time.** There are no `init()`
  functions and no static constructors, so nothing runs before `main`
  ([pay only for what you use](concept.md#pay-only-for-what-you-use)), and
  initialization order between packages can't matter. Global state that needs
  run-time setup is created in `main` and passed down, or uses a lazily
  initialized standard-library type (**Open:** `Lazy[T]`, whose first access
  may run code and possibly fail).

### Downgrading when there's no concurrency

**Status:** Proposed

When whole-program analysis shows that nothing can run concurrently, the
synchronization is compiled away. The source stays the same:

| Program | `Atomic[T]` becomes | `Mutex[T]` becomes |
| --- | --- | --- |
| Single OS thread, no green threads, no interrupt or signal handlers | Plain loads and stores | A borrow flag, no atomic instructions |
| Single OS thread with green threads (cooperative) | Plain loads and stores (a green thread can't be interrupted mid-operation). With [preemption](concurrency.md#preemption) on: single-instruction read-modify-write, safe on one core | A task-level lock without atomics (a green thread can yield while holding it) |
| Interrupt handlers reach the global (single-core microcontroller) | Target-specific interrupt-safe access, or a short critical section | A critical section (interrupts disabled while held) |
| Several OS threads | Real atomics | Real mutex |

"Nothing can run concurrently" is decided from the whole program: whether any
thread spawn, interrupt handler or signal handler is reachable. It's recorded
in the build output so it isn't a hidden optimization.

The observable behavior must be **identical in every mode**. In particular,
locking a mutex the same thread already holds must do the same thing whether
or not the mutex was downgraded. **Open:** make it a compile error where
detectable, and a defined abort otherwise?

## Comparison

| | Rust | Zig | Lode |
| --- | --- | --- | --- |
| Use-after-free prevented | Yes (borrowck) | No | Yes (value semantics) |
| Lifetime annotations | Yes | No | No |
| References in structs | Yes | Yes (unchecked) | Owning only (`Box`); shared structures come from std |
| Explicit allocators | Partly | Yes | Yes, as an implicit context |
| Fallible allocation | Mostly no | Yes | Yes, or abort by policy |
