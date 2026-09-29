# Concurrency

**Status: early.** This file records the constraints and a direction. Most of it
is Open.

## Requirements

- Native syntax or native elements for parallelism. They may live in the
  standard library, as long as they feel native.
- Data-race freedom is part of memory safety ([safety.md](safety.md)).
- No runtime, as defined in [concept.md](concept.md#what-no-runtime-means).
  There's no built-in scheduler as in Go. Green threads are optional and
  opt-in (see below).
- It must work on a kernel with no OS threads, and on an 8-bit microcontroller
  whose only "thread" is an interrupt handler.

## Data-race freedom

**Status:** Proposed

Value semantics does most of the work ([memory.md](memory.md)). A value passed
to another thread is copied or moved, so nothing is shared by accident. Sharing
is explicit, through types that are safe to share:

- `Atomic[T]` for integers and small values
- `Mutex[T]`, `RwLock[T]`: the data is *inside* the lock and can only be
  reached while holding it (as in Rust)
- `Shared[T]`: immutable data shared by reference counting (atomic), or kept
  alive by structured scoping (below)

Two marker traits, as in Rust's `Send`/`Sync`, decide what may cross a thread
boundary. Most types get them automatically. Types that wrap raw pointers opt
out unless their author asserts otherwise with `unsafe`.

## Structured concurrency

**Status:** Proposed

Threads are spawned inside a scope that doesn't end until they all finish, so a
thread can't outlive the data it reads:

```
fn sum_parallel(data: []u64) -> u64 {
	let (left, right) = data.split_half()
	var a: u64 = 0
	var b: u64 = 0
	scope s {
		s.spawn { a = sum(left) }
		s.spawn { b = sum(right) }
	}                                  // both threads joined here
	return a +| b
}
```

Because the scope ends before `data` does, `left` and `right` (views) can be
used by the threads without copying and without lifetime annotations. This
follows the view rules in [memory.md](memory.md#views).

**Open:** detached threads (daemons) need `sink`-only captures. Do we offer them
at all, or require them to be modeled as a scope at the top of `main`?

## Async: green threads

**Status:** Decided

There are no `async` functions and no function coloring. Concurrency beyond OS
threads uses **green threads**: stackful coroutines, each with its own stack,
scheduled by a library on top of the `context_switch` intrinsic
([safety.md](safety.md#the-trusted-boundary)). A function that does I/O is
written the same way whether it runs on an OS thread or a green thread.

Rejected:
- **Stackless coroutines** (Rust `async`): no runtime cost, but they split every
  API into two colors and make the code harder to read.
- **No async at all** (threads plus blocking I/O only): too costly for servers
  with many connections.

### Why this works better for Lode than for most languages

The classic problems with green threads are stack size and foreign code, and
Lode's other decisions address both:

- **Stack size.** A green thread needs its own stack, and nobody knows how big
  to make it. Lode computes [stack bounds](safety.md#stack-bounds): when the
  entry function's call graph is bounded, the green thread gets *exactly* that
  much stack. Otherwise it gets a default size with a guard page, and overflow
  is a defined abort. No segmented or copied stacks are needed.
- **Foreign code.** C code assumes a large stack and may block the whole OS
  thread. Because Lode is native by default and FFI is explicit
  ([packages.md](packages.md#external-libraries-ffi)), every foreign call site
  is known. Those calls switch to the OS thread's own stack (as Go's cgo does),
  and only programs that use FFI pay for it.

### Green threads without a runtime

**Status:** Decided (the layering is Proposed)

A scheduler, with its run queue, event loop and timers, *is* a runtime. So the
"no runtime" goal ([concept.md](concept.md#what-no-runtime-means)) can't mean
"no scheduler ever". It means the scheduler is **optional, opt-in and
minimal**, and a program that doesn't start one pays nothing for it.

Rules the scheduler must follow:

1. **Explicit start.** Nothing schedules green threads until the program starts
   a scheduler at a visible point, typically in `main`:
   ```
   fn main() uses alloc throws {
   	task.run(serve)          // the scheduler exists inside this call only
   }
   ```
   When `task.run` returns, every green thread has finished (structured
   concurrency), and nothing is left running in the background.
2. **No hidden OS threads.** The scheduler never creates OS threads unless the
   program configures it to (a worker count, or a pool for blocking
   operations). The default is one OS thread: the one that called `task.run`.
3. **No hidden signals.** Scheduling is cooperative by default: a green thread
   yields at I/O, at lock waits and at an explicit `yield()`. Signals or timers
   are used only when the program turns on [preemption](#preemption) when it
   starts the scheduler.
4. **Pay per layer.** The scheduler is built in layers, and only the layers the
   program reaches are linked (below).
5. **Replaceable.** Code finds the scheduler through an implicit context,
   declared as `uses task` (like `uses alloc` in
   [memory.md](memory.md#allocation)). A kernel, firmware or game engine can
   supply its own scheduler. Green-thread I/O works on top of any scheduler
   that implements the interface.

### Layers

**Status:** Proposed

| Layer | Provides | Linked when the program uses | Rough cost |
| --- | --- | --- | --- |
| 0. Coroutines | `context_switch` plus a stack per coroutine. Generators and symmetric coroutines with no scheduler at all. | `coroutine.new` | A few instructions per switch; no global state |
| 1. Run queue | Cooperative round-robin on one OS thread: `spawn`, `yield`, join, task-level locks | `task.run` | A queue and a loop |
| 2. I/O reactor | Parking on I/O readiness (epoll, io_uring, kqueue), timers, sleep, timeouts | I/O or timers inside `task.run` | Only the backend for the target, and only the operations used |
| 3. Multi-threaded | Several OS threads, work stealing, a pool for operations that can't be made non-blocking | An explicit worker count or pool setting | Real atomics and OS threads |

A program that only uses generators gets layer 0. A single-threaded network
server gets layers 0 to 2. Only a program that asks for several worker threads
pays for layer 3.

### Preemption

**Status:** Proposed. Opt-in; signals are the preferred mechanism.

A long CPU-bound loop never reaches a yield, so the other green threads on its
OS thread starve. With several worker threads (layer 3), work stealing moves
waiting green threads to other workers, which helps, but it doesn't help when
every worker is busy or there's only one. So the scheduler needs a way to
interrupt a running green thread.

Preemption is **off by default** (cooperative scheduling costs nothing) and is
turned on when the scheduler is started:

```
task.run(serve, .{workers = 8, preempt = .signal(10ms)})
```

#### Mechanism 1: signals (preferred)

A timer interrupts a green thread that has been running too long, and the
signal handler switches it out.

- **The timer** is a per-OS-thread CPU-time timer (`timer_create` on
  `CLOCK_THREAD_CPUTIME_ID`, delivered to that thread). It only fires while the
  thread is actually burning CPU, and there's no monitor thread (Go needs its
  `sysmon` thread for this). It's armed only when the run queue has other
  green threads waiting. A lone busy thread is never interrupted.
- **The handler** runs on an alternate signal stack (`sigaltstack`), so green
  thread stacks and their [stack bounds](safety.md#stack-bounds) are
  unaffected. It rewrites the interrupted context to jump into a trampoline
  that saves the complete register state (including vector registers) on the
  green thread's stack, then switches.
- **No safe points are needed.** Go's preemption has to stop where its garbage
  collector can find the pointers on the stack. Lode has no GC, so any
  instruction in Lode code is a valid place to switch, given a full register
  save.

Where the switch must *not* happen:

| Situation | Handling |
| --- | --- |
| Inside foreign (FFI) code | The handler checks that the interrupted address is in Lode code. If not, it sets a pending flag, and the switch happens when the FFI call returns. |
| Scheduler internals, green-thread lock operations, allocator fast paths | A per-OS-thread "no preemption" counter: a plain increment and decrement, with no syscall. The handler sees it's non-zero, sets the pending flag, and the region's exit checks the flag. Also available to `unsafe` code as `no_preempt { ... }`. |
| Blocking syscalls | Interrupted syscalls return `EINTR`, and `std/os` retries them (it must do this anyway). Handlers are installed with `SA_RESTART`. |

#### Mechanism 2: compiler-inserted yield points (fallback)

For targets without usable signals (wasm, some embedded systems), or when a
program asks for it. The compiler inserts a check (load a flag, rarely taken
branch) where time can accumulate without bound:

- Only in loops whose total cost can't be bounded at compile time. A loop with
  a known trip count whose cost is below the time slice needs no check.
  LatticeFoundry's cost lattice (bet B9) supplies the bound.
- At function entry, only for functions that are part of recursive cycles.
- Checks are made less frequent by counting iterations (check every N
  iterations), so tight loops can still be unrolled and vectorized.

That keeps the overhead to the loops that actually need it, but it's never
zero. That's why this is the fallback and not the default.

#### Other platforms

| Target | Mechanism |
| --- | --- |
| Linux, BSDs, macOS | Signals |
| Windows | A monitor thread suspends the worker and rewrites its context (`SuspendThread` / `SetThreadContext`), which is what Go does. The monitor thread exists only when preemption is enabled. |
| Bare metal / RTOS | A hardware timer interrupt, which is exactly how an RTOS preempts. It goes through the same trampoline. |
| Kernel | The kernel's own timer interrupt |
| wasm | Yield points only |

#### Consequences elsewhere

- **Downgraded synchronization.** A program with green threads on a single OS
  thread normally compiles `Atomic` operations down to plain loads and stores,
  because a green thread can't be interrupted in the middle of one
  ([memory.md](memory.md#downgrading-when-theres-no-concurrency)). With
  preemption on, it can be. So those programs use single-instruction
  read-modify-write operations where the target has them (safe against an
  interrupt on the same core, and cheaper than locked atomics), or the
  no-preemption counter otherwise.
- **Backend.** LatticeFoundry needs to provide the full-context trampoline and
  the yield-point insertion ([backend.md](backend.md#needed-for-the-safety-story)).

### Still open (green threads)

- Cancellation and timeouts: see [Cancellation](#cancellation-and-deadlines)
  for the proposed direction. The exact wake-up path is still open.
- Stacks for green threads come from the allocator in context. Should the
  scheduler keep a pool of freed stacks (faster, but memory held longer)?

## Thread placement: dedicated threads, CPU pinning, the main thread

**Status:** Decided that this must be supported. The API is Proposed.

Two needs drive this:
- **Maximum performance.** A computation owns an OS thread, which is pinned to a
  CPU core, possibly isolated, possibly busy-polling (what Go programs do with
  `runtime.LockOSThread` plus `sched_setaffinity`, or what DPDK-style network
  stacks do).
- **Thread-affine foreign libraries.** Some libraries must be called from one
  specific thread: macOS AppKit and many other UI toolkits need the **main
  thread**, and OpenGL contexts and some C libraries use thread-local state.

### OS threads are already first-class

`scope.spawn` in [structured concurrency](#structured-concurrency) creates a
real OS thread, so a computation that should own a thread just runs on one.
Green threads are opt-in on top, so there's nothing to "lock" in the common
case. What's needed is control over where the thread runs:

```
scope s {
	s.spawn(.{cpu = 3, priority = .fifo(50), stack = .bound}) {
		poll_nic_forever(&queue)      // owns core 3, never shares it
	}
}
```

- `cpu` sets the affinity (`sched_setaffinity` on Linux,
  `SetThreadAffinityMask` on Windows). macOS only offers affinity *hints*, so
  there it's best-effort, and the build reports it.
- `priority` sets the scheduling class, e.g. real-time FIFO, where the OS
  allows it. Failing to get it is an error, not silently ignored.
- `stack = .bound` sizes the thread's stack from its
  [stack bound](safety.md#stack-bounds).
- `std/os` exposes the rest for programs that need it: locking memory to avoid
  page faults (`mlockall`), and reading the CPU/NUMA topology.

### Green threads that need a fixed OS thread

Inside `task.run`, a green thread may need to stay on one OS thread (for a
thread-affine library, or to keep a hot loop on one core). Two forms:

- **Dedicated task:** `task.spawn_dedicated(.{cpu = 5}) { ... }` behaves like
  any green thread for the rest of the program (it can be joined, it can use
  channels and green-thread locks), but it gets an OS thread of its own. It
  never migrates and never shares that thread. The preemption timer is never
  armed on it, because nothing else is waiting on its thread.
- **Pinned scope:** `task.pinned { ... }` keeps the current green thread on
  its current OS thread until the scope ends. Other green threads on that
  worker move elsewhere. This is Go's `LockOSThread`/`UnlockOSThread`, but a
  scope, so it can't be left unbalanced.

Worker threads themselves can be pinned: `task.run(serve, .{workers = cpus(0..8), pin = true})`.
The allocator in context can be per-NUMA-node for pinned workers
([memory.md](memory.md#allocation)).

### The main thread

`main` runs on the process's main OS thread. What happens to that thread
depends on how the scheduler is started:

- `task.run(f)` (default): the main thread becomes worker 0, like any other.
- `task.run(f, .{main = .reserved})`: the scheduler's workers are other OS
  threads, and the main thread stays available for the program. That's where
  a UI event loop that never returns runs (for example `NSApplication.run`).

Work is sent to the main thread through `main_thread.post(fn)`. The platform
package implements the wake-up by integrating with the foreign event loop
(a run-loop source on macOS, a queued message on Windows). Where the foreign
loop is just a file descriptor (the X11 connection, Wayland), the main thread
can register it in [`std/poll`](#io) and run a normal Lode loop instead.

### Checking thread affinity at compile time

**Status:** Proposed

"Must be called on the main thread" is normally a runtime crash (macOS
aborts, or worse, corrupts silently). Lode can check it with the same implicit
context mechanism as `uses alloc` and `uses task`:

| Context | Satisfied in |
| --- | --- |
| `uses main_thread` | `main` itself (before starting the scheduler, or with `main = .reserved`), and functions run through `main_thread.post` |
| `uses pinned` | Dedicated tasks, `task.pinned { }` scopes, and plain OS threads |

A binding to a thread-affine foreign library marks its functions with the
context they need ([packages.md](packages.md#external-libraries-ffi)), for example
`fn Window.show(self) uses main_thread`. Calling it from a green thread that
may migrate is then a **compile error**, not a crash on a user's machine.

This also answers **thread-local variables**. A green thread that migrates
between OS threads would see a different thread-local each time. So reading a
thread-local requires `uses pinned`, and green threads get task-local storage
instead. **Open:** exact rules for task-locals.

## Channels and synchronization tools

**Status:** Decided that these live in the standard library with no special
syntax, and must be memory safe. The API is Proposed.

Go's toolbox for goroutines is one of its best features. Lode provides the
same tools in `std/sync` (name Open), as ordinary library types. They work with
OS threads, green threads and a mix of the two.

### Channels

```
let (tx, rx) = channel[Job](capacity: 16)

scope s {
	s.spawn {
		for job in jobs {
			tx.send(job) catch { break }     // the receivers are gone
		}
	}                                        // tx dropped here: channel closes
	s.spawn {
		while let job = rx.recv() {          // none once closed and drained
			process(job)
		}
	}
}
```

Memory safety comes from the rules the language already has:

- **`send` takes the value (`sink`).** It moves into the channel, and the
  sender can't touch it afterwards. `recv` gives the receiver ownership. No two
  threads ever see the same value, so there's no data race to prevent.
- **Only sendable values** (the `Send`-like marker from
  [data-race freedom](#data-race-freedom)) can go through a channel.
- **Views can't be sent.** A channel's buffer is storage, and views can't be
  stored ([memory.md](memory.md#views)). Send an owned value, a
  `Shared[T]` or a [handle](memory.md#shared-and-back-pointer-structures-belong-to-the-standard-library).
- Values still buffered when the channel is destroyed are destroyed with it.

**No crash paths**, unlike Go:

| Go | Lode |
| --- | --- |
| Send on a closed channel panics | `send` fails with `Closed` and **gives the value back** in the error, so nothing is lost |
| Closing twice panics | Closing is not a separate call. A channel closes when every `Sender` is gone (as in Rust). `tx.close()` exists, but it consumes that sender (`sink self`), so it can't be called twice. |
| A `nil` channel blocks forever (used to disable a `select` case) | No nil. A case is disabled by passing `none` in its place. |
| "all goroutines are asleep - deadlock!" kills the process | When every green thread is blocked and no I/O or timer is pending, `task.run` returns a `Deadlock` error instead |

Variants:
- `Sender` can be copied, for several producers. `Receiver` can be copied too,
  for several consumers. (Go's channels are multi-producer, multi-consumer.)
  The endpoint types also give direction, like Go's `chan<-` and `<-chan`.
- `capacity: 0` is a rendezvous channel: `send` waits for a receiver.
- There's no unbounded channel by default. A bounded channel never allocates
  after creation. An unbounded one would `use alloc` and throw `AllocError` on
  `send` (**Open:** worth providing?).
- `try_send` and `try_recv` never block.

### `select` without syntax

Go's `select` is syntax. Here it's a library function. Each case maps what it
receives into one enum the caller defines, and the result is handled with an
ordinary `match`:

```
enum Event {
	job(Job)
	quit
	tick
}

loop {
	match select(.{
		rx_jobs.case(Event.job),
		rx_quit.case(fn(_) { Event.quit }),
		task.after(1s).case(fn(_) { Event.tick }),
	}) {
		job(j) => process(j)
		quit => break
		tick => report()
	}
}
```

- The case list is a comptime tuple, so `select` is specialized for exactly
  these cases, with no allocation and no dynamic dispatch.
- The case bodies (`Event.job`, the small functions) only build a value. The
  real work happens in the `match`, so there's no hidden control flow inside
  `select`.
- **Fairness:** when several cases are ready, Go picks one at random. We
  propose a rotating start instead, which is just as fair and deterministic.
  **Open.**
- **Open:** send cases. A value offered to a send case that doesn't fire has
  to be given back to the caller. It can be done, but the API is awkward.

### Waking up the right kind of waiter

One channel can connect a green thread to an OS thread (for example a
[dedicated task](#green-threads-that-need-a-fixed-os-thread) feeding the
scheduler). Each waiter registers how it must be woken: a green thread is put
back in the run queue, and an OS thread is woken by a futex (or the platform's
equivalent). This choice only happens when someone actually has to wait. The
fast path (a value is ready) doesn't depend on who's waiting.

A [hand-written event loop](#io) can wait on channels too: a receiver can
provide a pollable handle (an `eventfd` on Linux), which is registered in
`std/poll` next to sockets. Again, the scheduler gets no private shortcut.

When the program has no concurrency at all, channels are
[downgraded](memory.md#downgrading-when-theres-no-concurrency) like `Mutex`
and `Atomic`: no atomic instructions.

### The rest of the toolbox

| Go | Lode | Notes |
| --- | --- | --- |
| `sync.WaitGroup` | Not needed | A `scope` waits for everything spawned in it |
| `errgroup.Group` | A `scope` whose tasks can throw | The first error cancels the rest of the scope, and the scope rethrows it |
| `sync.Mutex`, `RWMutex` | `Mutex[T]`, `RwLock[T]` | The data is inside the lock ([data-race freedom](#data-race-freedom)) |
| `sync.Once` | `Once[T]`, `Lazy[T]` | Ties in with lazy globals ([memory.md](memory.md#globals)) |
| `sync.Cond` | `Condvar` | Tied to a specific `Mutex[T]` so it can't be used with the wrong lock |
| Semaphore (`x/sync`) | `Semaphore` | |
| `time.After`, `time.Ticker` | `task.after(d)`, `task.ticker(d)` | Receivers, so they work in `select` |
| `context.Context` | Implicit cancellation context, see below | |
| `sync/atomic` | `Atomic[T]` | |

Each is linked only if used, and all of them work across green and OS
threads.

### Cancellation and deadlines

Go passes `ctx` explicitly through every call, which is noisy, and it's easy to
forget to check it. Lode uses the same implicit context mechanism as
allocators and schedulers:

- Every `scope` carries a cancellation state. Cancelling the scope (by error,
  by deadline, or explicitly with `s.cancel()`) cancels everything spawned in
  it, recursively.
- **Every point where a green thread can park** (I/O, channel operations,
  lock waits, `sleep`) checks it and fails with `Cancelled`. Because those
  operations already `throw`, cancellation needs no new control flow: it's an
  error like the others.
- Deadlines: `scope(.{deadline = 5s}) s { ... }`.
- CPU-bound code that never parks can check explicitly with
  `task.check_cancelled()`. **Open:** should preemption points also check?

## I/O

**Status:** Decided that there are separate implementations and that
hand-written event loops are supported. The package layout is Proposed.

Blocking I/O and green-thread I/O are different enough to be **separate
code**, not one implementation that checks at run time which mode it's in. A
third style is supported as a first-class option: a single thread doing
**non-blocking I/O by hand**, managing its own buffers per file descriptor.

Everything is built on one shared bottom layer, and the green-thread scheduler
gets no private shortcuts. Anything it does, a hand-written event loop can do
too.

```
            ┌──────────────────┬───────────────────┬───────────────────────┐
  styles    │ blocking         │ green threads     │ hand-written loop     │
            │ std/io, std/net  │ std/task/io, ...  │ user code             │
            └────────┬─────────┴─────────┬─────────┴───────────┬───────────┘
                     │                   │ (reactor, layer 2)  │
            ┌────────┴───────────────────┴─────────────────────┴───────────┐
  shared    │ std/poll: readiness (epoll, kqueue), completion (io_uring)    │
            │ std/os:   typed syscalls, non-blocking fds, errno as errors   │
            └──────────────────────────────────────────────────────────────┘
```

| Layer | Package (names Open) | What it offers |
| --- | --- | --- |
| OS | `std/os` | Typed, safe wrappers over syscalls: `read`, `write`, `open` with `O_NONBLOCK`, and so on. "Would block" is an ordinary error value (`.would_block`), not a special case. |
| Polling | `std/poll` | A portable readiness API (register an fd with an interest, wait for events), plus target-specific completion APIs such as io_uring. |
| Blocking | `std/io`, `std/net`, `std/fs` | Files and sockets that block the calling OS thread. No scheduler needed. |
| Green threads | `std/task/io` and similar | The same kinds of objects, but a call that would block parks the green thread and hands the fd to the reactor. Requires `uses task`. |
| Hand-written | *(user code)* | A loop over `std/poll`, with the program's own per-fd buffers and state machines. |

A hand-written loop needs nothing beyond `std/os` and `std/poll`: no scheduler,
no green-thread stacks, no `uses task`.

### Choosing the mode by type, not by a check

Code that doesn't care which mode it runs in is written against **traits**
(`Reader`, `Writer`, `BufReader` and so on), and the caller's concrete type
picks the implementation:

```
fn copy[R: Reader, W: Writer](inout src: R, inout dst: W) throws -> u64 { ... }

copy(&file, &stdout)              // blocking file → blocking stdout
copy(&conn, &log)                 // inside task.run: a green-thread socket
```

Generics are resolved at compile time, so there's no run-time check of any
kind. A program with no scheduler contains only blocking code (the hello-world
benchmark stays at 2 syscalls).

Mistakes this catches at compile time:
- Using green-thread I/O outside `task.run` is an error: `uses task` isn't
  satisfied.
- Calling blocking I/O from inside a green thread stalls every green thread
  on that OS thread. The compiler can see it (a blocking call reachable from a
  function that `uses task`) and warns. **Open:** warning or error?

### Protocols written without I/O

**Status:** Proposed

So that parsers and protocols (HTTP, TLS, compression) work in **all three**
modes, the standard library writes them as **I/O-free state machines**: they
take bytes in and give bytes and events out, and never read or write
themselves. Each I/O mode wraps them in a thin driver.

This is what makes the hand-written style practical. A program managing its
own buffers per fd feeds received bytes into the same HTTP parser the blocking
and green-thread servers use. Nothing is written three times.

## Beyond v1

- Novel synchronization primitives (a goal from the original concept).
- SIMT/GPU targets (a non-goal for v1, see [concept.md](concept.md#non-goals-for-now)).
- Interrupt handlers as a concurrency context. They're a kind of thread with
  strict rules (no allocation, bounded stack), and `uses alloc` and stack bounds
  already give us the tools to check them.
