# Error handling

## Requirements

- Better than Go's `if err != nil`, which is repetitive and easy to get wrong
  by ignoring or shadowing the error.
- No unwinding. Unwinding needs tables and an unwinder, which is a runtime, and
  it hides control flow.
- Errors are visible in function signatures, and they cost no more than a
  return value.

## Model: typed `throws`, compiled as return values

**Status:** Decided; implemented in the compiler (see
[In the compiler today](#in-the-compiler-today))

It reads like exceptions and is implemented like `Result`. This is Swift's
typed-throws model with Zig's error sets.

```
enum ParseError {
	empty
	invalid_digit(pos: usize)
	overflow
}

fn parse_u32(s: str) throws(ParseError) -> u32 {
	if s.len == 0 {
		throw .empty
	}
	var n: u32 = 0
	for (i, c) in s.bytes().enumerate() {
		if c < '0' || c > '9' {
			throw .invalid_digit(i)
		}
		n = n.checked_mul(10) ?? throw .overflow
		n = n.checked_add(u32(c - '0')) ?? throw .overflow
	}
	return n
}
```

Calling a throwing function must be marked:

```
let n = try parse_u32(s)                  // propagate to our caller

let n = parse_u32(s) catch e {             // handle here
	log("bad input: {}", e)
	return
}

let n = parse_u32(s) catch 0               // fallback value

match parse_u32(s) {                       // full control
	ok(v) => use(v)
	err(.empty) => ...
	err(e) => ...
}
```

- `try` is required at every call site that can throw, so every exit point is
  visible.
- An error value can't be silently dropped. `catch _ {}` is explicit and easy
  to grep.
- Under the hood, `throws(E) -> T` is `enum { ok(T), err(E) }` in the return
  slot. LatticeFoundry needs no exception or unwinding support for this. That
  resolves LF's open "exceptions / unwinding" question as far as Lode is
  concerned: *not needed*.

## Error sets

**Status:** Proposed. The compiler has only named error types, with no
conversion (below). M8 proposes explicit unions, `throws(A | B)`, before
inference ([allocation.md](allocation.md#out-of-memory)).

- `throws(E)` names a concrete error type.
- `throws` alone means "**inferred**": the compiler computes the union of every
  error the body can produce, as Zig does. This is convenient inside a package.
- **Public functions must name their error type**, so an internal change can't
  silently change a public API. (Open: enforce by lint or by the compiler?)
- A union of error types converts implicitly on `try` when the target set is a
  superset. Converting to an unrelated type is explicit (`catch e { throw .io(e) }`).

## Error return traces

**Status:** Proposed. Not implemented.

In debug builds, each `try` that propagates an error records its location in a
small fixed-size buffer. When an error reaches the top unhandled (in `main`),
the trace is printed. This is Zig's best debugging feature, and it needs no
unwinding. Release builds drop it, or keep it by profile choice.

## Cleanup: `defer` and `errdefer`

**Status:** Decided; implemented in the compiler

```
fn open_both(a: str, b: str) uses alloc throws(IoError) -> (File, File) {
	let fa = try File.open(a)
	errdefer fa.close()           // only runs if we exit with an error
	let fb = try File.open(b)
	return (fa, fb)
}
```

`deinit` ([memory.md](memory.md#destruction)) covers most cleanup. `defer`
and `errdefer` cover the rest.

## In the compiler today

**Status:** Implemented subset (syntax in [syntax.md](syntax.md#errors))

- `fn f(...) throws(E) -> T` (or `throws(E)` alone, for no value). `E`
  must be an enum: its variants are the errors.
- A call to a function that throws must be handled. A call that isn't is
  an error: "`f` can throw, and its error must be handled".
  - `try f()` is the call's value. On an error, the function leaves with
    it. Only a function that throws can use `try`, and only with the same
    error type: there's no conversion between error sets yet. To convert,
    catch and throw: `f() catch e { throw .io(...) }`.
  - `f() catch e { ... }` runs the block with `e` bound to the error.
    When the call's value is used (`let n = f() catch e { ... }`), the
    block must leave (`return`, `throw`, `break` or `continue`): a block
    has no value. As a statement on its own, the block may end normally.
  - `f() catch v` uses `v` when the call fails. `v` is only evaluated
    then, as with `??`.
  - `f() catch _ { ... }` doesn't bind the error. `f() catch _ {}` ignores
    it, explicitly.
  - `match f() { ok(v) => ..., err(e) => ... }` handles both. A function
    that throws and returns nothing gives `ok` without a value. Patterns
    don't nest yet, so `err(.empty)` is written as `err(e)` and a `match`
    on `e`.
- `throw value` leaves with the error `value`, of the function's error
  type. `throw .name(...)` takes the variant from it. `opt ?? throw .name`
  throws when `opt` is `none`; elsewhere, `throw` is a statement.
- `defer` and `errdefer` take a block or one statement. They run when
  control leaves the block they're in: at its end, and at every `return`,
  `throw`, `try` that fails, `break` and `continue` that leaves it, in
  reverse order. `errdefer` runs only when the function leaves with an
  error, and only in a function that throws. A `return` runs them after
  computing its value. `os.exit` ends the process without running any.
- Destruction runs at the same exits, in the same order: a variable that
  owns a value with a `deinit` is destroyed where a `defer` written at its
  declaration would run ([memory.md](memory.md#destruction)). So a `defer`
  written after `let f = os.open(...)` runs before `f` is closed.
- A `defer` body can't leave itself (`return`, `throw`, `try`, or a
  `break` or `continue` out of it), and can't assign variables declared
  outside it, or pass them `inout` or `set`. So running it changes no
  facts. It's checked where it's
  written, with the facts there about the variables nothing after it
  assigns ([safety.md](safety.md#the-fact-language)).
- It can move a variable declared outside it (pass it `sink`, as in
  `errdefer os.close(f) catch _ {}`), when the variable is assigned at
  every exit the body runs at; moving it after the `defer` is an error at
  those exits ([allocation.md](allocation.md#defer-and-errdefer)).
- An error type is an enum that's `Copy`: `catch v` and `catch _` drop the
  error, so it can't hold a value that needs destruction.
- `main` can't throw: it handles its errors and returns an exit status.
- Under the hood, a function that throws returns a result, an enum
  `{ ok(T), err(E) }` laid out like any enum
  ([types.md](types.md#in-the-compiler-today)), in storage the caller
  passes. `try`, `catch` and `match` test its tag. There's no unwinding.
- Not yet: inferred error sets (`throws` alone is an error: "name the
  error type"), conversion between error sets on `try`, error return
  traces, and `errdefer` with the error (`errdefer |e|` in Zig).

Decisions made for this subset:

- A `catch` block has no value. Lode has no block expressions; a fallback
  value is written `catch v`.
- After `catch`, a `{` following a name starts the block, as after `if`:
  `catch e {`. A struct literal fallback goes in parentheses:
  `catch (Point{x: 0, y: 0})`.
- Public functions name their error type, since nothing else is supported.
  Whether the compiler or a lint enforces that once inference exists is
  still Open.

## What is *not* an error

- **Absence** is `?T`, not an error. `map.get(k)` returns `?V`.
- **Bugs** (violated invariants) aren't handled at runtime at all. The safety
  model makes them compile errors where it can ([safety.md](safety.md)).
- **`abort()`** exists for "this program can't continue", but it is explicit,
  and there is no `panic`/`recover`. In the compiler today, it's `os.abort()`,
  a [`never`](types.md#never-in-the-compiler-today) function that exits with
  status 134 (what a shell shows for `SIGABRT`), without raising the signal
  ([packages.md](packages.md)).
