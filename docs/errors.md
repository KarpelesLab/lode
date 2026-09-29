# Error handling

## Requirements

- Better than Go's `if err != nil`, which is repetitive and easy to get wrong
  by ignoring or shadowing the error.
- No unwinding. Unwinding needs tables and an unwinder, which is a runtime, and
  it hides control flow.
- Errors are visible in function signatures, and they cost no more than a
  return value.

## Model: typed `throws`, compiled as return values

**Status:** Proposed

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

**Status:** Proposed

- `throws(E)` names a concrete error type.
- `throws` alone means "**inferred**": the compiler computes the union of every
  error the body can produce, as Zig does. This is convenient inside a package.
- **Public functions must name their error type**, so an internal change can't
  silently change a public API. (Open: enforce by lint or by the compiler?)
- A union of error types converts implicitly on `try` when the target set is a
  superset. Converting to an unrelated type is explicit (`catch e { throw .io(e) }`).

## Error return traces

**Status:** Proposed

In debug builds, each `try` that propagates an error records its location in a
small fixed-size buffer. When an error reaches the top unhandled (in `main`),
the trace is printed. This is Zig's best debugging feature, and it needs no
unwinding. Release builds drop it, or keep it by profile choice.

## Cleanup: `defer` and `errdefer`

**Status:** Proposed

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

## What is *not* an error

- **Absence** is `?T`, not an error. `map.get(k)` returns `?V`.
- **Bugs** (violated invariants) aren't handled at runtime at all. The safety
  model makes them compile errors where it can ([safety.md](safety.md)).
- **`abort()`** exists for "this program can't continue", but it is explicit,
  and there is no `panic`/`recover`.
