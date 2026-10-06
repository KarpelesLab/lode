# Strings

## Principles

**Status:** Decided

- UTF-8 by default.
- The **encoding is part of the string type**, so any string can be iterated as
  runes in its own encoding. A Shift-JIS string yields Shift-JIS runes.
- **No implicit conversion** between encodings. Conversion is a library, likely
  part of the standard kit but not the core.
- Character types (encodings) are defined in the standard library, not built
  into the compiler.

## Types

**Status:** Proposed

| Type | Meaning |
| --- | --- |
| `Str[E]` | A view of bytes known to be valid in encoding `E` |
| `String[E]` | An owned, growable string in encoding `E` (it allocates, see [memory.md](memory.md#allocation)) |
| `str`, `string` | Aliases for `Str[utf8]` and `String[utf8]` |
| `E.Rune` | One character in encoding `E` (`utf8.Rune` is a Unicode scalar value) |
| `[]u8` | Raw bytes, with no encoding claim |

An `Encoding` is a trait that the standard library implements for `utf8`,
`ascii`, `latin1`, `sjis`, `utf16le` and so on:

```
trait Encoding {
	type Rune: Copy + Eq
	const MAX_LEN: usize                         // the longest rune, in bytes
	fn decode(bytes: []u8) -> ?(Rune, usize)     // next rune and its length
	fn encode(r: Rune, set out: [MAX_LEN]u8) -> usize
	fn validate(bytes: []u8) -> bool
}
```

The associated constant `MAX_LEN` settles the longest rune of each
encoding ([generics.md](generics.md#traits)).

User code can define its own encodings (legacy code pages, game ROM charsets and
so on) with no compiler support.

## Validity

**Status:** Proposed

A `Str[E]` is **always valid** in `E`. That's the invariant that makes rune
iteration total, with no crash path.

- From bytes: `Str[E].from(bytes)` returns `?Str[E]`, or an error with the
  offset.
- `Str[E].from_lossy(bytes)` replaces invalid sequences, where `E` has a
  replacement rune.
- Literals are checked at compile time.

## Literals

**Status:** Proposed

Source files are UTF-8, so a literal is UTF-8 unless its type says otherwise.
Converting a literal to another encoding happens **at compile time**. This
doesn't conflict with "no implicit conversion" because it isn't a runtime
operation, and a character that can't be represented is a compile error:

```
let a = "hello"                      // Str[utf8]
let b: Str[sjis] = "こんにちは"        // re-encoded while compiling
let c: Str[ascii] = "café"           // error: 'é' is not representable in ascii
```

## Operations

**Status:** Proposed

- `s.len` is the length in **bytes**. It's never ambiguous and O(1).
- `for r in s` iterates runes of `E`. `s.bytes()` iterates bytes.
- Byte indexing `s[i]` is **not** available on `Str`, because a byte is not a
  character. Slicing `s[a..b]` needs proof that `a` and `b` are rune
  boundaries, or it returns `?Str[E]` (Open: which one).
- Grapheme clusters (what users see as "a character") come from a Unicode
  library, not the core. They need tables, and the core stays small.
- Comparing `Str[A]` to `Str[B]` is a type error. Convert first.

## In the compiler today

**Status:** Implemented subset

Until there are generics, `str` is a built-in type: a pointer and a length in
bytes, always valid UTF-8 (a literal that isn't is rejected). What works:

- string literals, placed in read-only data
- `str` locals and parameters (passed as two values: pointer and length)
- `s.len` (a `usize`; the checker knows it's at most the largest `isize`)
- `s.ptr` (a `*u8`), only in `unsafe` code
- `s.bytes()`: the bytes of `s` as a `[]u8`, a view of the same storage with
  the same length (the checker knows `s.bytes().len` is `s.len`, and a
  literal's length). It's read-only, like every slice that isn't `inout`.
  Byte indexing goes through it: `s.bytes()[i]`; `s[i]` is an error.
  It's a built-in projection of its receiver: like any view, it can be
  kept in a local, passed to functions and returned, but not stored in a
  struct field ([memory.md](memory.md#views-in-the-compiler-today)).
- slicing the bytes: `s.bytes()[i..j]` is a `[]u8`
  ([types.md](types.md#in-the-compiler-today)). `s[i..j]` is an error: a
  `str` must stay valid UTF-8, and the checker can't prove that `i` and `j`
  are character boundaries. Until that's decided (see
  [Operations](#operations)), a byte slice makes clear it may split a
  character.

- returning a `str`: a string literal (`fn Day.name(self) -> str { ...
  return "Mon" ... }`), or one that borrows from the parameters, as in
  `fn pick(a: str, b: str) -> str`; the caller's result borrows from what
  it passed, and can't be used after that changes (M8c,
  [memory.md](memory.md#views-in-the-compiler-today))
- `String` (M8c, [String](#string) below)

- `std/encoding` has the `Encoding` trait, implemented by `Utf8` and
  `Ascii`, as a library over bytes: `decode` returns a `Decoded[Rune]`
  struct, as there are no tuples
  ([packages.md](packages.md#the-standard-library-in-the-compiler-today)).

Not yet: comparing strings (`==` on `str` or `String`), slicing a `str`
itself, rune iteration, and other encodings.

## String

**Status:** Implemented (M8c): `std/string`'s `String`, in the prelude

`String` is strings.md's `String[utf8]`, named `String` until `Str[E]` and
`String[E]` exist: owned UTF-8 text on the heap
([allocation.md](allocation.md#string)).

```
var s = try String.from("hello")
try s.push_str(", world")
let ok = try s.push(0x1f600)             // a character: false for a surrogate
io.print("{} ({} bytes)\n", s, s.len())
let t = s.as_str()                       // a `str` borrowing from `s`
let f = try string.format("{} items", n) // formatted into a new string
```

- Its bytes are `s.bytes`, a `List[u8]` that's `pub let`: read everywhere
  (`s.bytes.len`, `s.bytes[i]`, proven like a slice's), changed only by
  `std/string`. Every way to add to it adds whole characters (a `str`, a
  scalar value, or bytes checked to be UTF-8), so they're always valid
  UTF-8, and `s.as_str()` can view them as a `str` with no check.
- `String.new()` allocates nothing; `String.from(s)`, `push_str`, `push`
  and `reserve` allocate (`uses alloc throws(AllocError)`), through the
  allocator the string's bytes came from once it has some.
  `truncate(n) -> bool` keeps the first `n` bytes if `n` is at a
  character's start; `clear()` keeps the storage.
- `s.len()` is the length in bytes, a method: the field is `s.bytes.len`.
- It's `Clone`, and `io.Format`: `io.print("{}", s)` writes its text.
- It's an `io.Writer` that never allocates: a `Writer`'s methods can't
  declare `uses alloc`, or every writer's callers, `io.print` too, would
  need it. It appends bytes that fit in the room left (and throws
  `no_space`, appending nothing, otherwise), and refuses bytes that aren't
  UTF-8 (`other(EILSEQ)`). `string.write_fmt(&s, fmt, args...)` formats
  twice: once into a counter, to `reserve` the room, then into the string.
  An argument whose `Format` writes more the second time is cut where the
  room ends.
- Not yet: `==` and ordering (an `impl Eq` for types with pointer fields,
  [allocation.md](allocation.md#eq-on-heap-types)), `String.from_bytes`,
  and a `Writer` whose error type can be `AllocError` (M8d's unions).

