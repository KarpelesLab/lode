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
	type Rune
	fn decode(bytes: []u8) -> ?(Rune, usize)     // next rune and its length
	fn encode(r: Rune, set out: [4]u8) -> usize  // Open: max rune length per encoding
	fn validate(bytes: []u8) -> bool
}
```

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
