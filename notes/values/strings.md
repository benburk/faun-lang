# Strings

This note owns `Str`, Faun's text: what a string holds, how it is written,
spliced and compared, and the line it draws between text and bytes.
Character literals are numerals and belong to [numbers](numbers.md); this
note covers only how they meet text.

## What a string is

`Str` is valid UTF-8, held as bytes behind a private wrapper:

```ruby
Str : List(U8).(
  # The number of bytes, which for text beyond ASCII is more than the
  # number of characters.
  len : Str -> Nat
  len(Str(bytes)) -> bytes.len()
)
```

(Excerpt from `str.fn`.) No other module can name the wrapper, so every
`Str` came from a literal or through a method that kept it valid. String
syntax is the one thing outside `str.fn` that builds one directly. Bytes
become text through `Str.from_utf8`, which answers `Err(InvalidUtf8)` for
ill-formed input, or `Str.from_ascii`; text becomes bytes through
`to_utf8`. Machine lowering holds a `Str` as its list is held, a buffer and
a length.

The library reads text with `is_empty`, `split`, `lines`, `trim`,
`starts_with`, `ends_with`, `drop_prefix` and `drop_suffix`, and writes it
with `concat`, `pieces.join(separator)`, `repeat`, `pad_start`, `pad_end`
and `Str.hex(bytes)`. Matching and cutting go byte by byte. That is sound
for text, since no byte that continues a character equals one that begins
a character, so a match never starts inside one. There is no indexing; a
slice by byte position, `text.slice(start, end)`, answers `Err(NotAtBoundary)`
where either end falls inside a character, so a slice is always text. `len`
counts bytes; `pad_start` and `pad_end` count
Unicode scalars.

```ruby
expect "é".len() == 2 & "🦌".len() == 4
expect "é".pad_start(3) == "  é"
expect Str.from_utf8([0xc3]) == Err(InvalidUtf8)
expect Str.from_utf8([0xc3, 0xa9]) == Ok("é")
expect "a,b,,c".split(",").join("-") == "a-b--c"
```

`cmp` is byte order: the first differing byte decides, and a string comes
before every string extending it. On UTF-8 that is Unicode scalar order. It
is not a collation, so `"Zebra" < "apple"` and `"10" < "9"`. `equals` is
its view, and `hash_into` feeds the bytes, so a `Str` keys a `Map`.

## Literals and splices

A literal is written in double quotes and may span lines, its line breaks
part of the text. It escapes `\n`, `\r`, `\t`, `\0`, `\\`, `\"`, `\'` and
`\$` as themselves, and `\u{...}` writes any scalar by its one to six
hexadecimal digits, as Rust does.

`${value}` splices a value's text into the string: a `Str` as it is, and
anything else by its `to_str`. The pieces are joined with `concat`. A width
pads the spliced text with spaces: `${value:<12}` is that text's
`pad_end(12)`, and `${value:>7}` its `pad_start(7)`. The width is a numeral,
and text already that wide is left whole.

```ruby
Celsius : Int.(
  to_str : Celsius -> Str
  to_str(Celsius(degrees)) -> "${degrees}°C"
)

expect "${1 + 2} and ${True}" == "3 and True"
expect "${Celsius(-4)}" == "-4°C"
expect "[${"ab":<4}|${7:>3}]" == "[ab  |  7]"
expect "${1234.5678.to_fixed(2):>9}" == "  1234.57"
expect "\u{1F98C}" == "🦌" & "\${x}".len() == 4
expect "${"ab"}" == "ab" & "ab".to_str() == "\"ab\""
expect "${["a", "b, c"]}" == "[\"a\", \"b, c\"]"
```

`Bool`, the numbers, `Str` and `List` have `to_str`. A closed record, a
tuple and a closed tag row have one without declaring it, and a declared
type asks for the structural one by writing its signature alone. A value
whose type has none cannot be spliced: `` `Secret` has no field or method
`to_str` ``.

A `Str`'s `to_str` writes it as a literal would: in double quotes, with
`"`, `\`, a `$` opening `${`, and control characters escaped, so a string
among a list's elements, a tuple's members or a tag's fields reads as one,
and `["a", "b, c"]` is not taken for three. Whether a splice's value is a
`Str` is known once its type is, so a generic definition splicing a value
it was handed shows a `Str` as its text too, and asking `x.to_str()`
instead gives the literal.

A string in a pattern is a test of equality, asked before the clause's
guard. It never covers anything, so clauses over strings end in a
catch-all:

```ruby
verb : Str -> Nat
verb("get") -> 1
verb("put") -> 2
verb(_) -> 0
```

## Text and bytes

Where data may not be text, it stays `List(U8)`. The host's streams read
and write bytes; `read_to_str!` is the one read that validates, answering
`InvalidUtf8` among its errors. The `run_stdin!` runner hands a program its
input as `List(U8)`, so a program hashing or decoding it pays for no check,
and one that wants text asks `Str.from_utf8` itself.

A character literal is a numeral, its scalar value, and may name it by
number, `'\u{e9}'`. At a `U8` it must be ASCII, below 128, so `'a'` matches
the byte `"a"` holds. Any other character is more than one byte in UTF-8,
so it is refused there, with its bytes shown and the two ways out offered:

```
error: `'é'` is not one byte in UTF-8, so it cannot be a `U8`
  = note: `'é'` is 2 bytes in UTF-8: `[0xc3, 0xa9]`
  = help: write `0xe9` for the byte 233, or `"é".to_utf8()` for its encoding
```

At `Nat`, `Int` and the wider words it stays its scalar value: `'é'` at a
`U32` is 233.

## Rationale

### Why is `Str` bytes behind a wrapper?

UTF-8 is what files, terminals and networks carry. Holding text as UTF-8
means reading and writing it costs no conversion, and ASCII, most of what
programs compare against, is one byte a character. Keeping the bytes
behind a private wrapper makes validity an invariant held at one module:
`from_utf8` checks once, and every method after it may assume. And since
`Str` is a `List(U8)` underneath, it needs no primitive of its own. It gets
the list's buffer representation and the list's operations inside
`str.fn`.

The cost is that `len` is bytes, not characters, and there is no constant
time "nth character". Grapheme clusters, which is what a reader calls a
character, are not modelled at all. Python's strings index by code point
and Swift's by grapheme cluster; both pay for it in representation or in
time. The names say which unit an operation counts.

### Why is slicing by position checked?

A byte offset into text is about bytes, not letters: cutting text for
display needs characters, which a byte count is not. But fixed-format text,
a nine-letter word read as three thirds or a column of a report, is cut by
position, and without a slice every such program went through the bytes,
`Str.from_utf8(word.to_utf8().take(6).drop(3))`, to say `word[3:6]`. So
`slice` takes byte positions and answers a `Result`: `NotAtBoundary` where a
position falls inside a character, `OutOfBounds` past the end. A slice is
always text, which is what the bytes round trip guaranteed, and the
`Result` says what Ori's `Str.take` could not: it cut to the nearest
character boundary, quietly answering a question about letters with a
count of bytes, and was removed.

The cost is a `Result` at every slice, `word.slice(3, 6).ok_or("")`, where
the text is known to be ASCII. The recourse, where many cuts are made, is
working on `List(U8)` throughout, as the host and `run_stdin!` already hand
it.

### Why are splices `to_str`?

Because `to_str` is already how every value says itself, so a splice adds
no second protocol. Faun has no traits. A splice is a method call, resolved
by the value's type as any call is, and generic code that splices asks for
`to_str` through an ordinary `where` bound. Records, tuples and tag rows
have it structurally, so `"${result}"` works for an `Ok(48)` or an
`Err(Malformed)` with nothing declared.

The cost is one text per type. There is no second form for debugging, like
Rust's `{:?}`, and no format language beyond a padding width. Number
formatting is a method call inside the splice:
`${x.to_fixed(2)}`. Layout belongs to text, so the width pads whatever text
it is given.

### Why does a `Str`'s `to_str` quote it, when its splice does not?

Because a value inside another is written by its own `to_str`, and a
string written bare there cannot be told from the text around it:
`["a", "b, c"]` and `["a", "b", "c"]` both came out `[a, b, c]`, and
`Ok("")` came out `Ok()`. With one text per type, the one a string has to
give is the one that reads back as that string, as Rust's `Debug` and
Python's `repr` give. A splice is where text is being built, and there a
string is wanted as itself, so a splice of a `Str` is the string. Nothing
else changes: a number, a tag or a record is written the same either way.

The cost is that `${x}` and `x.to_str()` differ for a `Str`, and only for a
`Str`, which a definition writing its own `to_str` has to choose between: a
splice for a part shown as text, `"${degrees}°C"`, and `to_str` for one
shown as a value. Where the type is generic, the splice is decided when
the definition is specialized, as `&` on `Bool` is. A `Str`'s `to_str`
also walks its bytes and builds a new string, where it once answered the
string it had.

### Why not a second member for a value shown inside another?

Rust has `Debug` beside `Display`. In Faun every type with `to_str` would
need the second member too, a declared type's own `to_str` a matching one,
and generic containers a bound on it: a second protocol for one type's
sake. Quoting only in the `to_str` the compiler makes for records, tuples
and tags would not do either: `List` and `Result` are written in Faun and
cannot ask whether an element is a `Str`, so a list of strings would stay
ambiguous.

### Why is a splice of a `Str` decided at specialization?

Because only then is its type always known. Decided where it is checked, a
generic definition splicing a value it was handed would quote a `Str`, and
the runners, which splice what a program answers, would print a program
answering a `Str` in quotes. The splice is checked as a `to_str` call, so
a generic one still asks `to_str` through its `where` bound.

### Why `${…}` rather than `{…}`?

So that braces are just braces. JSON, CSS and code in a string need no
doubling, as they would under Python's or Rust's `{name}`:
`"body { color: ${color}; }"` reads like its output. `${` almost never
occurs in text, and `\$` escapes it where it does.

### Why must a character at a `U8` be ASCII?

Because a `U8` in Faun is a byte of UTF-8 text, and a byte from 128 to 255
is never a whole character there. `'é'` at a `U8` used to be 233, which is
`é` only in Latin-1: `byte == 'é'` compiled and could never match a byte of
a Faun string, since `"é"` holds `0xc3` then `0xa9`. Refusing it turns that
silent mismatch into an error naming the bytes. The cost is that a program
that does mean the byte 233 writes `0xe9`, which says what it means. At the
wider types a character is its scalar value, which is what a code point is.
No program in the corpus wrote a non-ASCII character literal at any type.

Making `'é'` at a `U8` its UTF-8 bytes was the other way to keep it, but a
character would then be a list where a byte is wanted, which no position
can hold.

### Why is `cmp` byte order rather than a collation?

A program needs one neutral order to sort strings, key a `SortedMap` and
print deterministic output. Every collation is an opinion about a locale,
case and normalization. Byte order is cheap, documented, agrees with
Unicode scalar order, and claims to be nothing more. A program that wants a
reader's order sorts with `sort_on` over a key it chooses. Ori first
shipped no string order at all for this reason. Every program that sorted
names then had to work around the gap, so it gained this one.

## History

- **2026-11-04:** a character at a `U8` must be ASCII. `'é'` there had been
  233 and `'€'` out of range; both are refused now, naming their bytes. The
  lexer began reading `'\u{…}'`, which the standard library's README and
  the tree-sitter grammar already described. Found while writing this note,
  which had to set `'é'` at a `U8` as 233 beside `"é".to_utf8()` as
  `[0xc3, 0xa9]`.
- **2026-11-05:** a `Str`'s `to_str` quotes it, so a string inside a value
  reads as one: `["a", "b, c"]` had printed `[a, b, c]`, and a runner's
  `Ok("")` had printed `Ok()`. clap's help, which showed a default by its
  `to_str`, splices it instead, so `[default: <stdout>]` stays unquoted.
- **2026-11-11:** `Str.slice` took the place of the bytes round trip for
  cutting text by position, checked at both ends, after a word-squares
  program needed `word[3:6]` three times over.

## Related

- [Numbers](numbers.md): character literals as numerals, and the `U8`
  bytes a string holds
- [Collections](collections.md): `List`, which `Str` wraps, and hashing
- [Methods](../forms/methods.md): structural `to_str` and asking for it by
  signature
- [Pattern matching](../forms/pattern-matching.md): string patterns as
  equality tests, and coverage
- [Effects](../forms/effects.md): the host streams, which carry bytes
