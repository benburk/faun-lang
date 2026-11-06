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
a character, so a match never starts inside one. There is no indexing and
no slicing by position. `len` counts bytes; `pad_start` and `pad_end` count
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

### Why no slicing by position?

A byte offset into text has no use that is both correct and about text.
Fixed-width fields are byte work, and cutting text for display needs
characters, which a byte count is not. So a program that wants the middle
of a string says it is working in bytes: `to_utf8`, then `take`, `drop` or
`split_at` on the list, and `from_utf8` back, where a failure is a real
question about what the bytes turned out to be. Ori tried a `Str.take`
that cut to the nearest character boundary and removed it. It was sound,
but it answered a question about letters with a count of bytes, and had no
`Result` to say so.

The cost is ceremony for programs that parse fixed-format ASCII. The
recourse is the same round trip, or working on `List(U8)` throughout, as
the host and `run_stdin!` already hand it.

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
the definition is specialized, as `&` on `Bool` is. See
[quoted strings](../proposals/approved/quoted-strings.md).

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

### Why is `cmp` byte order rather than a collation?

A program needs one neutral order to sort strings, key a `SortedMap` and
print deterministic output. Every collation is an opinion about a locale,
case and normalization. Byte order is cheap, documented, agrees with
Unicode scalar order, and claims to be nothing more. A program that wants a
reader's order sorts with `sort_on` over a key it chooses. Ori first
shipped no string order at all for this reason. Every program that sorted
names then had to work around the gap, so it gained this one.

## Related

- [Numbers](numbers.md): character literals as numerals, and the `U8`
  bytes a string holds
- [Collections](collections.md): `List`, which `Str` wraps, and hashing
- [Methods](../forms/methods.md): structural `to_str` and asking for it by
  signature
- [Pattern matching](../forms/pattern-matching.md): string patterns as
  equality tests, and coverage
- [Effects](../forms/effects.md): the host streams, which carry bytes
