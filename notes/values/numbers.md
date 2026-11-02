# Numbers

This note owns Faun's integers: how a numeral gets its type, the
arbitrary-precision `Nat` and `Int`, the fixed-width words `U8`, `U16`, `U32`
and `U64`, and what arithmetic answers at its edges, such as subtraction
below zero, division by zero and the sign of a remainder. Floats have their
own note.

## Numerals

A numeral has no type of its own. Its position decides, and the numeral is
built through that type's `of_nat`; at `Nat` the numeral already is the
value. Hexadecimal, binary and character literals are other spellings of
the same thing, a character standing for its Unicode scalar value:

```ruby
double(x) -> x.mul(2)

expect double(21) == 42
expect double(U8.of_nat(200)) == 144
expect 0xff == 255 & 0b1101 == 13 & ')' == 41
```

The `2` in `double` is whatever `x` is, so `double` serves every type with a
`mul`. Where nothing decides, a numeral is a `Nat`, and a negated one an
`Int`: `(-3).abs()` is `3`.

A numeral may be a `Nat`, `Int`, `U8`, `U16`, `U32` or `U64`, and nothing
else. A type does not become numeric by defining `of_nat`; it is built with
an explicit call such as `Money.of_nat(7)`. Anything else is refused:

```
error: a numeral cannot be a `Bool`
  = note: a numeral is a `Nat`, `Int`, `U8`, `U16`, `U32`, or `U64`
  = help: convert a value with `of_nat`
```

A word's module bounds what may be written with a private value beside the
type, `numerals_below = 256` in `u8.fn`. `300` written where a `U8` is
wanted is refused, as pattern or expression, and so is `-1`. The bound is
on what is written, not on what is computed: `U8.of_nat(300)` is `44`,
since wrapping is what a `U8` means. `Nat` and `Int` take a numeral of any
size, so `0x10000000000000000` is `18446744073709551616`.

A numeral with a point, `1.5`, belongs to the floats, and a numeral without
one never does ([floats](floats.md)). A numeral in a pattern is a test of
equality ([pattern matching](../forms/pattern-matching.md)).

## `Nat` and `Int`

Both are ordinary types in the standard library, with arithmetic written as
clauses over their constructors:

```ruby
Nat : [Zero, Succ(Nat)].(
  sub : (Nat, Nat) -> Nat
  sub(0, _) -> 0
  sub(m, 0) -> m
  sub(Succ(m), Succ(n)) -> m - n
)

Int : [Pos(Nat), NegSucc(Nat)]
```

(Excerpts from `nat.fn` and `int.fn`.) `NegSucc(n)` is `-(n + 1)`, so zero
is only `Pos(0)` and every integer has one spelling. `Int.abs` answers a
`Nat`; `Nat.from_int` answers `Err(Negative)` for a negative one.

`Nat`, `Int` and the words define `+`, `-`, `*`, `/` and `%`, and a `cmp`
that `<`, `==` and the rest are views of
([operators](../forms/operators.md)). At the edges:

| Expression             | Answer    | Rule                             |
| ---------------------- | --------- | -------------------------------- |
| `3 - 5`                | `0`       | natural subtraction is monus     |
| `7 / 0`, `7 % 0`       | `0`, `7`  | the same for every type          |
| `-7 / 3`, `-7 % 3`     | `-3`, `2` | Euclidean: no negative remainder |
| `7 / -3`, `7 % -3`     | `-2`, `1` | the divisor's sign is not kept   |
| `U8.of_nat(3) - 5`     | `254`     | the words are rings              |
| `U8.of_nat(255) * 255` | `1`       |                                  |

Each row is checked by `faun test`. `a = (a / b) * b + a % b` holds for
every `a` and `b` of every type, zero included.

## How a `Nat` runs

The clauses specify the operations; they are not how they run. Barb, the
compiler's optimizing tier ([Barb](../barb.md)), recognizes a definition by
the shape of its equations, checked by induction, and answers a call of it
as the one operation it is: addition, monus, multiplication, division,
remainder, comparison, power, and the bitwise walks. It never reads a name.
A program's own counting type, spelled nothing like `Nat`, is recognized
the same way:

```ruby
Tally : [Empty, Mark(Tally)].(
  plus : (Tally, Tally) -> Tally
  plus(Empty, y) -> y
  plus(Mark(x), y) -> Mark(plus(x, y))

  times : (Tally, Tally) -> Tally
  times(Empty, _) -> Empty
  times(Mark(x), y) -> plus(y, times(x, y))
)
```

`faun emit barb` shows `plus` as `<add>` and `times` as `<mul>`, and a
product of two tallies of a million marks each is one multiplication.

Machine lowering then holds a natural in one word. A natural small enough
that twice it fits the word is held as twice itself, low bit clear, and
needs no allocation. A larger one is a reference-counted object of
word-sized digits, least significant first, which the runtime adds and
multiplies a word at a time and divides by Knuth's algorithm D. A sum of
two small numbers is the small sum, so the common case costs a test of the
tag. Where range analysis proves a value below a bound, it is held as a
plain word with no test: in `spectralnorm` the row index, taken from
`List.range`, is a word, while the column, a counter nothing bounds, is a
natural ([spectral-norm](../spectralnorm-performance.md)). Running out of
memory for naturals ends the program with status 2.

## The words

`U8`, `U16`, `U32` and `U64` are `Nat` behind a private constructor, and
every operation reduces its answer modulo `2^k`:

```ruby
U8 : Nat.(
  add : (U8, U8) -> U8
  add(U8(a), U8(b)) -> U8((a + b) % 256)

  sub : (U8, U8) -> U8
  sub(U8(a), U8(b)) -> U8((a + 256 - b) % 256)
)
```

(Excerpt from `u8.fn`.) Division and remainder work on the unsigned
representatives, with the same zero rules, and so does the order. The words
have `&`, `|`, `^`, `!`, `shift_left`, `shift_right`, `rotate_left` and
`rotate_right`; a shift by the width or more is zero. `Int` has no bitwise
operations. `of_nat` wraps; `from_nat` refuses instead, `U8.from_nat(256)`
being `Err(TooBig)`; and widening, `U64.of_u8`, cannot wrap.

Each word is held in machine words, and so is its arithmetic. A `U32`'s
sums and products are worked out at 64 bits and narrowed after. A `U64`'s
exact sum or product can pass 64 bits, but its low 64 bits are the sum or
product of its operands' low bits, so the compiler recognizes the
remainder by 2^64 and works it out at 64 bits, wrapping: one `add` or
`imul` on x86-64, and the same words carried on wasm32 and the 6502. A
hash loop of `U64` multiplications that took 2.6 s as naturals takes
0.01 s.

## Rationale

### Why does a numeral take its type from context?

So that one spelling serves every integer type, with no suffixes like
Rust's `3u8` and no casts. Generic code needs nothing more: `double` above
works for naturals and bytes alike. The list of types is closed so that a
numeral always means an exact integer: each type on it either holds the
written value or refuses it at compile time. Haskell lets any `Num`
instance take a literal through `fromInteger`, so `300 :: Word8` is
`44`, with at most a warning.

The cost is that a type of your own takes no numeral; you write
`Money.of_nat(7)`, a conversion the reader can see.

### Why is `Nat` arbitrary-precision rather than a machine word?

Because overflow is a silent wrong answer, and Faun has no trap to turn it
into a loud one. A fixed-width `Nat` would have to wrap, which is what the
words already are, so `Nat` keeps the other meaning: a count is the count.
Spectral-norm shows the difference. C's 32-bit `int` version of its matrix
entry overflows past about `n = 23,000`, and Faun's `Nat` version neither
wraps nor needs a declaration.

What keeps it fast is that most numbers are small. Small naturals are held
inside the word, and range analysis drops the tag test where it can prove a
bound. Recognizing operations by shape rather than by name keeps the library
the specification and gives a user's own types the same speed. A near miss
is safe: the definition runs as written.

The cost is real where nothing bounds a value. Spectral-norm's integer
entry took 1.04 s at `n = 1000`, against 0.048 s for the same program
computing it in `F64` and 0.031 s for C. A walk that matches no recognized
shape runs as written, one call per unit: `again(Succ(n)) -> again(n) + 1`
nests a million calls for a million and overflows the stack. Where a value
has a known width, a word is the recourse: n-body holds its step count in a
`U32`, as C holds it in an `int`, so the loop counts in a machine word
([n-body](../nbody-performance.md)).

### Why is natural subtraction monus?

A `Nat` has no negatives, and `sub` must answer one for every pair, so it
stops at zero. Monus is what the clauses say: take one from each until
either runs out. The standard library leans on it.
`Str.pad_end(text, width)` appends `" ".repeat(width - scalars(text))`
spaces, and text already wider gets none, with no comparison written.

The alternatives each cost more. Answering an `Int` would turn every
countdown's type over, and answering a `Result` would put a `?` on every
subtraction. The cost of monus is that a mistaken `a - b` with `b > a`
answers 0 quietly. When the sign matters, compare first or work in `Int`:
`Int.of_nat(3) - 5` is `-2`.

### Why are the words rings that wrap?

Because the programs that use fixed widths want modular arithmetic.
Hashes, checksums, random generators and ciphers are written in it.
`md5.fn` adds four `U32`s and rotates in one line, and the standard
library's hasher multiplies a `U64` by a prime:

```ruby
(d, b + (a + f + k + words.get_or(g, 0)).rotate_left(s), b, c)
```

Wrapping is the definition, not a failure, so there is nothing to detect,
and every word has an additive inverse: `U8.of_nat(0) - 1` is `255`. Rust
traps on overflow in debug builds and wraps in release builds, so the same
program means two things. A `U8` means one thing everywhere.

The cost is that a word is not a small `Nat`, and the two should not feel
interchangeable. `numerals_below` catches the written mistake, `U8` at
`300`. `from_nat` is the checked narrowing for a value computed at run
time.

### Why does division by zero answer zero, and `a % 0` answer `a`?

Faun has no panic, so every arithmetic operation must answer something.
Zero is the quotient that keeps `a = (a / b) * b + a % b` true at `b = 0`,
provided `a % 0` is `a`. Lean's natural division does the same. Totality
also leaves the optimizer free to drop a division nothing reads, or to move
it. A division that could trap would be an effect, fixed in place
([computation](../computation.md)).

The cost is that a zero divisor gives a plausible answer rather than an
error, so test the divisor where zero means a mistake. Earlier designs
tried the other options. One trapped and offered checked variants, which
gave pure code a way to crash. Another answered `a % 0 = 0`, which breaks
the identity.

### Why Euclidean signed division?

So the remainder is never negative: `0 <= a % b < |b|` for any nonzero `b`
of either sign, and `%` is usable as an index or a position on a dial:
`-5 % 100` is `95`, not `-5`. The identity still holds, and on non-negative
operands the answers are `Nat`'s.

The cost is surprise for anyone from C, Rust or Java, whose `/` truncates.
`-7 / 2` is `-4` here and `-3` there. Python floors, which agrees for a
positive divisor but not a negative one: `7 % -3` is `-2` in Python and `1`
in Faun. Rust's `div_euclid` and `rem_euclid` give Faun's answers.

## Related

- [Floats](floats.md): the numerals with a point, and conversions from
  integers
- [Strings](strings.md): character literals in byte positions, and
  `to_str`
- [Operators](../forms/operators.md): `+`, `%`, `&` and `<` as methods
- [Pattern matching](../forms/pattern-matching.md): numerals and ranges as
  tests
- [Types](../types.md): inference, and the `where` bounds generic
  arithmetic uses
- [Memory](../machine/memory.md): the reference counting large naturals
  share with every other cell
