# Compression

This note owns what writing checksums, DEFLATE and PNG in Faun taught: a
large, exactly specified workload of bit-level work on `U8` and `U32`, big
byte buffers and random access into a window, with outside programs as
oracles. The libraries are in-tree under
`crates/frontend/examples/libraries/`: `crc`, `flate`, and to come,
`png`. Each finding is a workaround the code carries, an error that
misled, or something the standard library lacked, with what it cost and
where it stands.

## Findings

### A constant is worked out again wherever it is named

A top-level constant that is not a literal, such as CRC-32's 256-entry
table built by `List.range(256).map(…)`, is computed afresh at every use.
Named inside the byte loop, the table was built once a byte: 4 MB took
6.3 seconds, and 10 seconds through a recursive walk rather than a `fold`.
Bound once to a local and passed down, the same loop took 12 ms.

Nothing says so: no note mentions it, and the program reads as if the
table were a value. The workaround, in `crc.fn`, binds the table at the
top of `update` and threads it through the walk as a parameter. The fix
belongs in the compiler: a constant without parameters is worked out once,
before `main` or on first use, as Haskell's CAFs and Rust's `static`s are.

### Random access into a list is constant time

`List.get` reads a buffer at an offset: 4 million reads at scattered
indices into a 4 MB list took 28 ms, so a DEFLATE window can be a list
indexed directly. `get` answers a `Result`, so a read that cannot miss
still pays for `.ok_or(0)` in the source.

### A failed expectation does not say what it saw

`expect a == b` that fails points at the line, but prints neither side, so
finding the right Adler-32 of a test vector took a run of Python. A failed
`==` could print both values, as Rust's `assert_eq!` does. Inflate's first
fixed-Huffman test failed the same way, and finding that it answered
`Err(BadDistance)` took a throwaway program that printed it with
`faun run`.

### A natural in a hot loop costs several times a word

"Small values cost almost nothing" holds for holding a `Nat`, not for
working one out where the compiler cannot bound it. Inflate's bit
position grows with the input, so every `bit / 8`, `bit % 8` and
`bit + length` took the natural's general path, calls to `nat.to_word`,
`nat.from_word` and `nat.div_word` in the profile. Reading 23 million
9-bit fields from a 20 MB buffer took 280 ms with the position a `Nat` and
45 ms with it a `U64`, the loop otherwise the same.

Inflate carries the workaround: positions are `U64` (named `Bit` in
`flate.fn`), Huffman tables `List(U16)`, the length and distance tables
`List(U32)`, and each crosses to `Nat` only to index a list, with
`.to_nat()`. On 50 MB of text that took inflate from 1.10 s to 0.63 s.
The cost is a conversion at every boundary, since `List.get`, `len` and
`take` speak `Nat`. A fix in the compiler would bound a position by what
it indexes, `input.len() * 8`, which range analysis does not yet carry
through a loop's state.

### Bitwise and binds as loosely as Boolean and

`&` on `Nat` and the words is the method `and`, at the precedence of
`Bool`'s `&`, below comparison. So `flags & 4 == 0` reads as
`flags & (4 == 0)`, refused with

```text
error: mismatched types
   |
   |   if header & 1 == 1 then …
   |      ------   ^^^^^^ expected `Nat`, found `Bool`
```

which names the right place but not the cause. Inflate wrote it eight times
before the first refusal, and twice more after. Every flag test in `flate.fn` is
parenthesized, `(flags & 4) == 0`. C has this precedence and it is a
known trap there; Rust binds `&` above `==`. Either the operator note
gives the bit operators their own level above comparison, or a test
`x & k == v` on numbers is refused with a message saying to parenthesize.

### A binding cannot leave, and says what to write

`[cmf, flg, *] = input else return Err(Truncated)` is refused with "a
binding takes no `else`", and a help line giving the form that works,
`input is [cmf, flg, *] else return …`. The message is the model for the
precedence one above.

### Results and tuples answered per symbol cost nothing

Decoding a symbol answers `Result((U64, Bit), …)`, a tuple in a result,
once for every symbol of the stream, and its caller takes it apart with
`?`. Writing the decode out by hand in the loop, with no result and no
tuple, changed 1.10 s to 1.09 s: the compiler builds neither. The clean
form stays.

### Growing the output where it lies is cheap

Inflate's output is its window: a literal is `out.append(byte)`, and a
match appends a byte at a time from `out.get(from)`, so an overlapping
match repeats what it writes, as RFC 1951 asks. A hundred million
appends, half of them reading back from the list, took 170 ms, since
nothing else holds the buffer.

### Narrowing between words goes through `Nat`

Widening is complete: `U64.of_u8`, `of_u16`, `of_u32`, and the same on
`U32` and `U16`. Narrowing is not: `U64` has `to_u32` and `to_u8` but no
`to_u16`, and `U32` and `U16` have no `to_` at all, so a narrowing that
is not there is `U16.of_nat(x.to_nat())`.

### A test of binary output builds natively

The reference interpreter's test runner hands back standard output as a
`String`, so a program writing bytes cannot be checked through it. The
flate test builds its gzip example with `faun build` and runs that,
which ties it to x86-64 Linux as the benchmark-game test is.

### `just format` ends every text file with a newline

The format recipe appends a newline to any file ripgrep reads as text and
finds without one. The fixtures' inputs are bytes compared exactly, and
three of them read as text, so formatting changed them and every test of
them failed, the test of a single byte reading two. An `.ignore` beside
them, as the tree-sitter grammar's generated files have, keeps the recipe
and searches away.

### Profiling works

`faun build --symbols` names every function and chains frames, so `perf
record -g` and `perf report` read a Faun program as they would C. Every
finding above with a profile came from it. What it shows is coarse after
inlining: inflate's whole loop is one function, `codes`.

### Building a full-width table per block shows

Each dynamic block builds a literal table of 2 to the longest code length
entries, up to 32768, by `List.repeat` and a fold over the lengths: 10%
of inflate's time on 50 MB of text, for blocks of some 16000 symbols. A
first-level table of 9 or 10 bits with a second level for longer codes,
as zlib builds, would cut it; this is the next step for speed, not a
finding about Faun.

## Throughput

On x86-64, release build, over 50 MB of random bytes read from standard
input, less the 26 ms reading them takes; zlib through Python for scale:

| Checksum | Faun     | zlib      | Notes                         |
| -------- | -------- | --------- | ----------------------------- |
| CRC-32   | 500 MB/s | 9000 MB/s | one table lookup a byte       |
| Adler-32 | 230 MB/s | 5500 MB/s | sums reduced every 5552 bytes |

zlib's CRC-32 reads several bytes a step through several tables, and its
Adler-32 sums 16 bytes a step; both are open to Faun as well.

Inflate, over 50 MB of the repository's own source and notes compressed
by zlib at level 6 to a quarter of its size, measured as the gzip example
reading standard input and writing standard output, in megabytes of
output a second:

| Stream       | Faun     | zlib     |
| ------------ | -------- | -------- |
| raw DEFLATE  | 100 MB/s | 510 MB/s |
| gzip, CRC-32 | 83 MB/s  |          |

## Related

- [Collections](values/collections.md): `List` and its lookups
- [Numbers](values/numbers.md): the wrapping words
- [Memory](machine/memory.md): buffers written in place
