# Compression

This note owns what writing checksums, DEFLATE and PNG in Faun taught: a
large, exactly specified workload of bit-level work on `U8` and `U32`, big
byte buffers and random access into a window, with outside programs as
oracles. The libraries are in-tree under
`crates/frontend/examples/libraries/`: `crc`, `flate` and `png`. Each finding is a workaround the code carries, an error that
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
`faun run`. PNG's first Paeth expectation, and the PAM example's header
length, failed the same way, each found by working the answer out by
hand.

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
which ties it to x86-64 Linux as the benchmark-game test is; the PNG test
does the same with its PAM example.

### `just format` ends every text file with a newline

The format recipe appends a newline to any file ripgrep reads as text and
finds without one. The fixtures' inputs are bytes compared exactly, and
three of them read as text, so formatting changed them and every test of
them failed, the test of a single byte reading two. An `.ignore` beside
them, as the tree-sitter grammar's generated files have, keeps the recipe
and searches away.

### Positions want words outside inflate too

The PNG decoder kept its positions and sample values as `Nat`, and
`nat.to_word`, `nat.from_word` and `nat.mul` are 12% of decoding an
interlaced image, where each pixel's place is worked out by
multiplication. Inflate's workaround, `U64` positions, would serve here
too; it is left undone, since inflate is most of the time.

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

### The match search wants words too

Deflate confirms inflate's finding from the other side. Its search walks
a hash chain and compares bytes, every step working out a position, a
distance or a length. Written over `Nat`, compressing 5 MB of source at
level 6 took 610 ms, and the profile was the search and
`nat.to_word`/`nat.from_word`. With the search's positions, lengths and
distances `U64`, the same took 343 ms, and level 9 went from 2.4 s to
1.1 s; moving the rest of the loop to words as well took 6% more off.
`deflate.fn` names the word `Pos` and crosses to `Nat` only to index a
list.

### Nothing compares bytes several at a time

A match is found by comparing bytes from two places until they differ,
up to 258 of them. zlib compares a word or two at a time; Faun has no way
to read a word out of a list at an offset, nor a standard
`common_prefix_len(list, a, b)`, so `deflate.fn`'s `matching` compares a
byte a step, each through a `get` answering a `Result`. At level 9 the
search is 94% of the time. A `U64.of_le_bytes_at(list, i)`, or a prefix
length on lists that the compiler turns into word compares, would serve
the window here and the unfiltering of PNG rows.

### The search's loop keeps its state on the stack

The profile of level 9, annotated, shows the chain walk's ten or so live
values stored to the stack and read back each step, comparisons made into
bytes by `setb` and `movzbl` before they are tested, and small constants
loaded by `push` and `pop`. Part of the time is the memory the chain
reaches into, which C pays too, but most of the 5× to zlib at level 9 is
this. It is code generation's to fix, and the search is a good workload
for it: one function, no allocation, every value a word.

### A mask after a mixture binds before it

The hash of three bytes was first written `a.shift_left(10) ^
b.shift_left(5) ^ c & 32767`, meaning the mask to apply to the whole.
`&` binds tighter than `^`, as in C and Rust, so only `c` was masked, the
hash ran past the table, and every lookup missed. Nothing failed: the
output still read back, every expectation held, and compression was
merely 1.9 times bigger, 2.32 MB where zlib writes 1.21. Only comparing
sizes with zlib showed it, so the deflate test now holds every output to
within 2% of zlib's size at the same level. The precedence is the usual
one; the lesson is that a compressor's tests need a size oracle, not only
a round trip. The hash is now a product's top bits, which needs no mask.

### Expectations run on a budget, and a stream has a fixed cost

The test suite asks a library's expectations through the reference
interpreter, with a budget of 100 million steps for the whole file. A
round trip at every level through every container ran out of it, and the
suite said only `FuelExhausted`, from the test's support code, not which
expectation or how far it got. Natively the same expectations took 1.4 s.

What spent the budget was a fixed cost per call: deflate began each
stream by filling two tables of 32768 entries, its hash heads and its
window, so compressing one byte took 5.2 million instructions, and a
repeated `List.repeat` was the profile's top line. The tables are now
sized to the input, a hash of 8 to 15 bits and a window no longer than
the input, which halved it; most of the rest is building each block's
codes, a fixed cost of a few lists of 286. The expectations were cut to
four levels, leaving every level and container to the native test.

### A wrapper has no equality until it asks

`Level` wraps a `Nat`, and `Level.of_nat(12) == Level.best` was refused
with "`Level` has no field or method `equals`". A record or a tuple has
`equals` without declaring it; a declared type asks by writing the
signature with no body, `equals : (Level, Level) -> Bool`, which the
message could say, as the refusal of a binding with `else` says its fix.

### A lambda is never kept

Binding a lambda to share it, `bump = |counts, i| …`, is refused with
"a lambda stands only as a call's argument, as functions are passed and
not kept", which says exactly what and why. The cost is small: the
helpers deflate wanted inside one function, `bump`, `bases` and
`symbol_at`, are top-level functions instead.

### A row of tags cannot name another

`png.fn` answers its own failures and every one inflate can give, since
the image data is inflated with `?`. Its `PngError` alias has to list
inflate's six tags again by hand: a row cannot take in another alias,
and both `[NotPng, *InflateError]` and the same in a signature are
refused with

```text
error: expected one of `]`, a type name, found `*`
```

Leaving inflate's tags out is refused at the `?`, with a message that
says exactly which, "`A` and `B` are not among the tags of `[C]`, which
admits no others", so the list is found quickly, but it is a copy that
drifts when inflate gains a tag. A record already spreads, `{x: 1, *r}`;
a row spreading an alias, `[NotPng, *InflateError]`, would be the same
idea for tags. The alternative the tags note gives, wrapping inflate's
failures in one tag with `map_err`, changes what callers match on.

### A list built in a loop is built, even to be compared

Interlaced decoding first read each pixel through `List.range(width).fold`
a row, and asked whether a grey sample was tRNS's key with
`format.key == [grey]`. Both allocate in the loop: a list of every column
each row, and a one-element list each pixel, each freed at once. On a
1024 by 1024 interlaced RGB image that took 1.02 s, three quarters of it in
`seq.reserve`, `seq.release` and `nat.coalesce`. Counting columns by
recursion, and matching the key, `format.key is ([k] then k == grey, …)`,
took it to 0.12 s, with the scatter below.

Nothing in the source says which of these allocates: `[grey]` reads as a
value to compare, and `List.range(n).fold` as a loop. A list literal only
compared and dropped, and a range only folded, could each be left
unbuilt, as a cell whose fields are its only readers already is.

### Writing in place makes a scatter cheap

Adam7 stores an image as seven smaller ones. The decoder reads each pass
in turn and writes each pixel where it falls in the whole image, four
`put`s into a list of `width * height * 4` noughts. Nothing else holds
that list, so every `put` writes where it lies; the scatter costs about
what reading the pixels in order does. The first version, which read
each pixel of the whole image from whichever pass held it, needed a pass
table, a tuple of each pass's start and stride, and division a pixel.

### Choosing once a row beats choosing once a byte

Unfiltering first matched the filter type for every byte, and read the
left, upper and upper-left bytes for every byte whether the filter needed
them or not. Matching once a row, with a walk for each filter that reads
only what it uses, and converting 8-bit rows straight through rather than
pixel by pixel, took a 2048 by 2048 RGBA image from 0.77 s to 0.31 s; an
image of 8-bit red, green, blue and alpha is its own pixels once
unfiltered, and is answered as it is. A clause's head can match a
record's fields against literals, `straight_pixels(raw, _, _, {colour: 6,
depth: 8, *})`, which keeps each fast path to one line.

Paeth's predictor first worked in `Int`, as the specification writes it,
`p = a + b - c`. Each of its three distances is written without going
below nought, `|b - c|`, `|a - c|` and `|a + b - 2c|`, so it stays in
`Nat`.

### A string can name a chunk

A chunk's type is four ASCII bytes, read with `Str.from_ascii` and matched
against string literals, `"IHDR" then …`, as the specification names
them. Only a critical chunk's capital first letter needs the bytes
themselves, `U8.is_ascii_upper`.

### A slice to checksum is a copy

`Crc32.update` takes a `List(U8)`, so the CRC-32 of a chunk, its type and
data, is `input.drop(at + 4).take(length + 4)`: `drop` is free, but `take`
copies. Over a 9 MB file that is a few milliseconds; a walk that took a
start and a count, or a `List` slice that shares its buffer as `drop` does,
would need none.

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

Deflate, over 50 MB of the repository's own source and notes, as the
gzip example compressing standard input to a gzip file, in megabytes of
input a second, with zlib's through Python at the same level:

| Level | Faun      | zlib      | Faun's size | zlib's size |
| ----- | --------- | --------- | ----------- | ----------- |
| 1     | 44 MB/s   | 181 MB/s  | 16,019,810  | 16,285,456  |
| 6     | 13.7 MB/s | 52.1 MB/s | 13,087,687  | 13,101,272  |
| 9     | 3.6 MB/s  | 17.5 MB/s | 12,995,702  | 13,004,460  |

The search is zlib's, its levels' table and its lazy matching, though its
hash is not, so sizes agree to within a percent; Faun's are a little
smaller because each block's code is a true Huffman code cut to 15 bits
as miniz cuts it, and each block is written whichever of stored, fixed or
its own code is smallest. On the fixtures, raw DEFLATE:

| Input            | Level | Faun   | zlib   |
| ---------------- | ----- | ------ | ------ |
| text, 70 KB      | 1     | 26,408 | 26,475 |
| text, 70 KB      | 6     | 22,469 | 22,473 |
| text, 70 KB      | 9     | 22,368 | 22,377 |
| repetitive, 68 K | 6     | 96     | 97     |
| random, 70 KB    | 6     | 70,025 | 70,025 |

PNG decoding, over images Pillow and pypng wrote, through the PAM
example reading standard input and writing standard output, in megabytes
of RGBA a second; Pillow, on libpng's zlib, for scale:

| Image                    | Faun    | Pillow   |
| ------------------------ | ------- | -------- |
| 2048², 8-bit RGBA, noisy | 54 MB/s | 380 MB/s |
| 1024², 8-bit RGB, Adam7  | 34 MB/s | 300 MB/s |
| 1024², 16-bit RGB, Adam7 | 24 MB/s | 250 MB/s |

Of the 0.31 s the RGBA image takes, inflate is 0.25 s, where zlib takes
0.04 s; reading the chunks with their CRC-32s and writing the output take
0.03 s, and unfiltering 0.03 s. PNG decoding is as fast as inflate is.

## Related

- [Collections](values/collections.md): `List` and its lookups
- [Numbers](values/numbers.md): the wrapping words
- [Memory](machine/memory.md): buffers written in place
