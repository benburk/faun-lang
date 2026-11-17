# Compression

This note owns what writing checksums, DEFLATE and PNG in Faun taught: a
large, exactly specified workload of bit-level work on `U8` and `U32`, big
byte buffers and random access into a window, with outside programs as
oracles. The libraries are in-tree under
`crates/frontend/examples/libraries/`: `crc`, `flate` and `png`. Each
finding is a workaround the code carries, an error that misled, or
something the standard library lacked, with what it cost and where it
stands.

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

which names the right place but not the cause. Inflate wrote it eight
times before the first refusal, and twice more after. Every flag test in
`flate.fn` is parenthesized, `(flags & 4) == 0`. C has this precedence and
it is a known trap there; Rust binds `&` above `==`. Either the operator
note gives the bit operators their own level above comparison, or a test
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

Each dynamic block built a literal table of 2 to the longest code length
entries, up to 32768, by `List.repeat` and a fold over the lengths: 10%
of inflate's time on 50 MB of text, for blocks of some 16000 symbols.
Now a table reads at most 10 bits, and a code longer than that, marked in
the table, is read a bit at a time as puff reads every code, through how
many codes each length has and the symbols in code order. With the
match's length, distance and copy moved to `U64` as well, 16 MB of text
inflates in 121 ms rather than 185. A first level of 8, 9 or 11 bits did
no better than 10, and a second level, zlib's way, was not needed: codes
over 10 bits are rare enough that reading them a bit at a time does not
show in the profile.

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

### A slice to checksum is a view

`Crc32.update` takes a `List(U8)`, so the CRC-32 of a chunk, its type and
data, is `input.drop(at + 4).take(length + 4)`. Both are free: 100000
calls of `drop(i).take(n)` cost the same at a `n` of 10 as of 100000, so
`take` of a list shares its buffer as `drop` does, rather than walking
`take_into` as the source reads. That a view costs nothing until the
list it shares is grown is the next finding's other side.

### A view held while its list grows copies the list

Copying a match by slices rather than a byte at a time,
`out.concat(out.drop(from).take(length))`, made inflate quadratic: 300 KB
took 8.2 billion instructions where the byte loop takes 94 million. The
view shares `out`'s buffer, so `out` is no longer held by one, and
joining onto it copies all of it, every match. A probe growing a list by
its own last three bytes 20000 times shows it: 912 million instructions
through `concat(out.drop(k).take(3))`, 13 million through three `get`s
into a list literal. Binding the view first changes nothing; copying it,
`take(…).map(|byte| byte)`, puts it in a buffer of its own and the loop is
linear again, but `reverse().reverse()` does not, since those cancel.

Nothing in the source says which of `drop`, `take` and `map` copies, and
the cost of being wrong is not a constant but a power. The copy through
`map` read the window with fewer instructions than the byte loop, 4.48
billion against 5.14 for 16 MB, and took as long, an allocation a match,
so inflate kept the byte loop. A `List.extend_from(out, from, count)`,
appending a list's own elements where it lies, as Rust's
`extend_from_within` does, would serve every LZ77 decoder.

### Splitting a walk's clauses can lose its loop

Adler-32 read eight bytes a step with a clause reducing the sums when a
count ran out, written first:

```ruby ignore
adler_bytes(low, high, 0, bytes) -> adler_bytes(low % 65521, high % 65521, adler_run, bytes)
adler_bytes(low, high, left, [a, b, c, d, e, f, g, h, *rest]) if left >= 8 -> (
  s1 = low + U64.of_u8(a)
  …
```

Built natively, 16 MB said `stack overflow` and exited with status 3,
though every call is in tail position and `faun test` held. `faun emit
barb` shows why: Barb parted the clauses into `adler_bytes` and
`adler_bytes, going on`, each calling the other last, and the two calls
are calls, not a loop. In the cases tried it happened with a list pattern
of five elements or more and five bindings or more in its body; with four
of either the walk stayed one function. Writing the reduction last keeps
it whole, and `crc.fn` says why beside it. A tail call between the parts
of one walk could be a jump, as a call to itself is; until then nothing
warns, and a test on a small input passes.

### A word's arithmetic is a call in the profile

In inflate's profile, `U64.add`, `U64.cmp`, `U64.sub`, `U64.shift_right`,
`U64.to_nat` and `List.get` are functions of their own, each 1 to 3% of
the time, about a seventh in all, besides `codes`, the loop they are
called from. Each is a line in the standard library, `U64((a + b) %
18446744073709551616)`, which the backend reduces to an `add`, but does
not always inline into a large loop. `perf annotate` of `codes` also
shows its live values stored to the stack and read back, a comparison
made into a byte by `sete` and `movzbl` before it is tested, and small
constants loaded by `push` and `pop`, as the deflate search's does.

### An arm leaves with `return`, not `then return`

Refusing a bad argument from inside a match, `_ then return
host.exit!(2)`, is refused with "a body leaves only by a leaving line, `if
c return x` or `c else return x`, or by an arm, `P return x`", which
names the form wanted, `_ return host.exit!(2)`, and was fixed at once.

### Walking lists side by side beats reading them by index

The encoder's first filter pass read every byte and its neighbours by
index, `samples.get(at - stride).ok_or(0)` and the like, and scored the
five filters in five walks, each matching the filter for every byte. A
2048 by 2048 RGBA image took 1.8 s to filter, 9 MB/s, before deflate saw
a byte. Scoring all five in one walk, each byte and its neighbours read
once, took encoding at level 1 from 2.60 s to 1.57 s. Walking the row as
four lists side by side, `costs([x, *xs], [a, *as], [b, *bs], [c, *cs],
…)`, the row, itself from one pixel on, the row above and the row above
from one pixel on, took level 0 from 1.02 s to 0.59 s, and the profile's
`nat.from_word` and `nat.to_word`, 11% before, went away.

`drop` shares the buffer, so each cursor costs nothing to make, and a
pattern reads its head with no `Result` and no index to work out. What
the walk loses is the edges: before the first row and left of the first
pixel there are noughts, so the encoder keeps one row of noughts and
walks each row twice, its first pixel against noughts and the rest
against itself. The decoder's `unfilter_row` indexes into the output as
it grows, which is why it cannot do the same: the bytes to its left are
not written until it gets there.

### A smallest-by-key is a tuple's `min`

Choosing the filter with the smallest score is `min` over `(score,
filter)` pairs, taken apart with `map_ok` and `ok_or`: there is a
`sort_on` but no `min_on`, nor an `index_of_min`. Tuples compare in
order, so it is right, ties going to the lower filter as libpng's do; a
`min_on(|(score, _)| score)` would say so without depending on it.

### Reading a header out of bytes has no search

Finding where a PAM header ends, `ENDHDR\n`, has no `List` search for a
run of elements, nor a `Str` one that answers where. The example reads
the header a line at a time, `take_while(|byte| byte != '\n')` then
`Str.from_ascii` and `split(" ")`, and matches each line's words against
literals, `["WIDTH", n] then …`, which reads well; the Rust test does the
same search with `windows`.

### Record update and rows of tags join without asking

The example's flags update an `Encoding` as they are read,
`{filtering: Unfiltered, *encoding}`, and its result joins the PAM
reader's failure and the encoder's, `image_of(input).and_then(|image|
encode(image, encoding))`, `[NotPam]` and `[BadSize]` becoming one row
with nothing declared. A module can export a name it imported, so `png`
hands out flate's `Level` and a caller imports one library.

## Throughput

`crates/frontend/examples/libraries/flate/bench/run.py` measures every
library against Python's zlib, 1.3.2 here, on inputs made from the
committed fixtures, so they are the same at every commit: 16 MB of the
fixtures' 70 KB of text repeated, its repeats further apart than DEFLATE's
window reaches, 4 MB of noise, and a 1024 by 1024 RGBA PNG of gradients
with a little noise, its rows taking each filter in turn. Each Faun
program reads standard input and writes standard output; its time is the
quickest of three runs, pinned to one CPU, less the quickest time of a
program that only reads the same input. zlib's is on bytes in memory. In
megabytes a second of the larger side, input for checksums and deflate,
output for inflate and PNG, on x86-64:

| Work            | Before | Now  | zlib  | zlib over now |
| --------------- | ------ | ---- | ----- | ------------- |
| CRC-32          | 460    | 829  | 8954  | 10.8          |
| Adler-32        | 213    | 1590 | 5461  | 3.4           |
| inflate, raw    | 81     | 130  | 606   | 4.7           |
| inflate, zlib   | 60     | 122  | 560   | 4.6           |
| inflate, gzip   | 73     | 115  | 571   | 5.0           |
| inflate, stored | 1353   | 1689 | 23369 | 13.8          |
| deflate, 1      | 34     | 36   | 180   | 5.0           |
| deflate, 6      | 5.4    | 5.4  | 21    | 3.9           |
| deflate, 9      | 3.6    | 3.6  | 14    | 3.9           |
| PNG decode      | 35     | 44   | 372   | 8.4           |

"Before" is the libraries as each stage left them, "now" after the two
changes this section's findings give: inflate's tables and words, and the
checksums eight bytes a step. Inflate of a zlib stream gained the most,
since its Adler-32 was over a quarter of its time. The PNG's zlib column
is the inflate of its image data alone, a floor under any decoder; Pillow,
on libpng, decoded a 2048 by 2048 RGBA image at 380 MB/s. Deflate's speed
is its search's, which this section left alone: the repeated fixture text
holds many more matches than prose, so deflate is slower on it than on the
repository's own source, 13.7 MB/s at level 6, and zlib slower too.

zlib's CRC-32 reads its eight bytes a step as two words, where Faun's
reads them as eight `get`s, each checked against the list's length; its
Adler-32 sums 16 bytes a step in vector registers.

The search is zlib's, its levels' table and its lazy matching, though its
hash is not, so sizes agree to within a percent; Faun's are a little
smaller because each block's code is a true Huffman code cut to 15 bits
as miniz cuts it, and each block is written whichever of stored, fixed or
its own code is smallest. On the benchmark's text, gzip files:

| Level | Faun      | zlib      |
| ----- | --------- | --------- |
| 1     | 5,967,368 | 5,977,160 |
| 6     | 4,878,746 | 4,881,023 |
| 9     | 4,835,952 | 4,840,685 |

On the fixtures, raw DEFLATE:

| Input            | Level | Faun   | zlib   |
| ---------------- | ----- | ------ | ------ |
| text, 70 KB      | 1     | 26,408 | 26,475 |
| text, 70 KB      | 6     | 22,469 | 22,473 |
| text, 70 KB      | 9     | 22,368 | 22,377 |
| repetitive, 68 K | 6     | 96     | 97     |
| random, 70 KB    | 6     | 70,025 | 70,025 |

PNG decoding before this section's changes, over images Pillow and pypng
wrote, through the PAM example, in megabytes of RGBA a second, Pillow
for scale:

| Image                    | Faun    | Pillow   |
| ------------------------ | ------- | -------- |
| 2048², 8-bit RGBA, noisy | 54 MB/s | 380 MB/s |
| 1024², 8-bit RGB, Adam7  | 34 MB/s | 300 MB/s |
| 1024², 16-bit RGB, Adam7 | 24 MB/s | 250 MB/s |

Of the 0.31 s the RGBA image took, inflate was 0.25 s, where zlib takes
0.04 s; reading the chunks with their CRC-32s and writing the output took
0.03 s, and unfiltering 0.03 s. PNG decoding is as fast as inflate is.

PNG encoding, through the `topng` example reading a PAM file on standard
input and writing a PNG file, in megabytes of RGBA a second; Pillow
saving the same image, in RGBA for the first and RGB for the second, as
`topng` writes them:

| Image, level         | Faun     | Size       | Pillow  | Size      |
| -------------------- | -------- | ---------- | ------- | --------- |
| 2048², noisy RGBA, 6 | 3.1 MB/s | 6,021,518  | 17 MB/s | 6,052,244 |
| 2048², noisy RGBA, 1 | 16 MB/s  | 6,453,818  |         |           |
| 2048², noisy RGBA, 0 | 31 MB/s  | 16,783,684 |         |           |
| 2048², opaque RGB, 6 | 4.4 MB/s | 5,391,483  | 16 MB/s | 5,336,787 |
| 2048², opaque RGB, 1 | 18 MB/s  | 6,080,092  |         |           |

At level 6 deflate's search is 65% of the time, and the filtering, at
level 0, about 0.5 s; filtering is libpng's, so sizes are Pillow's within
a percent. Over every valid PngSuite image, the encoder writes 67,060
bytes where Pillow, saving each in the colour type `topng` chose, writes
67,112, and 65,196 with `optimize`; at level 9, 65,022. Choosing the
fewest channels that hold an image exactly, grey and dropping alpha, is
what keeps the suite's 162 images from 78,748 bytes, which Pillow writes
saving them all as RGBA.

## A ratchet workload, proposed

The [ratchet](../RATCHET.md) improves the compiler against fourteen
programs, each with a C twin. Compression would be a good fifteenth: a
loop of words and table lookups with no allocation but a growing output,
where this note's findings, a constant worked out at every use, a word's
arithmetic left as calls and the search's spills, are each what a
compiler change would move. It is not added, because `eval/` is
protected: changing the suite starts a new series and needs approval.

The proposal, for that decision:

- **`crc32`**, a kernel in `eval/workloads` reading its input as bytes,
  as `checksum` does: table-driven CRC-32 a byte at a time, the table
  built in the program, against a C twin of 20 lines. Sizes 4 MB, 1 MB and
  1 KB as `checksum`'s; it fits the 6502, its table 1 KB.
- **`inflate`**, taking a size as its argument: the program writes a
  deterministic text of that size, compresses it with fixed Huffman codes
  and a short hash-chain search written in it, inflates the result and
  prints the length and CRC-32 of what it read back. Both directions run
  on every target with no input file; the C twin is the same 300 lines,
  not zlib, so the twin measures how far the compiler is from C, not how
  far the algorithm is from zlib's. On the 6502 at a few hundred bytes the
  window and tables fit in 16 KB.

`crc32` alone would have caught the first finding, the table rebuilt a
byte, as a 500-fold regression.

## Related

- [Collections](values/collections.md): `List` and its lookups
- [Numbers](values/numbers.md): the wrapping words
- [Memory](machine/memory.md): buffers written in place
