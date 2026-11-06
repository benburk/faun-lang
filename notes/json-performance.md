# JSON performance

The JSON library parses 4.4 MB of user records in **205 ms** on x86-64, and
reads them into typed records and writes them back in **503 ms**. Rust's
serde_json does the same in 27 ms and 15 ms, Node in 66 ms and 67 ms, and
Python's `json` in 101 ms and 115 ms: Faun is 7.5× slower than serde_json at
parsing, 2× slower than Python, and 34× slower than serde_json at decoding.
It is exact where the others are not: integers keep every digit, and a
member named twice or not read is refused.

Measured 2026-11-06 on a Ryzen 9 9950X, CPU 5, seven-run medians, with
every change below. Peak memory is the largest resident size.

| 20,000 users, 4.4 MB | Parse  | Peak    | Decode | Peak    |
| -------------------- | ------ | ------- | ------ | ------- |
| Faun, x86-64         | 205 ms | 88 MiB  | 503 ms | 359 MiB |
| Faun, wasm32         | 234 ms | 110 MiB | 511 ms | 327 MiB |
| Rust, serde_json     | 27 ms  | 47 MiB  | 15 ms  | 21 MiB  |
| Node 24              | 66 ms  | 92 MiB  | 67 ms  | 113 MiB |
| Python 3.13          | 101 ms | 42 MiB  | 115 ms | 55 MiB  |

At 2,000 users, 0.4 MB, Faun parses in 13.6 ms, ahead of Python's 19.0 ms and
Node's 26.1 ms, which pay more to start; serde_json takes 2.4 ms.

## The benchmark

`crates/faun/examples/libraries/json/bench/` holds it:

- `generate.py` writes an array of user records, the same text for the same
  count: integers up to 10^12, floats with two decimals, strings with
  escapes and non-ASCII text, booleans, `null`, a nested object and two
  arrays each.
- `parse` reads a tree and walks all of it, answering how many values there
  are, the sum of the integers and the bytes of the strings.
- `decode` reads typed records, refusing unknown members, and writes them
  back, answering counts and the bytes written, which is the input's length
  when the round trip is exact.
- `reference/` has the same two in Python, JavaScript and Rust. The Rust
  `decode` uses serde's derive with `deny_unknown_fields`, and serde_json's
  `float_roundtrip`, without which it reads `6.5600000000000005` as `6.56`.
- `run.py --cpu N --count 20000` builds every program, checks that every
  answer agrees, and alternates pinned runs.

## What it found

Two programs the library ran on its own tests failed on real input:

- **Decoding an array overflowed the stack.** Each element's decode called
  the rest before answering, so 20,000 records went 20,000 frames deep.
  Looking a field up recursed through the members the same way. Both are
  loops now.
- **Writing any large tree took quadratic time.** `List.join` built its
  answer from the right, putting each piece before everything joined so
  far: that copies each piece once in a linked list, but Faun's lists are
  buffers, and a join puts the second sequence after the first in the
  first's room, or copies both. So each piece copied the whole answer. Built
  from the left, each piece goes into the room after what is already
  joined. Writing the decoded records back took 153 s and now takes 0.25 s;
  joining 400,000 strings takes 60 ms.

And three shortcuts in the library itself:

- A string with no escape is taken from the input as a view, where it was
  read a byte at a time onto a list, turned round, and checked: parsing went
  from 235 ms to 202 ms and its peak from 178 MiB to 88 MiB.
- A string needing no escape is written in quotes as it is, where each byte
  went through `flat_map`: decoding went from 721 ms to 559 ms, and its peak
  from 693 MiB to 359 MiB.
- A field finds its member and records its place, and `finish` marks the
  places in one pass, where names were compared again at every field, at
  every pairing of fields and at `finish`, about 200 comparisons an object.
  Decoding alone went from 0.18 s to 0.12 s. Indexing each object's members
  in a `Map` first was slower, 0.70 s for parsing and decoding against
  0.38 s, and twice the memory: a map costs more to build than nine names
  cost to compare.

## Where the rest goes

`faun build --symbols` names each function for `perf`. Parsing, by share of
samples:

| Function        | Share | What it is                           |
| --------------- | ----- | ------------------------------------ |
| `seq.release`   | 10.0% | giving up a buffer                   |
| `cell.release`  | 9.3%  | giving up a cell                     |
| `nat.retain`    | 8.0%  | taking a claim                       |
| `nat.allocate`  | 7.6%  | the private heap handing out a block |
| `nat.coalesce`  | 5.2%  | the heap joining free blocks         |
| `utf8`          | 5.0%  | checking a string's bytes            |
| `List.fold`     | 3.7%  | the benchmark's own walk             |
| `nat.mul`, etc. | ~8%   | integers read as arbitrary naturals  |

About half the time is the memory runtime: every value is a cell or a
buffer, every one is counted, and every one is given back. Decoding is the
same, with `seq.release`, `nat.coalesce` and `nat.allocate` the first three
at 32% together. serde_json's typed decode builds no tree at all.

Checking each string as UTF-8 is 5%. `Str.slice`, taking part of a `Str`
without checking it again, was tried and measured no faster, and the
[strings](values/strings.md) note keeps its reasons against slicing text by
byte, so it was not kept.

## What changed in the compiler

- **Joins.** Joining a short sequence before a long one nothing else holds
  copied the long one, so `[x].concat(built)` in a loop was quadratic:
  80,000 such joins took 21.6 s. On x86-64 and wasm32 each element layout a
  program joins now has a routine every join calls, which writes the first
  into room before the second where the second has room there or is
  strictly longer; those take 6 ms. The 6502's calls carry four values and
  one result, so it keeps the inline join, and its images are unchanged. A
  program that joins often is smaller for the routine, and a tiny one
  joining once is larger by it, so `faun build --small` builds both ways
  and keeps the smaller. Requiring the second to be strictly longer, not as
  long, keeps a stream's equal chunks growing at one end: growing at both
  took parsing's peak from 90 MiB to 127 MiB.
- **Symbols.** `faun build --symbols` writes a `.symtab` naming each
  function. Without it, an image is byte for byte as before, so the size
  ratchets hold.

## Next steps

1. The memory runtime is now the cost: fewer cells for small values, a
   cheaper path for freeing a block the heap will soon reuse, and taking no
   claim where a value is only read.
2. Integers are arbitrary naturals however small; one that fits a word could
   be read as one.
