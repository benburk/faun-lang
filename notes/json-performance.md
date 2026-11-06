# JSON performance

The JSON library parses 4.4 MB of user records in **202 ms** on x86-64, and
reads them into typed records and writes them back in **559 ms**. Rust's
serde_json does the same in 27 ms and 14 ms, Node in 67 ms and 64 ms, and
Python's `json` in 99 ms and 110 ms: Faun is 7.6× slower than serde_json at
parsing, 2× slower than Python, and 40× slower than serde_json at decoding.
It is exact where the others are not: integers keep every digit, and a
member named twice or not read is refused.

Measured 2026-11-06 on a Ryzen 9 9950X, CPU 5, seven-run medians, against
revision `0340454` with the changes below. Peak memory is the largest
resident size.

| 20,000 users, 4.4 MB | Parse  | Peak    | Decode | Peak    |
| -------------------- | ------ | ------- | ------ | ------- |
| Faun, x86-64         | 202 ms | 88 MiB  | 559 ms | 359 MiB |
| Faun, wasm32         | 233 ms | 110 MiB | 561 ms | 348 MiB |
| Rust, serde_json     | 27 ms  | 47 MiB  | 14 ms  | 21 MiB  |
| Node 24              | 67 ms  | 92 MiB  | 64 ms  | 112 MiB |
| Python 3.13          | 99 ms  | 42 MiB  | 110 ms | 55 MiB  |

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

And two shortcuts in the library itself:

- A string with no escape is taken from the input as a view, where it was
  read a byte at a time onto a list, turned round, and checked: parsing went
  from 235 ms to 202 ms and its peak from 178 MiB to 88 MiB.
- A string needing no escape is written in quotes as it is, where each byte
  went through `flat_map`: decoding went from 721 ms to 559 ms, and its peak
  from 693 MiB to 359 MiB.

## Where the rest goes

The executables carry no symbols, so `perf` reports addresses alone, and
these are reasoned from the code rather than measured:

- **Every value is a cell.** A record of nine members is a list of nine
  pairs, each a cell holding a string buffer and a `Json` cell. serde_json's
  typed decode never builds a tree at all.
- **Member names are compared pairwise.** Looking a field up scans the
  members and then the rest for a second one; `Decode.sequence` checks each
  field's claims against those before it; `finish` checks every member
  against every claim. For nine members that is about 200 string
  comparisons an object.
- **A string is checked as UTF-8 again.** The input is a `Str`, so every
  stretch between quotes is valid already, but the library can only make a
  `Str` from bytes through `Str.from_utf8`.
- **The decoded records, their tree and the tree written back are alive at
  once,** which is most of the peak.

## Next steps

1. A `.symtab` in the x86-64 executable, so `perf` names functions.
2. Member lookup and claims by one pass over the object, refusing a repeated
   name where the object is bound, instead of where each field is read.
3. A way to take part of a `Str` as a `Str` without checking it again.
4. Joining a short sequence before a long one nothing else holds still
   copies the long one: `[x].concat(acc)` in a loop is quadratic, and
   `List.join` only avoids it. Growing the second sequence at its front
   fixes it, at a cost of code at every join, which pushed a 6502 program
   past 64 KiB. A routine called from every join would cost none, but the
   6502 takes at most four arguments and one result, and a join has six and
   two.
