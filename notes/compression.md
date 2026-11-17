# Compression

This note owns what writing checksums, DEFLATE and PNG in Faun taught: a
large, exactly specified workload of bit-level work on `U8` and `U32`, big
byte buffers and random access into a window, with outside programs as
oracles. The libraries are in-tree under
`crates/frontend/examples/libraries/`: `crc`, and to come, `flate` and
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
`==` could print both values, as Rust's `assert_eq!` does.

## Throughput

On x86-64, release build, over 50 MB of random bytes read from standard
input, less the 26 ms reading them takes; zlib through Python for scale:

| Checksum | Faun     | zlib      | Notes                         |
| -------- | -------- | --------- | ----------------------------- |
| CRC-32   | 500 MB/s | 9000 MB/s | one table lookup a byte       |
| Adler-32 | 230 MB/s | 5500 MB/s | sums reduced every 5552 bytes |

zlib's CRC-32 reads several bytes a step through several tables, and its
Adler-32 sums 16 bytes a step; both are open to Faun as well.

## Related

- [Collections](values/collections.md): `List` and its lookups
- [Numbers](values/numbers.md): the wrapping words
- [Memory](machine/memory.md): buffers written in place
