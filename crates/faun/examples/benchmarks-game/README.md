# The benchmarks game in Faun

Eight programs from the
[benchmarks game](https://benchmarksgame-team.pages.debian.net/benchmarksgame/),
written as idiomatic Faun, each beside one of the game's own C programs:
an idiomatic one, single-threaded and plain, rather than the fastest. Each
writes the game's output, byte for byte.

The Faun programs are written as Faun is meant to be written, shortly and
plainly, not tuned for speed: where one is slow, the compiler is what is
to change. A run is counted down from where it starts, a sequence's runs
of bases are counted as the bases they are, and a line is written as it
is made, leaving buffering to the host.

| Program        | What it stresses                                     |
| -------------- | ---------------------------------------------------- |
| binary-trees   | making and freeing millions of small cells           |
| fannkuch-redux | short lists rebuilt in a tight walk                  |
| fasta          | a random generator, and writing output in batches    |
| k-nucleotide   | a `Map` under load, keyed by runs of bases           |
| mandelbrot     | `F64` arithmetic in a walk that leaves early         |
| n-body         | `F64` arithmetic on small records                    |
| pidigits       | `Int` arithmetic on numbers thousands of digits long |
| spectral-norm  | `F64` arithmetic over long lists                     |

Each folder holds `main.fn`, the game's C program as `main.c`, and the
game's output at a small size, which the tests hold the Faun program to.

## Running

```console
$ just benchmarks-game
$ just benchmarks-game --only fasta --runs 5 --cpu 3
$ just benchmarks-game --game
```

Each program is built, checked against the game's output, and run
`--runs` times beside its C program, whose output at the measured size it
must equal. Sizes default to ones the whole set takes a minute or so at;
`--game` asks for the game's own.

## Scoring

As the game scores programs:

- **Time:** the lowest elapsed time of the runs.
- **Memory:** the peak resident memory, read when the program is waited
  for.
- **Source:** comments removed, each run of white space made one space,
  and gzip at its lowest level: the compressed bytes.

## The C programs

| Program        | The game's program       | Why it                           |
| -------------- | ------------------------ | -------------------------------- |
| binary-trees   | gcc #1, Kevin Carson     | `malloc` and `free` per node     |
| fannkuch-redux | gcc #1, Joseph Piché     | a plain port of the Java one     |
| fasta          | gcc #8, Drake Diedrich   | "simple, idiomatic C", its words |
| k-nucleotide   | gcc #1, Jeremy Zerfas    | the game's only C program        |
| mandelbrot     | gcc #8, Greg Buchholz    | plain loops, no vectors          |
| n-body         | gcc #1, Christoph Bauer  | plain structs and loops          |
| pidigits       | gcc #1, Mr Ledrug        | GMP, as C has no big numbers     |
| spectral-norm  | gcc #8, Sebastien Loisel | plain loops                      |

Every one is built with `-O3 -fomit-frame-pointer`; the game's own flags
vary a little by program and name its machine. k-nucleotide is built
without OpenMP, so its `#pragma omp` lines do nothing and it runs on one
thread, with `khash.h` from [klib](https://github.com/attractivechaos/klib),
under the MIT license, beside it. pidigits writes no last line where the
count of digits is no multiple of ten, which the game never asks for, so
at the size checked only Faun's is held to the game's output. The game's
programs are under its [revised BSD license](LICENSE).

## Results

On an AMD Ryzen 9 9950X, pinned to one core, on 2026-11-12: the lowest of
five runs at the default sizes, and of one run at the game's.

| Program        | Size      | Faun s | C s  | ×    | Memory × | Source × |
| -------------- | --------- | ------ | ---- | ---- | -------- | -------- |
| binary-trees   | 18        | 0.69   | 0.48 | 1.4  | 0.9      | 0.8      |
| fannkuch-redux | 10        | 2.44   | 0.14 | 16.8 | 0.1      | 1.3      |
| fasta          | 2,500,000 | 1.27   | 0.64 | 2.0  | 0.2      | 1.2      |
| k-nucleotide   | 250,000   | 1.66   | 0.03 | 50.3 | 24.5     | 0.4      |
| mandelbrot     | 4,000     | 11.44  | 0.57 | 19.9 | 0.1      | 1.7      |
| n-body         | 5,000,000 | 0.26   | 0.17 | 1.5  | 0.1      | 1.4      |
| pidigits       | 4,000     | 0.65   | 0.05 | 12.4 | 0.3      | 1.4      |
| spectral-norm  | 2,000     | 0.19   | 0.34 | 0.6  | 0.1      | 1.5      |

At the game's sizes:

| Program       | Size       | Faun s | C s  | ×    | Memory, Faun / C |
| ------------- | ---------- | ------ | ---- | ---- | ---------------- |
| binary-trees  | 21         | 7.11   | 8.05 | 0.9  | 262 / 264 MB     |
| fasta         | 25,000,000 | 12.62  | 6.59 | 1.9  | 0.3 / 1.8 MB     |
| mandelbrot    | 16,000     | 192.76 | 9.40 | 20.5 | 0.8 / 2.1 MB     |
| n-body        | 50,000,000 | 2.59   | 1.69 | 1.5  | 0.3 / 2.1 MB     |
| pidigits      | 10,000     | 4.49   | 0.36 | 12.6 | 1.8 / 3.0 MB     |
| spectral-norm | 5,500      | 1.43   | 2.60 | 0.5  | 0.8 / 2.1 MB     |

fannkuch-redux at 12 takes Faun several minutes, and k-nucleotide at the
game's size gigabytes, so neither is measured there.

What they say, each slow one a thing for the compiler to learn:

- **Close to C:** binary-trees, n-body, fasta, and spectral-norm, where
  this C program is the slower. A Faun program's memory is its own: with
  no C library beneath it, one holding little peaks at a third of a
  megabyte.
- **Lists rebuilt where C writes in place:** fannkuch-redux flips a
  permutation by taking it apart and building it again, three lists a
  flip, where C swaps in an array. A list nothing else holds could be
  turned over where it lies.
- **`Map` against a tuned hash table:** k-nucleotide makes a string of
  each run of bases and counts it into Faun's `Map`, where C's khash
  counts a number the bases spell, in place.
- **`Int` against GMP:** pidigits' arithmetic is Faun's own, against
  hand-tuned assembly.
- **Comparing floats through naturals:** mandelbrot's escape test asks
  whether a float exceeds four, and `F64.cmp` compares two `U64` keys by
  calling `Nat.cmp`, which takes naturals: a key past 2^63, as every
  positive float's is, is boxed on the heap to be compared. Comparing
  words that fit a register as words would make the test one instruction.
