# Ratchet findings

What the measurements have shown so far. `log.tsv` holds every evaluation and its verdict, and [standings.md](standings.md) every program beside its C twin. The reports the log names are in `ratchet/reports/` of the main checkout (gitignored); the counts are exact, so running the same two revisions again writes the same numbers.

## Where Faun stands against C

At `c3cded9`, as geometric means over the programs that have a twin on the target:

| Target, lab backend | Speed | Memory | Size | Small |
| ------------------- | ----- | ------ | ---- | ----- |
| x86-64 Linux        | 6.9   | 0.16   | 1.8  | 1.3   |
| wasm32 WASI         | 44    | 5.7    | 1.9  | 1.2   |
| 6502 sim65          | 20    | 7.4    | 13   | 13    |

- **x86-64** runs within about twice C's instructions on six programs (binary-trees, checksum, mandelbrot, spectral-norm, fasta, n-body) and holds a sixth of its memory, a static image against one that loads a C library.
- **Lab against stock:** on x86-64 lab runs 12% fewer instructions, holds 13% less and is 19% smaller. binary-trees halves in instructions and memory, and mandelbrot runs 37% fewer. On wasm32 and the 6502 lab is 7 to 9% smaller and otherwise within a few percent of stock.

## The largest gaps

- **Floats on wasm32 are in software.** The target says it computes no floats, so mandelbrot, n-body and spectral-norm burn 6,600 to 24,000 times the twin's fuel. Each module that reaches floats, k-nucleotide's among them, is over 300 KB where the rest are 6 to 65 KB. wasm32 has float instructions, so answering the float claims with them is the largest single gain the suite can see.
- **Plain loops over naturals and lists.** collatz runs 212 instructions a step on x86-64 where C runs 5: 44 times C there, 31 on wasm32 and 13 on the 6502. queens and sieve are 36 times C on x86-64, and pidigits 21 times GMP.
- **Lists rebuilt and `Map`:** fannkuch-redux is 57 times C on x86-64 and k-nucleotide 58, as the benchmarks game's README explains.
- **Memory on wasm32.** Every program touches at least 72 KiB of linear memory where a C twin touches 12 to 16, and checksum holds its whole megabyte of input where C reads a byte at a time.
- **The 6502's images.** The smallest program, checksum, is 21 KB where cc65's is 2.6 KB, and those that fit are 13 times their twins. Six programs fit in 64 KiB on neither backend, MD5 does not fit on lab, and binary-trees and sort do not fit on stock. On lab, binary-trees overflows its stack at its smallest depth, and sort does by 50 numbers.
- **A compiler error.** Stock for the 6502 refuses MD5 with `after natural legalization: main! instruction follows control flow that does not come back`, which is no size limit.

## What merging the lab backend changed

`c3cded9` against `711f676`, the commit before the merge, on the stock backend both have:

- **x86-64 mandelbrot regressed.** It runs 17.4% more instructions, 143.2 M from 122.0 M at size 400, and takes 10 to 20% more processor time, the edge of what the time guard reports. The gate before this one compared lab with lab and so did not see the default backend.
- **6502 checksum regressed.** It takes 2.7 times the cycles, 11.0 M from 4.1 M, and is 2.7% larger: the constant rotation the lab's README records.
- **Gains:** wasm32 MD5 burns 60% less fuel and mandelbrot 13% less, x86-64 k-nucleotide runs 5% fewer instructions, and the float programs' images are 3 to 6% smaller on wasm32 and the 6502.

Under these rules the merge is a rejection for the two regressions, each past 10% in its cell.

## About the measures

- **Resident memory from `wait4` is rounded** to a quarter of a megabyte on this 32-core machine: fasta reads 512 KiB where it holds 96. `eval/measure.c` counts the page tables instead, and ten passes of every Faun cell agreed to the kilobyte.
- **Elapsed time is not usable on a busy machine:** with every core loaded it reported programs 50 to 80% slower whose instructions had not changed. So did processor time, by its median alone and by its quickest run alone. Asking both of interleaved runs reported only mandelbrot, six timings of six.
