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

## What the code generation series showed

Series 2, from `4a66a65`, aimed at word-heavy hot loops like the
compression libraries'. Two candidates were accepted: natural comparisons
asked as one word comparison (`16405ac`, score 0.992), and machine IR
folding a known shift, conversion, comparison and branch (`7809e77`, score
0.963).

- **A change on x86-64 alone rarely clears the neutral line.** x86-64
  speed is one group of thirteen, so a change that only moves it has to
  take about 1.3% off every x86-64 program, on both backends, to move the
  score by a tenth of a percent. Threading an edge that carries a number
  past a block that only tests it, so `a & b` branches on its comparisons,
  took 10% off deflate's instructions at level 9 and changed no cell for
  the worse, and scored 0.99916: neutral, four times over, with and
  without moving a branch's comparison down beside it. The suite's loops
  have few conditions joined by `&` or `|`; the compression libraries are
  full of them. It is kept on the branch `ratchet/codegen-threading`.
- **The same for inlining.** Copying a definition that costs 24 or less
  wherever it is called, past the caller's allowance, inlines `U64.add`
  into inflate's `codes` and takes 10% off inflate's instructions, but the
  suite's programs are small enough that the allowance never runs out:
  neutral, 0.9993, with 6502 images up to 1% larger.
- **Size pays for a push and a pop.** Writing a small constant as one move
  rather than a push and a pop, favouring speed, ran 0.9% fewer
  instructions across the targets but made x86-64 images 1.5% larger, and
  0.9% larger written only in blocks on a cycle: rejected both ways, the
  loss more than half the gain.
- **What changes many targets at once is what moves the score.** Both
  accepted candidates are in machine IR, which every target reads: the
  comparison took 14 to 17% off sieve and 8 to 12% off queens on x86-64
  and wasm32, and the folding 17% off collatz on x86-64, 65% off checksum
  on the 6502 and 4 to 10% off every image.
- **The 6502 lab sort is at the edge of its memory.** Its image is 63 KB
  of 64, so its bytes written move by tens of bytes with nothing but the
  length of the name it is run under, which the evaluator holds fixed. A
  wider fold, following a number through any conversion to a word, made it
  write 1,508 bytes rather than 804 at 24 numbers, and 1,345 rather than
  815 at none, with the same output and every frame the same size; four
  string appends whose separator's length was known became unconditional,
  and nothing else changed. Following a number to a word only from an
  address, the handle a natural constant is, kept collatz's gain and left
  sort within the 6502's slack. The cause on the 6502 was not found.
- **A cached incumbent compiler can be stale.** The evaluator exports each
  revision into one tree per commit but builds all of them in one shared
  target directory, and `git archive` gives every file its commit's time,
  so cargo can take an older export's build as fresh: `16405ac`'s cached
  compiler was the trunk's, and a candidate on top of it was credited
  with `16405ac`'s own gain again (logged `invalid`). Deleting
  `~/.cache/faun-ratchet/bin/<commit>` and touching the export's files
  rebuilt it. The evaluator is protected, so this is for a pull request of
  its own.

## About the measures

- **Resident memory from `wait4` is rounded** to a quarter of a megabyte on this 32-core machine: fasta reads 512 KiB where it holds 96. `eval/measure.c` counts the page tables instead, and ten passes of every Faun cell agreed to the kilobyte.
- **Elapsed time is not usable on a busy machine:** with every core loaded it reported programs 50 to 80% slower whose instructions had not changed. So did processor time, by its median alone and by its quickest run alone. Asking both of interleaved runs reported only mandelbrot, six timings of six.

## Lists built only to be walked or compared

- **Fuel weighs a buffer lightly.** The Barb interpreter the fuel tests run on charged `List.range(48).fold` 12% more than the loop by hand, where x86-64 ran 3.4 times the instructions and 250 times the memory for `List.range(n).fold` at three million. A fuel test of something left unbuilt compares against the hand-written loop within a few percent, not against a ratio.
- **A 6502 image near 64 KiB leaves the heap no room.** Fusing queens' range but not the copy of its chain inside the fused step grew the stock image from 61.8 to 63.9 KB, and the program ran out of heap at its smallest size, status 2 after 274 thousand cycles. Fusing the chain inside the step too took it to 52 KB.
- **Constant evaluation is quadratic in a list built at its end.** A repeat built front to back appends a walk at a time when Barb tries to fold it, and trying `List.repeat(0, 1024)` cost inflate 31% more compiling before giving up. A walk pushing one value every round is the same list from either end, so repeat stays built from the end and fusion takes it as it is. Answering a recognized append in the evaluator directly made the attempts go further, not stop sooner: 9% more compiling with the old library.
- **The suite compares no literal list.** Following any field-less known value as a construction, `False` or `[]`, copied walks across the suite for nothing, 0.5 to 1% larger and a 6502 sort past its stack; md5's four-word digest through `flat_map` unrolled into four copies, 6% larger. Only a construction built in a body run more than once is followed now, within what inlining one callee may copy, and the suite's images are byte for byte the same.

## Small tags and pairs packed in a list's elements

- **The suite holds no list of small tags.** Packing a small sum's or pair's fields by their bits in the elements of a list built as the program runs, a block's symbols four bytes apart rather than six, changed no measure of the suite by a tenth of a percent: the win is on the flate probe, where `List([Literal(U8), Match(Nat, Nat)])` held 60 MB and now holds the 40 MB the packed-word workaround did, and ran 758 million instructions, now 743, against the workaround's 689.
- **Giving up and claiming a run of elements in one routine each** is where the series' gains came from: fannkuch-redux 27% fewer instructions on x86-64 and 22% less fuel on wasm32, inflate 14% fewer, and the 6502 lab binary-trees fitting the machine, since one walk called from every release and copy is smaller than one written into each.
- **Shrinking a 6502 image can raise its memory.** The 6502 lab sort image is 63,166 bytes on the trunk and 544 smaller with the routines above. On the trunk the heap's first request, the 1 KiB first arena, would reach the frames, so `grow` refuses it and the heap grows a block at a time exactly to what is held, 498 bytes. With the smaller image the 1 KiB arena fits, and the allocator, searching on from where the last allocation ended, writes through all of it before coming back: 1,022 bytes written at every size from 4 numbers to 32, with the same output, so 87% more memory by bytes written and the candidate rejected. Asking for a 512-byte first arena instead writes 1,243. Any change shrinking the sort image by some 400 bytes trips the same, until the 6502's heap asks for its first arena by what it needs or a search starts where blocks were freed.
