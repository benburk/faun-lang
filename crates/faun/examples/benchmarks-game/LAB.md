# The x86 codegen experiment

**Prompt for a future iteration:**

> Improve Faun's x86 code generation by one verifiable step. Follow
> `crates/faun/examples/benchmarks-game/LAB.md`.

The long-term target is to beat the eight checked-in, single-threaded C
programs on executable bytes, elapsed time, peak resident memory and
compressed program source, **on each workload**. The next step only has
to beat the last accepted Faun revision. A lower average cannot pay for
making a different workload worse. This is a comparison with these C
programs and build flags; it makes no claim about the fastest possible C.

## Worktrees and boundaries

Keep the prep worktree at its reviewed commit: it owns the runner, C,
inputs, oracles, standard library, flags and scoring policy. Run evaluation
from there. Make changes only in the implementation worktree. The first
incumbent is stock Faun. After accepting a change, keep its commit and use
a clean checkout of **that commit** as the next incumbent. Keep the stock
report to see cumulative progress. Reports belong under `target/lab/`;
keep the two confirming reports with the accepted commit in the experiment
log. A scoring-policy change starts a new measurement series.

- The new crate starts at optimized, validated
  [Barb](../../../core/src/barb/README.md). It owns the lowering from
  Barb, its machine IR, layout, allocation and x86-64 Linux emission.
  Target-neutral passes may be added to Barb; its input language and
  observable semantics stay the same.
- The stock x86 backend remains the default. The planned CLI selector
  is `faun build --target=x86_64-linux --backend=x86-lab`; the selector
  does not exist at the prep commit. The host stays `x86_64-linux`.
  Reuse the frontend, host, standard library and suitable low-level code.
  The stock target trait's input is already lowered machine IR: swapping
  only its emitter would be too late to make placement decisions.
- A program should still be how one would teach the algorithm in Faun.
  A small, clearer source or algorithm change is eligible when general
  recognition is a poor fit. Preserve the task's intended work: e.g.,
  binary-trees still builds and walks trees, not a formula for the
  printed counts. No precomputed answers, input-size switches, workload
  recognition, code golf, deleted expectations, or outsourcing code to
  uncounted files. The runner builds each side's single `main.fn` in an
  empty package against the verifier's standard library. Review the diff;
  output equality cannot decide idiomaticity or algorithmic equivalence.
- Change one thing at a time. Label it **compiler** or **source**. If
  both need to change, run old and new compilers on old and new source:
  the `--*-bin` and `--*-tree` options select them independently. Record
  which change actually earned the gain.

## Run it

Use native x86-64 Linux, the locked Nix shell, and the same idle logical
CPU for the whole comparison. In each compiler checkout, build the exact
clean revision with `nix develop -c cargo build --locked --release -p faun-cli`.
The runner hashes the compiler it actually uses; it does not rebuild it.
Run these commands from the prep worktree:

```sh
# Stock only. Replace 30 with an allowed idle CPU on another machine.
nix develop -c just codegen-lab --cpu 30 --json target/lab/stock.json

# Later, after the experimental backend exists and builds:
new=../faun-lang-x86-lab
nix develop -c just codegen-lab --cpu 30 --candidate-tree "$new" \
  --candidate-backend x86-lab --only binary-trees --runs 1 \
  --json target/lab/try.json
nix develop -c just codegen-lab --cpu 30 --candidate-tree "$new" \
  --candidate-backend x86-lab --gate --seed 2 --json target/lab/check-1.json
```

Repeat the gate on an idle machine with a different seed and report path.
For a later incumbent, add `--baseline-tree PATH --baseline-backend x86-lab`.
A focused run is for diagnosis; only a full gate can pass. A failed
correctness check aborts before a score is written. A completed gate
writes its evidence even if it rejects the change. Existing reports are
never overwritten. `--game` measures the game's large inputs separately;
fannkuch can take minutes and k-nucleotide can need gigabytes.

## What a result means

Each side must exit successfully with empty stderr. Check Faun against
the game's small golden bytes, and both Faun sides against C at a seeded
extra size and the measured size. Every timed run's stdout is hashed and
checked. For k-nucleotide, all sides read the very same FASTA file. At
pidigits 27 the checked-in C program omits the trailing partial line:
use the golden file for Faun there and multiples of ten for C comparisons.

Rotate run order, warm each image first, and time the emitted program,
including startup and stdout to a file. Compilation and output hashing
are outside the clock. A small native parent measures elapsed time and
uses Linux `wait4` for the child's peak RSS, rather than charging it
Python's pre-exec footprint. Record the individual paired samples, CPU,
kernel, compiler hashes, input/output hashes, source hashes and image
hashes in JSON. Ratios to C below one favor Faun.

- **ELF bytes:** length of the runnable image, without profiling symbols;
  build C with the suite's flags plus `-s`. Faun ships a standalone ELF.
  C's on-disk count excludes shared libraries, including GMP for pidigits.
- **Program bytes:** the suite's normalized, gzip level 1 size of
  `main.fn` or `main.c`. This measures the spelling of the program; it
  changes only when source changes. Neither metric counts gzipped ELF.
- **Runtime and memory:** median elapsed ns and median of per-run peak
  RSS in KiB. An unchanged ELF earns no runtime or RSS win. For different
  images, a shift must exceed 5% and 1 ms or 128 KiB respectively, with
  at least four fifths of paired rounds agreeing on direction. A shift
  outside the band without that agreement is inconclusive. These are
  engineering tolerances, not confidence intervals.

The gate needs clean checkouts, all eight default workloads and at least
five rounds. One exact byte counts for either size metric. Accept only a
repeatable improvement in at least one metric with no regression or
inconclusive comparison anywhere. Before promotion, inspect both reports
for the **same winning benchmark and metric**, inspect the diff, run
`just check` and `just test`, and add a semantic test exercising the
change. The performance gate alone cannot prove a compiler correct.
The original `just benchmarks-game` still reports the game's lowest time.

## Implementation order (future work)

1. **Make parity boring.** Add the opt-in crate and CLI route at the Barb
   boundary in `faun::compile_barb_to_image_with`, before
   `faun_core::lower_to_machine_ir`. Use the stock x86 host to lower
   source; offer a dump and validator for the new machine IR. Establish
   stock/candidate equivalence on examples, effects, exits and the eight
   workloads. Report unsupported operations explicitly during bring-up;
   a silently delegated stock build is not evidence of backend coverage.
   Bootstrap milestones are not optimization wins.
2. **Prove placement before removing counts.** Start with one class of
   fixed-size, nonescaping aggregate. Show its lifetime across calls,
   branches, joins, loop backedges and recursion. Use registers or a
   frame slot while that proof holds; use an owned heap value otherwise.
   Test a returned value, a retained alias and an old snapshot after an
   update. Dump the reason for each placement so a change can be checked
   in IR as well as on the clock. The stock compiler already borrows
   arguments, moves last uses and reuses some unique buffers.
3. **Then try scoped storage.** For dynamic scratch whose lifetime nests,
   test a bump region restored on every exit; copied-out results cannot
   point back into it. Overlapping or unknown lifetimes keep the safe
   heap/RC path. [Goose](https://github.com/aardappel/goose) uses
   statically assigned data stacks with scope-based reclamation. Borrow
   the technique only where Faun can prove its preconditions; value
   semantics alone do not prove nonescape or a bound on live bytes.
4. **Try SIMD first as a lowering choice.** Express independent float
   lanes in the x86 machine IR, with scalar tails, and test against
   scalar Barb. Preserve each lane's operation order, rounding, NaNs and
   signed zero; do not silently reassociate a reduction or fuse a multiply
   and add. Consider portable public SIMD float types only after a real
   workload demonstrates a gap that internal vectorization cannot cover.
