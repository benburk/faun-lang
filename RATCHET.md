# Ratchet

The ratchet improves the compiler: the frontend, Barb, the backends and the standard library. Each candidate is a git revision. `just eval <candidate> [incumbent]` builds both revisions' compilers, has each compile the suite's programs and the probes for every target with every backend, holds what the programs print to their twins', and measures them. The incumbent defaults to `origin/main`. Once the compilers are built, a run takes about ten seconds, on a busy machine too, because what decides is counted rather than timed.

## What is measured

**The suite** is sixteen programs, each a `main.fn` beside a C twin `main.c`. Nine are in [`crates/frontend/examples/benchmarks-game`](crates/frontend/examples/benchmarks-game/README.md): the game's eight and MD5. Seven small kernels are in [`eval/workloads`](eval/workloads): checksum, collatz, crc32, inflate, queens, sieve and sort, written without floats so that cc65 can build their twins and the programs can fit the 6502. Inflate compresses and reads back a text of its own, and its image is too large for the 6502 today, so there it counts by where its image would end. Every program is plain Faun, written as one would teach the algorithm, and every twin is C as plain.

**The probes** are in [`probes`](probes), outside `eval/`, so adding one needs no approval. Each shows one behaviour of the compiler: `main.fn` is a short program written the natural way, and `twin.fn` the workaround a library once used in its place, also in Faun, printing the same. Each takes its size as its one argument and prints a checksum of what it built, and `sizes` gives the size on each target it runs on, a line each, such as `x86_64-linux 100000`; a probe leaves out a target it does not fit. The natural spelling is what is scored, as a suite program is; the twin, built by the incumbent's compiler with the stock backend, is its reference, as a C twin is, and says how far the compiler has to go. The probes measured are the trunk's, below.

**A cell** is one program on one target with one backend. The targets are x86-64 Linux, wasm32 WASI and the 6502 under sim65; the backends are stock and lab. A cell has five measures, and lower is better in each:

| Metric  | x86-64 Linux            | wasm32 WASI    | 6502 sim65    |
| ------- | ----------------------- | -------------- | ------------- |
| speed   | instructions            | fuel           | cycles        |
| memory  | resident memory         | memory touched | bytes written |
| size    | image bytes             | module bytes   | image bytes   |
| small   | the same, `--small`     | the same       | the same      |
| compile | compiler's instructions | the same       | the same      |

- **Speed** is the work a run took, in the target's own count: instructions run in user space, Wasmtime's fuel, the simulator's cycles. A count is the same from run to run whatever else the machine is doing, so one run of each image is enough and the cells run side by side.
- **Memory** is the most the program held: on x86-64 the pages resident, read from its page tables; on wasm32 the pages of linear memory it read or wrote, the memory's own size growing 64 KiB at a time; on the 6502 the different bytes it wrote. Each counts what the heap took from the machine, its free blocks with its used ones, so a block never freed shows. The heap takes memory in arenas, each at least as large as the heap so far, and searches on from its last allocation, writing through an arena before it reuses what was freed: whether a buffer fits the last arena turns on the size measured, and moves a program's memory by up to that arena with what it holds the same. So a memory past the guard below is measured again, both sides, at three quarters of the size, a quarter of the way round a doubling, and is past the guard only where it is past it there too.
- **Size** is the image built favouring speed, as `faun build` does, and **small** the image built `--small`. A change may spend size for speed where it leaves `--small` alone.
- **Compile** is the instructions the compiler ran, across its threads, to build both images. The report also keeps each build's time and the compiler's peak memory, which are not scored. The C twins' compilers are not measured.

Each target measures at its own input size, in `eval/ratchet.py`'s table or a probe's `sizes`, small enough that a run takes a fraction of a second. Floats are in software on wasm32 and the 6502, so their sizes there are tiny. A run may hold at most 256 MiB: on x86-64 its address space is limited to that, and on wasm32 its linear memory, so a program gone wrong fails its cell rather than the machine.

**The C twins** are built with `gcc -O3` for x86-64, clang `-O3` with wasi-libc for wasm32 and `cl65 -O` for the 6502, and measured the same way on the same simulator or runtime. A twin missing on a target leaves the cell measured without it: cc65 has no floats, and there is no GMP beyond x86-64. The twins are the same for both sides, so they do not move a verdict. They say how far there is to go, in [`ratchet/standings.md`](ratchet/standings.md).

**Not measured:** Apple Silicon macOS, whose host builds none of the suite and whose images run on nothing here; compressed source, since the programs are fixed; how long compiling takes.

## Promotion

**Incumbent.** The incumbent is `origin/main`: no tags are used, and the log records verdicts, not commits. A branch's candidate is scored with everything else on the branch against the trunk, so a second change is accepted only where the branch as a whole still is, and once it is merged the trunk is what the next branch must beat. `just eval <candidate> <incumbent>` names another revision, such as the branch's previous commit to see what one change does alone.

**Golden.** Every image, built for speed and built `--small`, must print exactly what the twin built for this machine prints at a size drawn afresh from each run's seed, and the measured image again at the measured size, leaving with status zero and nothing on standard error. A measure the incumbent has and the candidate lacks, because the program no longer builds, fits or agrees, rejects the candidate whatever else it gained.

**Score.** Each measure of each cell is the candidate's over the incumbent's. The score is the geometric mean of them all, weighed so that each target's metric counts the same however many programs run there: seventeen groups, a target's speed, memory, size and small, the probes' four, and compiling. The probes count as one more target does, every probe on every target and backend in each of their groups, so that many probes do not swamp the suite and a fix one of them shows is an ordinary gain. The compiler runs on this machine whatever the target, so compiling is one group across all three, the probes' builds with the suite's. The gain is the part of the score the better cells make, and the loss the part the worse ones make.

**A candidate is accepted when all of these hold:**

- nothing that ran for the incumbent is broken;
- the gain is at least twice the loss, and more than nothing;
- no cell is more than 10% worse, a memory counting only where it is also 16 KiB larger, or 128 bytes on the 6502, and so again at three quarters of its size, and a compile only where it is 25% worse;
- where the run was timed, no x86-64 program takes longer, as below, but for one that ran the same work by every count;
- it changes no protected path.

These hold for the probes' cells as for the suite's. A memory past the guard at its size and not at three quarters of it, and a program taking longer with the same work, still count in the score as measured, and the summary and the log's row name them under `noted`, rejecting nothing. So a small regression is paid for by a gain twice its size somewhere else, and a large one by nothing. A candidate that passes all of these but improves the score by less than a tenth of a percent is `neutral`: logged, not promoted, so the incumbent does not move for noise-sized wins. A rejected change I still want is my call: log it as `override`. Only a committed candidate, scored on the whole suite by the pinned evaluator, is promoted: the summary names anything else under `not a promotion`. So does a run whose two compilers are one file though built from different sources.

**Repairs.** A measure the candidate has and the incumbent lacks counts as a halving: a program that starts to fit the 6502, or to run at all. A 6502 program too large for the machine's 64 KiB on both sides still counts by where its image would end, so shrinking one towards fitting is a gain.

**Noise.** `just noise` measures the incumbent against itself and must say `quiet`. Sizes, fuel, cycles and all three memories are exact. x86-64 instructions, and the branches counted beside them, differ between runs by about a part in ten million, so counts within one part in a hundred thousand are the same. The compiler's instructions differ by up to about a percent, from how its hash tables are seeded, so compile counts within two percent are the same. An image whose bytes did not change earns no change in speed or memory. Measured across six passes with every core of the machine busy, nothing else differed.

**Time.** Instructions are not seconds: a change can run fewer and take longer. `just eval --time <cpu>` also times the x86-64 images, pinned to that CPU: after a run to warm each, the candidate, the incumbent and the twin take turns, one run each in turning order, for at least five turns and as many as take a quarter of a second. A run's time is the processor time it was given. A program takes longer where both the candidate's quickest run and its median run are more than 10%, and a quarter of a millisecond, over the incumbent's: on a busy CPU a lucky run fools the quickest and a burst the median, seldom both. Where the candidate ran within a tenth of a percent of the incumbent's instructions and of its branches, and held the same memory, the time is noted and does not reject: the two did the same work, and a tenth of a percent of it does not take a tenth longer, so the time is where the code lies, a loop's head moving across a 64-byte line when anything before it changes size. Aligning the code is the compiler's to do, and a change that does it shows here as a time no longer noted. Times only reject; they earn nothing. Time a candidate before promoting it wherever its x86-64 instruction counts moved, on an idle CPU where there is one.

Every run writes a new JSON report to `ratchet/reports/` in the main checkout (gitignored, never overwritten). It holds both commits, the hashes of their compilers and of the sources they were built from, the evaluator's commit, the machine, the tools, the seed, every cell's measures for both sides and the twin, the score and the verdict.

## Climbing

1. **Start.** Work on a branch `ratchet/<goal>` from `origin/main`, committing each candidate there. Push or merge only when I ask. Read `ratchet/log.tsv` and `ratchet/FINDINGS.md` first, and don't retry a rejected idea without a new reason.
2. **Change one thing** and commit it. Debug with quick runs: `just eval --only fasta`, `faun emit`, a profiler on a `--symbols` build. Only a full `just eval`, with no `--only`, decides. It says which incumbent it scores the checkout against, and prints the path of its report.
3. **Record every evaluation** as a row in `ratchet/log.tsv`. Every run prints its row; `just eval --log` appends it. The row's idea is the subject of the commit measured, which already says what the change is, marked `(with uncommitted changes)` where the checkout held more; `--idea "<text>"` gives another, as for a run that times the same change again. The columns are tab-separated, all but the first two from the run's summary:
   - `series`: the evaluator's series, `SERIES` in `eval/ratchet.py`, which each protected change to what is measured or how it is scored bumps;
   - `idea`: a one-line description, the commit's subject unless `--idea` gives one;
   - `score`: the overall score, below one being better;
   - `speed`, `memory`, `size`, `small` and `compile`: each metric's change across the targets;
   - `worst`: the worst cell's ratio;
   - `verdict`: the verdict and its reasons;
   - `report`: the report's file name.
4. **Rejected or neutral:** log it, revert the candidate and keep iterating.
5. **Accepted:** read the diff against the shortcuts below, run `just check` and `just test`, and add a test that exercises the change, since equal output on sixteen programs does not prove a compiler correct. Then log it as `accept` and commit the row. Rows name no commit, so a rebase leaves the log as it is. The standings are not written on a branch.
6. **Standings** are written on `origin/main` only, once a branch is merged: fetch, then `just standings` measures the trunk against itself and writes `ratchet/standings.md` from that report, to commit on the trunk.
7. **A fix nothing shows.** Natural code that runs slowly is a compiler bug, but a fix scores `neutral` where no program in the suite shows the behaviour. Test first: add a probe, the natural program beside its workaround, in a small pull request of its own, and once it is on the trunk score the fix against it. A branch cannot add a probe and score itself by it: `just eval` measures the trunk's probes, and warns where the candidate's differ.
8. After five rejections in a row, step back: profile, read what the slow cells run, and try a bigger or different change. Write what was learned in `ratchet/FINDINGS.md`.

## Protected paths

The evaluator runs from an export of `origin/main`, never from the working tree: what is merged there is what I approved. So a candidate cannot run its own judge, and the programs, twins, probes and sizes it measures are the trunk's as of the last fetch. It exports other revisions, such as the incumbent, into `~/.cache/faun-ratchet`, so it creates no git worktrees, and builds each one's compiler once, from nothing, in a target directory of its own, keeping only the compiler. A shared target directory would let cargo, which judges freshness by time, take one export's build for another's, since `git archive` dates every file to its commit. `eval/protected.txt` lists the evaluator, the suite, the tools' versions and these rules. `just eval` rejects a candidate whose branch changes them. Changing one needs my approval, is a pull request of its own, and, where it changes what is measured or how it is scored, starts a new series in the log once it is merged: it bumps `SERIES`. A change that leaves every measure and verdict as it was, such as how a row is written, keeps the series. The probes are not protected, since a branch's own are never the ones measured.

`just eval --unpinned` runs the working tree's evaluator instead, for working on the evaluator itself. Its verdict is a measurement, never a promotion.

## Shortcuts that don't count

- Recognizing the suite or a probe: a program by its name, path, text or hash, an input by its size or bytes, or a shape only one of these programs has. Barb recognizes by shape what a definition computes; a recognition counts when it is as general as that and a program outside the suite shows it.
- Precomputed answers: an output, a table or a folded result for the sizes measured.
- Detecting the measurer: fuel, the simulator, the counter, the tracer or the seed.
- Giving up semantics for a count: a check dropped, an overflow or a full heap or a deep stack no longer reported, memory no longer freed, output no longer written when the program says.
- Moving work where it is not counted, such as into the kernel on x86-64. The time guard is there to see it.
- Editing the suite, the twins, the sizes or the rules, or deleting or loosening tests. A probe's workaround or size changes in a pull request of its own, never with the fix it would score.

Equal output does not prove the work was done, so review each accepted diff before logging it as accepted.
