# x86-64 code generation performance

Three changes to what a build favouring speed writes. Together they take
grep by derivatives from 7.75 G instructions to 6.01 G, 444 ms to 282 ms,
and JSON parsing from 2.39 G to 2.19 G, 221 ms to 191 ms. `faun build
--small` and the size ratchets build exactly what they built before, and
the 6502 is unchanged.

Measured 2026-11-06 with `just bench` (`crates/faun/examples/bench/run.py
--cpu 30 --runs 5`), on a machine other work was also running on: the
instruction counts are the steady measure, and times move by a few percent
between runs. Each row is built by the compiler after that step; size is the
image's.

| Instructions | Base    | Tail calls | Shrink-wrapping | Counts in place |
| ------------ | ------- | ---------- | --------------- | --------------- |
| json-parse   | 2,389 M | 2,373 M    | 2,309 M         | 2,193 M         |
| json-decode  | 5,213 M | 5,167 M    | 4,963 M         | 4,834 M         |
| grep         | 7,748 M | 7,635 M    | 6,773 M         | 6,010 M         |
| sat          | 8,065 M | 7,995 M    | 7,759 M         | 7,702 M         |
| nbody        | 7,180 M | 7,170 M    | 7,170 M         | 7,175 M         |
| spectralnorm | 6,657 M | 6,657 M    | 6,656 M         | 6,975 M         |

| Time         | Base   | Tail calls | Shrink-wrapping | Counts in place |
| ------------ | ------ | ---------- | --------------- | --------------- |
| json-parse   | 221 ms | 217 ms     | 207 ms          | 191 ms          |
| json-decode  | 530 ms | 519 ms     | 508 ms          | 483 ms          |
| grep         | 444 ms | 399 ms     | 390 ms          | 282 ms          |
| sat          | 329 ms | 311 ms     | 303 ms          | 264 ms          |
| nbody        | 281 ms | 280 ms     | 280 ms          | 280 ms          |
| spectralnorm | 198 ms | 198 ms     | 198 ms          | 204 ms          |

| Image, KiB   | Base  | Tail calls | Shrink-wrapping | Counts in place |
| ------------ | ----- | ---------- | --------------- | --------------- |
| json-parse   | 171.2 | 170.4      | 177.4           | 273.3           |
| json-decode  | 277.6 | 276.7      | 284.2           | 444.0           |
| grep         | 37.4  | 37.0       | 39.0            | 59.5            |
| sat          | 34.2  | 34.1       | 34.6            | 47.4            |
| nbody        | 28.9  | 28.8       | 29.4            | 34.9            |
| spectralnorm | 42.4  | 42.2       | 43.1            | 58.0            |

## Tail calls and jump threading

A call whose answers are its function's answers, to a function taking
nothing on the stack, is a jump once the frame is closed, so the callee
returns straight to the caller's caller. Jump threading then copies a run
of at most two moves ending in a jump or a return over the one jump that
reaches it, where nothing falls into it. `cell.release`'s shared path ends
`jmp nat.release`. Every image is smaller or the same: the `nat` example
went from 257 bytes to 253.

## Shrink-wrapping

A function opens its frame, and saves the registers it keeps for its
caller, only on the ways through it that touch them: a block holding a
spilled value or one in a kept register, storing, reaching the stack around
a call, or with moves through memory on its way out. A block from which no
such block can be reached runs without the frame; the way into one that
needs it opens it, and the way out to one that does not closes it after its
moves. Opening is never inside a loop: a block with the frame open reaches
only blocks with it open, or ones that never need it.

The first version kept a function's frame where it starts wherever
wrapping wrote more saves and restores than that, so no image grew. It
moved no instruction count at all: the functions it wrapped were not the
ones that run. Wrapping every function that can be wrapped is what took
grep's instructions down 11%, and it writes a save or restore at each way
in and out, so it is done only favouring speed. Favouring size, every
function opens its frame where it starts, as before. A branch layout that
put the empty way first was tried with it, and ran more instructions, so it
was not kept.

## Counting claims in place

Taking a claim on a cell, a buffer or a natural's object was a call to
`nat.retain`, and giving one up a call to `cell.release`, `seq.release` or
`nat.release`, which for a shared object only stored the count less one.
Favouring speed on a 32- or 64-bit target, the count is moved where it is
asked: a load, one unsigned comparison of the count less its least against
the span that neither fails, nor is an immortal's, nor frees, and a store.
Any other count still goes to the call, which fails, leaves an immortal
alone, or frees what the last claim held. The same is done in the
runtime's own walks: claiming the elements a copy takes, and giving up what
a freed cell's fields or a freed buffer's elements hold.

This is in the machine IR's legalization rather than the x86 backend,
because the object's header, the immortal count and what freeing walks are
the runtime's, written once there; wasm32 gets it too. The 6502 keeps the
calls: its room runs out before its time does, as with `inline_small`.

It costs: speed images are 25–60% larger, a few bytes at every use. And
spectral norm runs 5% more instructions. Its hot loop holds no claim at
all; the counts written elsewhere in the same large function changed what
the allocator spills, and the loop now keeps its column and sum on the
stack. A retain-only and a release-only build were measured: the regression
comes with retains, and releasing alone saves less than half as much
elsewhere, so both are kept.

## Cells with no fields

A constructor with no fields, of a sum whose other constructors have them,
was a cell allocated each time one was made: the `Continue` a processor's
step answers in [assemulator-fn](https://github.com/benburk/assemulator-fn),
26 million of them made and freed in 26 million steps, a third of the time.
Each such constructor is now one immortal cell laid out in the image, so
making one allocates nothing. The emulator ran 26% fewer instructions,
16.97 billion down to 12.51, and 25% fewer cycles. Of the benchmarks,
grep ran 25% fewer and the JSON ones 1% fewer, and none ran more.

Keeping and dropping one still calls, since counting in place sends an
immortal's count to the call. Asking for it before the call saved the
emulator another 2.5%, but grep and SAT ran more instructions with the
comparison at every count, and every image grew 3–9%, so it was not kept.

## Size

The size ratchets in `crates/core/tests/support/backend.rs` measure the
image favouring size, and none of their programs is legalized, so they are
unchanged by the counts. `faun build --small` still prepares the program
both ways, favouring size and as speed would, and keeps the smaller; now
either way counts by calls and emits favouring size, so every `--small`
image on every target is what it was after the tail calls. The ladder and the primary-size rungs, which are built
favouring speed, are entry functions with nothing to wrap or count, and
hold.

Base and after the three steps, in bytes; the 6502 builds only the small
examples, and each is the same before and after, both ways.

| x86-64        | Speed           | `--small`       |
| ------------- | --------------- | --------------- |
| hello         | 226 → 226       | 226 → 226       |
| minimal-hello | 178 → 178       | 178 → 178       |
| newton        | 2,770 → 3,227   | 2,770 → 2,752   |
| regex         | 28,834 → 49,494 | 28,528 → 28,130 |
| sat           | 41,160 → 46,792 | 40,320 → 40,032 |
| bench/grep    | 38,312 → 60,960 | 38,312 → 37,880 |

| wasm32        | Speed           | `--small`       |
| ------------- | --------------- | --------------- |
| hello         | 254 → 254       | 254 → 254       |
| minimal-hello | 140 → 140       | 140 → 140       |
| newton        | 2,620 → 2,911   | 2,620 → 2,620   |
| regex         | 23,903 → 37,243 | 23,866 → 23,866 |
| sat           | 28,245 → 32,065 | 27,778 → 27,778 |
| bench/grep    | 31,685 → 46,926 | 31,685 → 31,685 |

| 6502          | Bytes |
| ------------- | ----- |
| hello         | 204   |
| minimal-hello | 51    |
| newton        | 9,428 |

The `--small` column falls with the tail calls alone; the other two steps
leave it as it was.

## Left

- Spectral norm's spills: an allocator that keeps a loop's values in
  registers ahead of code outside it would take back its 5%.
- A count could stay out of line where the use is cold, which would take
  back much of the size.
