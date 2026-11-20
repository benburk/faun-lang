# Experimental x86-64 Linux backend

This crate starts with the x86 emitter and machine IR from Faun commit
`711f676`. The CLI selects it with `--backend=x86-lab` for `build`,
`run`, `test` and `emit`. The default backend remains `stock`.

The frontend produces the same optimized Barb program for both backends.
Like every other target, it reads the machine IR `faun-core` lowers,
optimizes and legalizes, and implements `faun_core::targets::Target`.
`src/selected.rs`, `src/encode.rs` and `src/elf.rs` select instructions,
encode them and write the executable. The crate shares Barb, the machine tier,
the register allocator and general utilities with the stock compiler.

From the implementation worktree:

```sh
nix develop -c cargo build --locked --release -p faun
target/release/faun build --backend=x86-lab crates/frontend/examples/hello.fn -o target/hello-lab
target/release/faun emit --backend=x86-lab machine crates/frontend/examples/hello.fn
```

Measure future changes from the prep worktree with the
[experiment contract](../../frontend/examples/benchmarks-game/LAB.md).

## Shared recognition benchmark, 2026-11-14

Compared `b2d3af9` with `d5f6b2d`, using `x86-lab` on both sides and the
same source and standard library from the trusted prep worktree. These
results isolate the move to shared Barb recognition, not the cumulative
benefit of the experimental backend over stock.

### WebAssembly

Times are median milliseconds around `_start`, excluding compilation and
instantiation, with a fresh instance per run. Wasmtime 50.0.1 ran nine
alternating pairs on CPU 19. A second campaign confirmed MD5's 44% and
Mandelbrot's 18-19% speedups. Memory is peak guest linear memory in KiB;
binary size is uncompressed module bytes.

| Workload       | Time before/after | RAM B/A   | Bytes B/A         |
| -------------- | ----------------- | --------- | ----------------- |
| MD5 1 MiB      | 8.424 / 4.734     | 384 / 384 | 15,730 / 15,731   |
| Mandelbrot 16  | 75.061 / 61.487   | 192 / 192 | 309,079 / 309,233 |
| Float fixture  | 0.020 / 0.017     | 128 / 64  | 119,292 / 25,148  |
| Rotate16 256 B | 0.034 / 0.034     | 384 / 384 | 6,905 / 6,900     |

The float comparison row is a compiler regression fixture. Its tiny
runtime, and the checksum's runtime, include substantial harness overhead.
MD5 fuel fell from 832,934,403 to 336,141,203; Mandelbrot fuel fell from
2,228,028,345 to 1,940,815,829. Fuel is not a CPU cycle count.

The other seven benchmarks-game modules and hex encoding were byte
identical. Timing differences on them do not establish an improvement.
Host process RSS, measured separately with startup and JIT included,
was 24.6 / 25.2 MiB for MD5, 108.8 / 108.8 MiB for Mandelbrot, and
56.5 / 26.5 MiB for the float fixture.

### 6502

Cycle counts come from the pinned sim65 emulator with identical `run.bin`
argument names. RAM is peak dynamic guest bytes: reserved bump heap plus
active software frames, C stack and hardware stack. It excludes the
program image, zero page and fixed address-space gaps. Instrumented memory
measurements matched the stock emulator's output and cycle counts.

| Workload       | Cycles before/after   | RAM B/A     | Bytes B/A         |
| -------------- | --------------------- | ----------- | ----------------- |
| FASTA 100      | 130475736 / 130475736 | 3264 / 3264 | 56391 / 56391     |
| Hex 64 B       | 688734 / 688734       | 7256 / 7256 | 26670 / 26670     |
| Rotate16 256 B | 1139534 / 16307844    | 7276 / 7282 | 24589 / 25173     |
| Float fixture  | n/a / 11361           | n/a / 1084  | too large / 55768 |

**Known regression:** the rotating checksum takes 14.3 times as many
cycles. Its lowered IR replaces direct constant shifts with a counted
shift loop that allocates loop state. Additional input lengths from zero
through 512 bytes confirmed correct output and the slowdown. Constant
rotation expansion on narrow targets needs further work; this merge is
not a universal performance win.

The float fixture previously exceeded 64 KiB and now fits. Six game
programs and MD5 still exceed the address space on both revisions;
binary-trees at depth six overflows its stack on both. Failed programs
have no performance ratio.

### Validation and evidence

All successful benchmark outputs were checked against C, hashlib, or an
independent checksum oracle. Other workloads running on the host make
wall time noisy; module hashes, guest memory, fuel and cycles provide
additional evidence. Portable inputs are smaller than the native suite.

At `d5f6b2d`, `just check` and `just test` passed (1,340 tests passed, one
skipped, plus doc tests and grammar checks). MD5 matched hashlib for 135
inputs including the 55/56-byte and streaming boundaries. Both full x86
gates, seeds 79 and 80, passed correctness and emitted identical images
for all eight workloads. Their verdict was **no change**, not a passing
performance-improvement gate; MD5's x86 image was also unchanged.

Raw reports remain under the trusted prep worktree's `target/lab/`, as
required by LAB.md: `portable-barb-d5f6b2d/report.json` and its reproduction
bundle, plus `barb-recognition-d5f6b2d-seed79.json` and
`barb-recognition-d5f6b2d-seed80.json`.
