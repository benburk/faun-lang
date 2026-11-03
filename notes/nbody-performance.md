# N-body performance investigation

The unchanged list-based benchmark now takes **0.057 s** at 1,000,000 steps
on x86-64, **17× faster** than the original build's 0.994 s and past the 10×
goal. Scalar C takes 0.038 s, so it remains **1.5× faster**; auto-vectorized
C takes 0.041 s. Measured 2026-11-03 with `compare.py` on CPU 10, seven-run
medians, while other builds were running on the machine. The sections below
record how it got here; the register-bank measurements, when C was still
5.7× faster, are under [Comparison with C](#comparison-with-c).

The measurements below predate `kick` pairing bodies through `map_accum`
rather than a hand-written `pull` counted down by `fuel`. `map_accum` once
built its answer backwards and turned it round, which allocated and copied a
second buffer: 1.39 s against 1.02 s for the hand-written walk, at 5,000,000
steps pinned to CPU 10. `map` and `map_accum` are now written directly, and
the compiler builds such a walk front to back in a loop, appending where
nothing else holds the buffer; a reversal onto nothing of a buffer nothing
else holds turns it round where it lies. The same 5,000,000 steps now take
**0.85 s** at best of five, as fast as a walk never turning its answer round
(0.82 s), on a machine then loaded by other work. The energies are
unchanged.

## Writing lists in place and fusing `kick` (2026-10-02)

Three Barb changes, measured together on CPU 10 at 1,000,000 steps (best of
three) and with counters over 5,000,000, per step:

| Revision                 | Elapsed | Instr./step | Cycles | Branches |
| ------------------------ | ------: | ----------: | -----: | -------: |
| Before (`bf2e09b`)       |  0.16 s |       4,635 |    866 |      495 |
| In place (`bcb809f`)     |  0.14 s |       4,100 |    748 |      555 |
| `kick` fused (`a6c989f`) |  0.11 s |       3,326 |    606 |      401 |
| Composed (`94cc271`)     |  0.07 s |       2,192 |    401 |      229 |
| Lengths kept (`9e47e44`) |  0.07 s |       2,067 |    413 |      134 |
| `U32` step count         |  0.07 s |       1,995 |    414 |      122 |
| Static uniqueness        |  0.05 s |       1,517 |    309 |       74 |
| Scalar C, as below       |  0.03 s |         544 |    194 |       13 |

`map` and `map_accum` replace each body where it lies instead of building
a new buffer; their index check and the runtime's uniqueness test add
branches, which fusing `kick` with the `map` that moves every body then
more than takes back. The sequence identities (`aa1801e`) drop the
`prepend(built, [])` each walk ended with. Energies match at every count
checked. Composing in-place walks then writes `kick`'s answer into the
buffer it walks too, through the `map_accum` it goes on with, so a step
builds no buffer at all; the rest of the gap is the calls between walks,
the index and uniqueness checks each replacement makes, and reference-count
traffic. Keeping a list's length through recognized sequence operations
then holds nbody's at five outright, so a replacement asks nothing of its
index; and holding the step count in 32 bits, as C holds it in a fixed
word, makes the step loop count in a word rather than an arbitrary-precision
natural, with no `nat.drop` a step. Neither moves the time: those branches
and calls were all predicted. What a step still asks is whether each buffer
it writes is its own, fifteen times, and the unconditional jumps the x86
backend lays structured control flow out with: 62 conditional branches and
59 unconditional against C's 10 and 3. Knowing statically that the buffer a
loop rewrites is nothing else's -- it is a replacement's answer, moved round,
once made so on entry -- removes the fifteen: a step then asks once, on
entering `kick`, and writes every element without asking, at 309 cycles.

## Comparison with C

[`reference.c`](../crates/faun/examples/nbody/reference.c) uses a five-element
array and ordinary nested loops. It preserves Faun's pair order, expression
grouping, momentum offset and right-associated energy sum. It has no hand-written
SIMD, approximate reciprocal square root, FMA or reassociation. It updates the
array in place, whereas Faun still rebuilds immutable lists: the gap measures
both representation and code generation, not float instruction selection alone.

GCC 15.2.0, `-O3 -march=x86-64 -mtune=generic -ffp-contract=off
-fno-math-errno`, with `-fno-tree-vectorize` for the scalar control. GCC partially
unrolls the constant-bounded loops even in that scalar build. The second C build
allows automatic SSE2 vectorization. Neither build enables AVX or fast math.

Seven alternating, warmed runs at 1,000,000 steps on the same Ryzen 9 9950X,
pinned to **CPU 10**; compilation excluded, process startup and output included:

| Program / compiler stage  | Median elapsed | Original speedup |
| ------------------------- | -------------: | ---------------: |
| Original Faun (`8566abb`) |        0.994 s |            1.00× |
| Local XMM + trim          |        0.242 s |            4.10× |
| Allocated XMM bank        |    **0.213 s** |        **4.66×** |
| Scalar C                  |       0.0372 s |            26.8× |
| C (auto-vectorized)       |       0.0359 s |            27.7× |

Original runs ranged from 0.993–0.999 s; the local-cache version from
0.242–0.244 s; allocated floats from 0.211–0.215 s; scalar C from
0.0369–0.0375 s. A heavily contended CPU-10 trial was discarded; these rows
were remeasured together after that load subsided, rather than combined with
older timings. These are local measurements, not comparisons with the
Benchmarks Game's differently configured machine.

Separate pinned counters over 5,000,000 steps, including startup:

| Program            | Instructions/step | Cycles/step | Branches/step |
| ------------------ | ----------------: | ----------: | ------------: |
| Local XMM + trim   |             6,159 |       1,253 |           633 |
| Allocated XMM bank |             5,816 |       1,100 |           633 |
| Scalar C           |               544 |         205 |            13 |

Register-bank allocation removes about **343 instructions per step** and
12% of elapsed time. The branch count barely changes: recursive list walks,
reference counting and buffer rebuilding remain. The shared bank machinery
can also serve an AArch64 target; this change does not add that backend.

Printed energies match exactly, after removing Faun's `Ok(...)` wrapper, at
0, 1, 10, 1,000, 10,000, 100,000, 1,000,000, 5,000,000 and **50,000,000** steps.
The last count is the [game's performance workload](https://benchmarksgame-team.pages.debian.net/benchmarksgame/description/nbody.html).
Its two energies are `-0.169075164` and `-0.169059907`. A single long-run check
took 11.97 s for the local-cache version, 10.48 s with allocated XMM registers
and 1.84 s for scalar C; those are not repeated-run medians. An earlier check
of the original executable took 48.26 s. The 1,000-step
output also matches the game's published reference. Printed agreement is not a
claim that every intermediate C bit pattern was compared.

The [leading C #9 submission](https://benchmarksgame-team.pages.debian.net/benchmarksgame/program/nbody-gcc-9.html)
uses explicit AVX vectors and a single-precision reciprocal-square-root estimate
with refinement. That is a different numerical implementation from scalar
`sqrtsd` and division. Its ranking is not a reason to silently replace Faun's
correctly rounded operations with approximations.

### Assembly evidence

Before either XMM improvement, `pull` computed `dt / (d2 * sqrt(d2))` through GPRs:

```asm
movq   xmm0, r15       ; d2
sqrtsd xmm0, xmm0
movq   rbp, xmm0
movq   xmm0, r15
movq   xmm1, rbp
mulsd  xmm0, xmm1
movq   r15, xmm0
movq   xmm0, r14       ; dt
movq   xmm1, r15
divsd  xmm0, xmm1
movq   r15, xmm0
```

The local-cache version kept `d2` in `xmm0` and fed the next calculation directly:

```asm
sqrtsd xmm1, xmm0
mulsd  xmm0, xmm1
movq   xmm2, r14       ; dt still arrives in a GPR
divsd  xmm2, xmm0
```

With shared bank allocation, `dt` also stays in XMM through this chain:

```asm
sqrtsd xmm11, xmm9
mulsd  xmm9, xmm11
movaps xmm11, xmm1     ; preserve dt for later use
divsd  xmm1, xmm9
```

GCC's scalar C keeps `dt` in `xmm6` across the loop. One of its unrolled pairs
uses the following sequence; register copies remain, but no integer transfers:

```asm
movapd xmm1, xmm0      ; d2
sqrtsd xmm1, xmm1
mulsd  xmm1, xmm0
movapd xmm0, xmm6      ; dt
divsd  xmm0, xmm1
```

C also loads and stores doubles directly between memory and XMM, uses memory
operands such as `subsd xmm5, [rax+56]`, and walks fixed-size bodies by adding
56 to a pointer. Faun now has direct XMM loads/stores too, but still passes
body fields across recursive calls and spills them to its stack frame. The remaining gap is
much larger than the choice between `sqrt` and a hardware instruction.

### What register-bank allocation guarantees

`OperandSpec.allowed` in the shared allocator describes legal registers at
uses and definitions, independently of fixed or tied constraints. Preferred
bank sets propagate through single-use tied copies, keeping word loads and
representation-only conversions in the float bank when their consumers need
it. Exact return-register preferences do not restrict a value's bank home to
one register across calls.

x86 uses all 16 XMM registers. It supplies bit-preserving GPR/XMM transfers,
direct 32/64-bit XMM memory accesses, word spills and mixed-bank parallel
copies. Internal calls clobber XMMs; stack arguments and results can transfer
directly to either bank. The first six arguments and first result retain the
integer-register ABI. Binary32 results stay zero-extended in their low 64-bit
word, including sqrt with a dirty independent destination. The allocated
instruction verifier rejects wrong-bank operands before encoding.

The old `machine::floats` cache and writeback pass are removed. Native tests
cover arithmetic and rounding, signed zeros, NaNs, all physical register
encodings, narrow copies, mixed-bank/memory cycles, direct memory accesses,
spills, loops and calls. Copies preserve NaN payload bits; arithmetic retains
the existing IEEE contract, which does not specify a particular NaN payload.
The other backends retain their shared conformance tests.

The preceding local-cache round improved 0.340 s to 0.240 s on CPU 10
(**1.42×**), reducing 6,639 instructions per step to 6,159. Those timings are
historical; the table above remeasures its final executable alongside this one.

## Earlier measurements

Measured on a Ryzen 9 9950X, Linux, against revision `8566abb`. All executables
were built with the release compiler. Times include startup and output, exclude
compilation, and use 1,000,000 steps. Seven alternating runs, after one warm-up
per binary, were pinned to CPU 0. Each row includes the changes above it.

| Compiler changes          | Median elapsed | Speedup over original |
| ------------------------- | -------------: | --------------------: |
| Original                  |        0.944 s |                 1.00× |
| Cell forwarding           |        0.766 s |                 1.23× |
| Stack arguments/results   |        0.536 s |                 1.76× |
| 16-leaf aggregates        |        0.372 s |                 2.54× |
| Common scalar expressions |        0.332 s |                 2.85× |
| Two-operand multiply      |        0.329 s |                 2.87× |

Original runs ranged from 0.939–0.958 s; final runs from 0.322–0.334 s. The last
change's timing difference is small enough to overlap run-to-run variation.
It removes unnecessary register constraints and reduces instructions, rather
than establishing another substantial speedup by itself.

Separate `perf stat` runs measured approximately 19,602 instructions and 5,221
cycles per step originally, versus **6,692 instructions and 1,819 cycles** in the
pre-XMM executable. Counters include startup. The initial investigation measured
the first fix alone at 0.936 s → 0.755 s, or 1.24×; the table above remeasures
all stages together.

Outputs agree byte-for-byte at 0, 1, 10, 1,000, 10,000, 100,000 and 1,000,000
steps. At a million steps the output is:

```text
Ok(-0.169075164
-0.169086185)
```

Existing expectations check reference energies at 0, 1 and 10 steps. The longer
comparisons check preservation of the baseline. A 10× improvement would take
about **94 ms** on that CPU-0 run; that version needed another roughly 3.5×
improvement. The latest CPU-10 comparison puts the threshold at 99 ms, versus
213 ms now: another roughly 2.15× is still needed.
The integration algorithm, order of pair updates and floating-point rounding
have not changed.

## Float lowering

`crates/faun/standard/README.md` documents the claims for `F64.add`, `sub`, `mul`,
`div` and `sqrt`. Machine IR contains `binary64` operations for all five.
`RawEncoder::float` in `crates/x86-64-linux/src/encode.rs` emits `addsd`, `subsd`,
`mulsd`, `divsd` and `sqrtsd`; executable disassembly confirms those instructions
in the pair update.

Float values now occupy XMM registers rather than consuming the GPR file
throughout their lifetimes. Transfers remain at integer observations and
register-passed call boundaries; spills and stack-passed values can stay in
the float bank. SSE2 is guaranteed on x86-64; AVX/FMA need an explicit
target-feature policy. Contracting `a*b+c` into FMA changes rounding, so it
cannot silently replace the existing operations.

Some long decimal literals still call software `F64.of_decimal` at startup.
They do not explain the integration loop's cost. Avoid timing compilation or
only a handful of steps when evaluating this benchmark.

## Allocation and representation

A baseline `perf record` run over 3,000,000 steps sampled approximately:

- 40% in `pull`, including arithmetic, projections, packing and spills;
- 36% in allocation, coalescing and block claiming;
- 6% in `kicked`;
- 8% in cell and sequence release.

The allocator helpers are named `nat.allocate`, `nat.coalesce` and `nat.claim`,
but serve cells and sequence buffers too. Their names do not imply software
float arithmetic. These are flat sample shares, not additive speedup estimates.

The original machine IR showed three avoidable costs:

1. `pair` built a fourteen-field cell and immediately projected all its fields.
   A seven-leaf `Body` fitted flat, but `(Body, Body)` exceeded the original
   eight-leaf threshold, even after inlining.
2. `pull` took eleven values and returned a ten-field cell. x86-64's original
   six-argument, one-result budget heap-packed excess arguments. `kicked` also
   needed a pack to return its three-value sequence.
3. Buffer projections repeated the same element-address arithmetic for each
   field of a body.

### Implemented changes

**Cell forwarding.** `ir::simplify` forwards a directly constructed cell's
fields when shapes and classes agree, and folds its known tag. Pruning removes
an unused construction before ownership placement and legalization. Calls
computing unread fields still execute in order, and escaping cells remain
allocated. This first fix removed ten temporary pair cells per step under the
original representation policy; it remains useful for explicitly boxed values.

**Stack calling convention.** x86-64 still passes the first six values in the
System V integer argument registers and returns the first in `rax`. Overflow
arguments and results use a caller-owned stack area rather than managed cells.
Each function reserves the largest area any of its calls needs, separately from
spills and saved registers. Recursion gets a separate area in each activation.
External providers keep their interfaces. Selection verifies both sides of each
call's stack layout; lowering checks combined frame displacements.

**Flat aggregate budget.** Raising the leaf budget from 8 to 16 keeps the
benchmark's pair and body/list results unboxed. Wider aggregates remain shared
cells. This is a copying/register-pressure policy, not a language limit.
Wasm already carries multiple values; sim65 still packs excess values through
`ir::fit`. Increasing this budget without first changing the x86 ABI would just
move much of the boxing into `fit`. The tradeoff is more SSA leaves and native
stack space in exchange for fewer heap objects.

**Common scalar expressions.** A region-local pass shares repeated pure
calculations, particularly element-address arithmetic after legalization. It
never merges loads, calls or allocations, nor reorders float operands. Keys
include result classes. Constants identify equal expressions but stay separate
instructions, preserving target immediate selection. Tables are bounded at
1024 entries each; two compact value-indexed tables record regions and canonical
operand identities. This adds an arena rebuild to the optimization schedule.
The small-program size tests remain intact; the WASI and sim65 greeting images
shrank by four bytes each.

**Integer multiplication.** The backend now uses two-operand `imul` for a low
word product instead of forcing operands into RAX/RCX and clobbering RDX.
Signed and unsigned multiplication have identical low bits. This also reduces
the runtime multiplication size fixture from 188 to 165 bytes. The shared-
intermediate size fixture grows by one byte because `imul` has a longer opcode
where the old operands already occupied its fixed registers.

After stack passing, flat aggregates and common expressions, a 5,000,000-step
profile put about **66% in `pull`**, 10% in `kicked`, and **7% in allocation,
coalescing and claiming**. That profile preceded the small `imul` refinement.
The dominant cost has moved from allocation toward the pair-update code.

## Next experiments toward 10×

1. **Reduce remaining transfers and spills.** Bank allocation is in place.
   Some tied inputs still make redundant round trips when their original GPR
   copy survives, and the register-passed ABI still uses GPRs. Inspect those
   cases without weakening bit-pattern or rounding guarantees.
2. **Remove sequence rebuilding from the integration loop.** Investigate
   broader uniqueness-aware reuse or fixed-length sequence specialization.
   Buffer prepends already reuse uniquely held spare capacity; the remaining
   question is how to avoid repeated walks and intermediate sequences. Every step
   still rebuilds lists in `kick`'s `map_accum`, then maps the position update.
   Preserve pair order and keep the general list benchmark as a control.
3. **Use address-generation instructions.** Common expressions now remove
   duplicate calculations; selection can still use better addressing modes
   for the calculations that remain. Do not CSE loads across stores or calls.

Exploratory fixed-five source rewrites and a fourfold increase in the inlining
budget fell short; neither is retained. Hand-unrolling this benchmark is not
evidence of a general compiler improvement. Measure subsequent changes
independently rather than multiplying speculative speedup estimates.

## Reproduce

Build the C controls and inspect the scalar compiler's assembly:

```sh
gcc -std=c11 -O3 -march=x86-64 -mtune=generic -ffp-contract=off \
  -fno-math-errno -fno-tree-vectorize -Wall -Wextra -Werror \
  crates/faun/examples/nbody/reference.c -lm -o /tmp/nbody-c-scalar
gcc -std=c11 -O3 -march=x86-64 -mtune=generic -ffp-contract=off \
  -fno-math-errno -Wall -Wextra -Werror \
  crates/faun/examples/nbody/reference.c -lm -o /tmp/nbody-c-auto
gcc -std=c11 -O3 -march=x86-64 -mtune=generic -ffp-contract=off \
  -fno-math-errno -fno-tree-vectorize -S -masm=intel -fverbose-asm \
  crates/faun/examples/nbody/reference.c -o /tmp/nbody-c.s
```

Build once in each revision, preserving binaries under distinct names. For
the changed revision:

```sh
nix develop --command cargo build --release
target/release/faun build crates/faun/examples/nbody/main.fn -o /tmp/nbody-after
target/release/faun emit machine crates/faun/examples/nbody/main.fn > /tmp/nbody.ir
objdump -D -b binary -m i386:x86-64 -M intel /tmp/nbody-after > /tmp/nbody.asm
```

Compare energy text before timing, preserving the raw timing samples as JSON:

```sh
python3 crates/faun/examples/compare.py --cpu 10 --argument 1000000 \
  --check 0,1,10,1000,10000,100000 \
  /tmp/nbody-before /tmp/nbody-after /tmp/nbody-c-scalar /tmp/nbody-c-auto
```

Choose a permitted, idle CPU and check its SMT sibling as well. The script
warms each executable, alternates run order, checks every timed output and
reports seven-run medians. `--argument 50000000 --runs 1` performs the longer
correctness comparison without treating one run as a stable timing estimate.

Use `/tmp/nbody-before` for the baseline build. The ELF has no section or symbol
table, so raw disassembly includes headers and data as well as code.
`faun emit target` prints prepared machine IR, not assembly.

```sh
python3 - /tmp/nbody-before /tmp/nbody-after <<'PY'
import os
import statistics
import subprocess
import sys
import time

os.sched_setaffinity(0, {0})  # Choose an allowed, otherwise idle CPU.
programs = sys.argv[1:]
expected = b"Ok(-0.169075164\n-0.169086185)\n"
samples = {program: [] for program in programs}
for program in programs:
    assert subprocess.check_output([program, "1000000"]) == expected
for trial in range(7):
    for program in programs[::1 if trial % 2 == 0 else -1]:
        start = time.perf_counter()
        output = subprocess.check_output([program, "1000000"])
        samples[program].append(time.perf_counter() - start)
        assert output == expected
for program, times in samples.items():
    print(program, "median", statistics.median(times), "seconds", times)
PY

perf stat -e cycles:u,instructions:u,branches:u,branch-misses:u \
  taskset -c 0 /tmp/nbody-after 1000000
perf record -e cycles:u -c 200000 -- /tmp/nbody-after 3000000
```

Validation: `nix develop --command just check` and
`nix develop --command just test`; the latest full suite has 738 passing tests,
one skipped, plus passing doc tests. The C reference also passed AddressSanitizer
and UndefinedBehaviorSanitizer at 100,000 steps. Tests cover recursive and repeated stack
arguments/results under register pressure, full-width unsigned multiplication,
common-expression scope and effects, and managed aliases across wide calls on
all three backends.

One full-suite run failed `check::tests::receiver_type_selects_a_method` in
untouched frontend code. Its isolated retry and the subsequent complete suite
passed. That intermittent test failure remains to investigate separately.
