# Spectral-norm performance

[`main.fn`](../crates/faun/examples/benchmarks-game/spectral-norm/main.fn) ports the benchmarks
game's [spectral-norm](https://benchmarksgame-team.pages.debian.net/benchmarksgame/description/spectralnorm.html):
ten rounds of the power method on the leading `n` by `n` corner of the
matrix whose entry at row `i` and column `j`, from nought, is
`1 / ((i + j)(i + j + 1) / 2 + i + 1)`. Each round multiplies by the matrix
and its transpose twice, so a run computes `40 n²` entries. Where n-body
steps five records many times, this walks long lists of `F64`: a multiply
folds over `u` once per row, carrying the column beside the sum, and maps a
fresh list of row sums out of `List.range(n)`.

## Where it stands (2026-10-03)

Five alternating, warmed runs on a Ryzen 9 9950X, pinned to **CPU 10**;
compilation excluded, process startup and output included:

| Program             | `n = 1000` | `n = 5500` |
| ------------------- | ---------: | ---------: |
| Faun                |   0.0479 s |    1.416 s |
| Scalar C            |   0.0309 s |    0.922 s |
| C (auto-vectorized) |            |    0.922 s |

Faun is **1.54×** behind scalar C at the game's workload of 5,500, whose
norm both print as the game's `1.274224153`. The answers also agree at 1,
2, 3, 7, 10, 100, 500, 1,000 and 2,000; at 100 the norm is the game's
`1.274219991`. C computes 1.2 billion entries in 0.92 s, about four cycles
each, which is about what one core's divider allows, so vectorizing gains it
nothing; Faun's half second more is the walks around the division.

## Writing the entry in floats

The program takes the indices as `F64`: the row converted once per row,
the column a float counter the fold carries. Every number in the entry is
whole and below `2⁵³`, so exact, and halving by `* 0.5` is exact too; the
entry is the one integers would give, bit for bit, until
`(i + j)(i + j + 1)` passes `2⁵³` near `n = 47,000,000`.

That is how some of the game's short programs take them. Sorted by gzipped
source size, [Chapel #2](https://benchmarksgame-team.pages.debian.net/benchmarksgame/program/spectralnorm-chapel-2.html)
(348 bytes) and [Haskell GHC #2](https://benchmarksgame-team.pages.debian.net/benchmarksgame/program/spectralnorm-ghc-2.html)
(410) compute the entry on reals; C #8, OCaml #2, Go and Julia #2 (377 to
417) on machine integers, which in C #8's 32-bit `int` overflow past about
`n = 23,000`. SBCL #6 declares its integers `(signed-byte 31)`, an assertion
it checks and propagates to the loop counters. Faun's `Nat` neither wraps
nor takes declarations, so writing the entry in integers costs it what the
next section measures.

Faun's program is 490 bytes gzipped, without comments and expectations,
against 495 for the integer version it replaced: one `times` taking the
entry as a function serves both the matrix and its transpose.

## The integer version, and what it showed

The first port computed the entry in `Nat`, as C #8 does in `int`, with the
column a `Nat` counter:

```faun
entry(i, j) -> (
  diagonal = i + j
  1.0 / F64.of_nat(diagonal * (diagonal + 1) / 2 + i + 1)
)
```

Three alternating runs at `n = 1000`, same conditions, the exact `of_nat`
row measured again on 2026-11-03:

| Program                           | Median elapsed |
| --------------------------------- | -------------: |
| Faun, `Nat` entry (`9e47e44`)     |         6.31 s |
| Faun, `Nat` entry, exact `of_nat` |         0.84 s |
| Faun, `F64` entry, as now         |       0.0479 s |
| Scalar C                          |       0.0309 s |

`F64.of_nat` rounded in software (`round_pack`), four-fifths of the first
run. Below `2⁵²` it now takes `2⁵²` away from
`of_bits(0x4330000000000000 + n)`, the pattern of `2⁵² + n`, which leaves
`n`; both steps are exact, and the subtraction is the claimed one, so x86-64
answers it with `subsd`. `F32.of_nat` does the same below `2²³`. Claiming
`of_nat` itself, as `add` is claimed, would not have been simpler: a claim
takes and answers patterns of one format, and a claimed definition is never
emitted, so a natural of any size would need a new operand kind and a
software path kept for numbers past a word.

What was left was the `Nat` arithmetic. Single runs at `n = 1000`, each a
different spelling of the integer version, measured again on 2026-11-03,
once a `U64`'s arithmetic was worked out in machine words:

| Entry                                           | Elapsed |
| ----------------------------------------------- | ------: |
| `Nat`, as above                                 |  0.84 s |
| `Nat`, guarded by `i < 2³⁰ & j < 2³⁰`, else NaN |  1.00 s |
| `U64` indices and arithmetic                    |  0.11 s |
| `F64` indices, the row converted once per entry |  0.15 s |

The machine IR says why:

- The row `i` comes from `List.range`, whose elements range analysis knows
  are below a length, so it is a word. The column is the fold's counter,
  which nothing ties to the list's length, so it is a `natural`, and every
  sum, product and quotient of it checks for an immediate.
- A guard narrows nothing: inside `j < 2³⁰` the arithmetic is still
  `natural`. The fast path of `of_nat` works out its `n + 0x4330…` in
  words, but passes it to `wrap64` as a `natural`, a call for every entry.
- `U64.mul` is `(a * b) % 2⁶⁴`, which is one `imul`: the `U64` entry's sum,
  product and halving are word instructions, and only `F64.of_nat` is a
  call.

## Next experiments

For this program, the half second Faun spends beyond C's divisions:

1. **Compare the inner loop with C's.** Read the machine code for the fold
   over `u`: the tuple it carries, the call through `at`, and the index
   and uniqueness checks of the walk, against C's few instructions around
   `divsd`.
2. **The lists between rounds.** Whether the list `List.range` builds is
   fused into the `map`, and whether each round's lists reuse the buffers
   the last one freed.

For integer programs like the first version, which are common:

1. **Narrow after a comparison.** Inside the branch where a `natural`
   passed `x < K`, with `K` small enough, hold `x` as a word. That makes
   `of_nat`'s add and `wrap64` word operations, and a guarded entry word
   multiplication and division.
2. **Bound fold counters.** A counter starting at a constant and stepped by
   one per element of a walk is below the start plus the list's length,
   which makes it a word as the row is.
3. **Recognize wrapping multiplication.** Done: `(a * b) % 2⁶⁴` of two
   words is one `imul`, as the words' `and`, `or` and `xor` are recognized,
   and their sums and differences one instruction each.

## Reproduce

```sh
gcc -std=c11 -O3 -march=x86-64 -mtune=generic -ffp-contract=off \
  -fno-math-errno -fno-tree-vectorize -Wall -Wextra -Werror \
  crates/faun/examples/benchmarks-game/spectral-norm/reference.c -lm -o /tmp/spectralnorm-c-scalar
gcc -std=c11 -O3 -march=x86-64 -mtune=generic -ffp-contract=off \
  -fno-math-errno -Wall -Wextra -Werror \
  crates/faun/examples/benchmarks-game/spectral-norm/reference.c -lm -o /tmp/spectralnorm-c-auto
nix develop --command cargo build --release
target/release/faun build crates/faun/examples/benchmarks-game/spectral-norm/main.fn -o /tmp/spectralnorm-faun
python3 crates/faun/examples/compare.py --cpu 10 --argument 5500 \
  --check 1,2,3,7,10,100,500,1000,2000 --runs 5 \
  /tmp/spectralnorm-faun /tmp/spectralnorm-c-scalar /tmp/spectralnorm-c-auto
```

[`reference.c`](../crates/faun/examples/benchmarks-game/spectral-norm/reference.c) keeps
Faun's order of operations: the indices as doubles, the column counted in
them, each row summed left to right from nought, and the two final sums in
one pass. At `n = 0` Faun prints `NaN` and C `-nan`, so the comparison
starts at one.
