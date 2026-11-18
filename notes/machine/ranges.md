# Ranges

Barb works out what every number in a program can be, so that machine IR
can hold a natural known to be small in a word with no tag to test
([numbers](../values/numbers.md#how-a-nat-runs)). This note owns how: the
abstract domain, which values are related, the engine that goes round a
recursion, and what each costs. What comes out is the same `Ranges`
lowering has always read, a least and a greatest for every term,
parameter, answer and field.

## Three stages

The analysis is a numeric program in, ranges out:

1. **Extract** (`barb/numeric.rs`). Each Barb definition is read once into
   a numeric program: statements that copy a value, are a constant, build
   a constructor, call a definition or an operation, or match a value with
   arms that each say what holds on entry. A tag is the number it is, a
   sequence its length, a field a slot shared by every value built into
   it, a record a value nothing is known of. Each statement keeps the Barb
   term it came from and the site that makes its value.
2. **Solve** (`barb/solve.rs`, with `packs.rs`). A solver generic over the
   relational domain, `solve::<D: Domain>(&Numeric, Scope) -> Solution`,
   chooses packs from the numeric program once and runs the engine below.
   It reads nothing of Barb, so a test writes a numeric program by hand.
3. **Map back** (`barb/bounds.rs`). What the solver found, by term,
   definition and slot, becomes `Ranges`: nothing reached is anything, a
   spine's rest says nothing, and what is assumed of a field holds.

The compiler solves with `Octagon`. The solver is generic over a `Domain`
trait (`barb/octagon.rs`), and the tests solve the same programs with
`Zone`, an octagon whose sums are forgotten after every step, and
`Intervals`, which relates nothing, checking octagons prove at least what
each does. A pack is shared between a match's arms until one says something
of it, so taking a state into an arm copies only what the arm changes.

## The domain

Every value a body binds has an interval, a least and a greatest, the
greatest missing for a natural nothing bounds. Some values have more: a
constraint of the form `±x ±y <= c` between two of them, which is an
octagon (Miné, 2006). `i < len` is `i - len <= -1`; `bit + 9 <= total` is
`bit - total <= -9`, since the sum is `bit` plus a constant; a count beside
the list it walks keeps `count + rest <= C`. A bound learned later on one
side reaches the other through the constraint.

An octagon over `n` values is a matrix of `2n` by `2n` bounds, one row for
`+x` and one for `-x`. Closing it, shortest paths, then each value's own
bound made even, then every entry tightened by its two values' own bounds
(Bagnara, Hill and Zaffanella, 2008), makes every constraint as tight as
the others imply; the tests check that against every integer point of
small octagons. Adding one constraint to a closed matrix closes again in
`O(n^2)`, going through only the constraint's four nodes; a value just
bound from another, `s = a + [lo, hi]`, takes `a`'s row moved, in `O(n)`.
A matrix whose closure finds a negative cycle holds no values, and the arm
that built it is never reached.

Naturals are at least nought, and that is said of every value. A natural
past 2^64 is still known exactly where it is a constant, beside the
octagon, as it was beside the interval: a remainder by 2^64 is a word. A
constructor's field holds an interval, every value built into it, as
before; fields are global and relate to nothing.

## Packing

A value is related only where the program relates it. Before a definition
is walked, a pass over its body groups its values: the two sides of a
comparison; a sum or a difference and its operands, a constant operand
being an offset rather than a value; a step and what it steps; a match's
rest and what it took apart; a length and its list; and, in a definition
that goes round, the numbers and lengths a recursive call hands on, with
the parameters they become. Only a value reaching a comparison or a
recursive call through these is grouped. Each group, a pack, is one
octagon; any other value is an interval alone.

A value is the place that makes it, not its level: two arms side by side
bind the same levels to different values. Within a pack, a value takes
the next place no value of the pack still in scope holds, so arms side by
side share places, and a pack's matrix is as large as the most of its
values in scope at once. A pack groups at most 96 values.

Octagons are kept in every definition, a loop or not. Keeping them only
in definitions that go round costs less, but makes a cliff of where a
guard is written: the same `bit + 9 <= total` bounds `bit` in a recursion
and is lost one helper away, and 485 ranges came out wider than the walk
this replaced. Performance should not depend on how a program is spelled,
so there is one mode.

## What a term says

- **A comparison** answers a `Bool` that carries, for each tag, what it
  says: `True` of `a < b` is `a - b <= -1`, `False` is `b - a <= 0`.
  Matching the `Bool`, now or after handing it through a binding, says that
  tag's constraint and closes.
- **A match answering tags** carries, for each tag an arm can answer, what
  that arm learned of the values before the match, and what its last term
  says of that tag besides. A tag several arms answer carries what all of
  them learned, joined, however many tags there are. So the `True` of
  `a < n & b < m` says both held. This is gathered only for a match whose
  answer is matched again on its tag.
- **A sum** `s = a + b` says `s - a` lies in `b`'s interval and `s - b` in
  `a`'s. A difference, which stops at nought, says `s <= a`. A step says
  `s - n = 1`.
- **A call** hands its callee what holds of its arguments: their intervals,
  and the constraints between any two, from their pack or their intervals.
  A definition starts from what every call to it hands it, joined, closed.

## The engine

A worklist of definitions, callees first, walked in sweeps: a sweep walks
what is waiting in order, and a definition waits again when what it is
handed, what something it calls answers or a field it reads grows. A
value, an entry, an answer or a field, counts a sweep it grew in; past
eight such sweeps, a bound that moved jumps to the next threshold: a
machine width, 2^8, 2^16, 2^32 or 2^64 less one, the most a sequence's
length can be, or one less than a divisor the program names; and past the
widest to none. A constraint between two parameters widens to the widths
alone. Counting sweeps rather than walks keeps a value many callers each
hand a little more from being taken for a value counting up. A recursive
call handing on a value no more than the parameter it becomes hands on
only how low it goes, and one handing a parameter on unchanged hands
nothing, so a bound widened while callers settled comes back down.

Every value has finitely many thresholds to pass, so the walk settles;
there is no round limit, and no forgetting everything when one runs out.
Narrowing then walks every definition again from the settled state,
without widening, at most eight times.

## What it replaced

| Was                                  | Now                                   |
| ------------------------------------ | ------------------------------------- |
| a guard narrowing a sum's operands   | the sum's constraints, closed         |
| `refine` of `a < b` by intervals     | `a - b <= -1`, kept relational        |
| per-tag implications, 8 tags at most | per-tag constraints, any tags         |
| `counters.rs`, a count beside a walk | `count + rest <= C`, kept by widening |
| 32 rounds, then forgetting all       | sweeps; widening per value; no limit  |

`affine.rs`, a sum of atoms times constants, answers what an index is in
terms of others for addressing, a different question, and stays. Machine
IR's guard analysis, `ir/bounds.rs`, reads comparisons of machine values
that Barb's terms no longer name one for one, and stays.

## What it costs and earns

Measured on the examples, the workloads and the probes, 98 programs, for
x86-64 with the stock backend, with a sequence's length bounded by memory
in every mode but the old analysis. Naturals are the values machine IR
holds as `natural`, not as a word; analysis is the compiler's instructions
analysing twice less analysing once. Before is the walk over Barb itself;
after is the three stages, which find the same ranges, byte for byte, in
every mode. The modes other than octagons were measured on the way, and
octagons everywhere is what the compiler does.

| Mode               | Naturals | Analysis, before | after  | Compiling, after |
| ------------------ | -------- | ---------------- | ------ | ---------------- |
| old walk           | 23,632   | 16.9 G           |        | 153.6 G          |
| intervals          | 23,842   | 16.0 G           | 11.4 G | 146.8 G          |
| zones              | 22,733   | 51.0 G           | 40.2 G | 171.8 G          |
| octagons in loops  | 22,007   | 39.1 G           | 28.7 G | 158.2 G          |
| octagons, the mode | 21,923   | 51.6 G           | 38.6 G | 167.8 G          |

Profiled before the stages, timing each part of the walk on gzip, a PNG
decoder, a JSON decoder, n-body and k-nucleotide: closing octagons took 10
to 35%, copying the state into each arm of a match 20 to 30%, walking Barb
itself 30 to 55%, gathering what a match's tags say 5 to 7%, and handing
calls their arguments 2 to 7%; joins, packs and narrowing took little. A
zone costs what an octagon does because it is one, its matrix closed the
same way. After the stages, closing is most of what is left.

On wasm32 the same programs hold 29,297 naturals with the old walk, 29,281
with zones, 29,468 with octagons in loops and 28,465 with octagons
everywhere: there, the old walk's guard on a sum outside a loop is worth
more than octagons in loops make up.

Packs are small. With octagons everywhere, 3,073 of 5,339 definitions
compiled have a pack; a pack's matrix is 3 values at the median, 6 at the
90th percentile and 24 at most; a definition's packs hold 4 places at the
median, 10 at the 90th percentile and 84 at most.

Sums earn their keep over zones: 810 naturals fewer, the counters among
them, at the same cost. Octagons outside loops earn 84 naturals on x86-64
and 1,003 on wasm32, where without them a guard on a sum outside a loop is
lost, and cost most where software float routines relate dozens of values
a pack: n-body, mandelbrot and spectral-norm compile in about twice the
instructions. Against the old walk under the same assumptions, a length
bounded by memory in both, no range is wider but for 1,981 terms, matches
and fields the octagons prove unreached, such as `List.drop` of a 256-entry
table by an index below 256 coming back empty.

## Memory bounds a length

A sequence's elements each take a byte at least, so no sequence is longer
than the memory a target addresses: 2^47 bytes on x86-64, 2^32 on wasm32,
2^16 on the 6502. With that bound, a position compared with
`input.len() * 8` is a word, and the `position` probe runs 19.5 million
instructions where it ran 57.7, against 29.1 for its workaround.
