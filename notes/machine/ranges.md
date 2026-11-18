# Ranges

Barb works out what every number in a program can be, so that machine IR
can hold a natural known to be small in a word with no tag to test
([numbers](../values/numbers.md#how-a-nat-runs)). This note owns how: the
abstract domain, which values are related, the engine that goes round a
recursion, and what each costs. The code is `crates/core/src/barb/bounds.rs`
and `octagon.rs`; what comes out is the same `Ranges` lowering has always
read, a least and a greatest for every term, parameter, answer and field.

## The domain

Every value a body binds has an interval, a least and a greatest, the
greatest missing for a natural nothing bounds. Some values have more: a
constraint of the form `±x ±y <= c` between two of them, which is an
octagon (Miné, 2006). `i < len` is `i - len <= -1`; `bit + 9 <= total` is
`bit - total <= -9`, since the sum is `bit` plus a constant; a count beside
the list it walks keeps `count + rest <= C`. A bound learned later on one
side reaches the other through the constraint: when `len` is found below
2^47, so is `i`, wherever the guard was.

An octagon over `n` values is a matrix of `2n` by `2n` bounds, one row for
`+x` and one for `-x`. Strong closure, Floyd–Warshall over the matrix and a
pass pairing `x` with `-x`, with bounds rounded to integers, makes every
constraint as tight as the others imply. Closure is what answers a question;
adding one constraint to a closed matrix and closing again costs `O(n^2)`.
A matrix whose closure finds a negative cycle holds no values, and the arm
that built it is never reached.

Naturals are at least nought, and that is said of every value. A natural
past 2^64 is still known exactly where it is a constant, beside the
octagon, as it was beside the interval: a remainder by 2^64 is a word. A
constructor's field holds an interval, every value built into it, as
before; fields are global and relate to nothing.

## Packing

A closure is cubic, so one matrix over every value of a definition would
cost too much where bodies are long. Values are related only where the
program relates them. Before walking a definition, a pass over its body
groups its values:

- the two sides of a comparison;
- a sum or a difference and its operands, a constant operand being an
  offset rather than a value;
- a step, `Succ(n)` or a list built one longer, and what it steps; a match
  taking a step apart and the rest it binds; a length and its list;
- a recursive call's argument and the parameter it becomes, and the
  definition's own related parameters together, which is where a counter's
  sum lives.

Only a value that reaches a comparison or a recursive call through these is
grouped at all. Each group, a pack, is a matrix of its own; any other value
is an interval alone. A pack has a size limit, past which a grouping is
refused and the relation falls back to intervals.

## What a term says

- **A comparison** answers a `Bool` that carries, for each tag, the
  constraint it holds: `True` of `a < b` says `a - b <= -1`, `False` says
  `b - a <= 0`. Matching the `Bool`, now or after handing it through a
  binding, adds that tag's constraint and closes.
- **A match answering tags** carries, for each tag an arm can answer, what
  that arm learned of the values before the match: the intervals and
  constraints it narrowed. A tag several arms answer carries what all of
  them learned, joined. So the `True` of `a < n & b < m` says both held, and
  a guard written as a helper returning a `Bool` narrows as one written in
  place.
- **A sum** `s = a + b` says `s - a` lies in `b`'s interval and `s - b` in
  `a`'s; with `b` a constant, `s - a = b` exactly. A difference, which stops
  at nought, says `s <= a`. A step says `s - n = 1`.
- **A call** hands its callee what holds of its arguments: their intervals,
  and the constraints between any two in one pack. A definition starts from
  what every call to it hands it, joined.

## The engine

A worklist of definitions, ordered by the call graph's strongly connected
components so that callers settle before what they call. A definition is
walked again when what it is handed, what something it calls answers, or a
field it reads grows.

Growth stops by widening. A value that keeps growing past a few changes, a
recursion's entry, a field or an answer, is widened: a bound that moved
jumps to the next machine width, 2^8, 2^16, 2^32 or 2^64 less one, and then
to none, and a constraint that loosened is dropped from the entry kept for
the next widening, though not from the closed one the walk reads. The
widths are thresholds so that a value kept below 4096 by a remainder
settles at 65535 rather than losing its bound and every bound copied from
it. A constraint like `count + rest <= C` does not move round a self-call,
so it survives widening untouched, and with it the bound on the count.

Every bound can only move a few times, so the walk always settles; there
is no round limit, and no fallback where it runs out. Narrowing then walks
every definition again from the settled state, without widening, to take
back what widening gave up beyond what the program reaches.

## What it replaces

The interval walk this replaces carried special cases, each a shape of
relation an interval cannot hold:

| Was                                  | Now                              |
| ------------------------------------ | -------------------------------- |
| a guard narrowing a sum's operands   | the sum's constraint, closed     |
| `refine` of `a < b` by intervals     | `a - b <= -1`, kept relational   |
| per-tag implications, 8 tags at most | per-tag constraints, any tags    |
| `counters.rs`, count beside a walk   | `count + rest <= C`, by widening |
| 32 rounds, then forgetting all       | widening per value; no limit     |

`affine.rs`, a sum of atoms times constants, answers a different question,
what an index is in terms of others for addressing, and stays.

## Cost

A walk of a definition costs what it did, plus for each relational step
`O(k^2)` in the size `k` of its pack, and `O(k^3)` for a full closure, which
only a call's entry and a joined match take. Packs are small in practice: a
loop's index, its bound and their steps. The limit on a pack's size bounds
the worst case at a constant times the old walk's.

## Memory bounds a length

A sequence's elements each take a byte at least, so no sequence is longer
than the memory a target addresses: 2^47 bytes on x86-64, 2^32 on wasm32,
2^16 on the 6502. With that bound, a position compared with
`input.len() * 8` is a word.
