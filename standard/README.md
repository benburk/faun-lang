# Arithmetic

`nat.fn` contains ordinary source definitions, not compiler intrinsics:

- `Nat = Zero | Succ(Nat)` is unbounded.
- `add`, `sub`, and `mul` are natural arithmetic; `sub` is monus.
- `div(x Zero) = Zero` and `mod(x Zero) = x`.
- `equals` and `less_than` return `Bool`.

There is no import syntax or automatic prelude yet. Prepend `nat.fn` to a
program's source before parsing it; do not also declare its types or functions.
Expressions currently use calls and constructors, for example:

```text
main!(h) ->
  two = Succ(Succ(Zero))
  exit!(h mod(mul(two Succ(two)) Succ(Succ(two))))
```

## Compilation

Barb validates the source, normalizes nonrecursive helpers, folds constants,
then recognizes arithmetic and derives ranges. Recognition checks structural
recursion equations, never function/type/constructor names. Constructor order
is irrelevant, including the order of `True` and `False`. Unsupported equivalent
spellings remain ordinary functions rather than being guessed at.

Constant evaluation keeps naturals encoded as arbitrary-precision magnitudes;
it does not expand their unary trees. Unrecognized recursion has a fuel budget,
and folded values have a size budget. Exhaustion leaves computation in place;
it does not introduce a numeric limit into the language.

Host return contracts supply finite ranges. `Target::routines()` resolves a
host word's width for that target. Builder clients can supply contracts with
`barb::Program::bound`. Comparisons refine their operands in each match arm,
and a branch that exits contributes no values to the continuation:

```text
bounded!(h True n) -> n
bounded!(h False n) -> exit!(h Zero)

main!(h) ->
  count = argc!(h)
  n = bounded!(h less_than(count Succ(Succ(Zero))) count)
  exit!(h add(n n))
```

Here `n` is at most one, but the sum needs two bits. More generally, bounded
operands do not imply that their result fits the same width.

## Current target boundary

Unknown or overflowing bounds select machine IR's `Class::Natural`, never
`Word`. Large constants use `NaturalConstant` with a compact magnitude in the
data pool. Promotions to arbitrary precision are explicit conversions.

The current targets **do not implement runtime bigints yet** and reject that
class explicitly. Values proven to fit use fixed-width operations; portable
regions implement monus, multiplication, division, and modulo on all three
targets. Multiplication currently uses repeated addition and division repeated
subtraction, so this is a correctness baseline, not fast arithmetic.

Runtime bigint storage/operations, native multiply/divide selection, `u8`, and
signed `Int` remain subsequent work. In particular, `Pos(Zero)` and `Neg(Zero)`
cannot be collapsed if constructors remain observably distinct.
