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

Runtime bigint storage/operations and native multiply/divide selection remain
subsequent work. The `U8` and `Int` definitions below work in Barb constant
evaluation/folding. They do **not** add runtime product/sum representation support
to machine lowering or any target, nor do they make unbounded signed magnitudes
fit a machine word. No `U8` packing or signed machine arithmetic is claimed.
Unused library types/functions do not require runtime representations: all three
files may be prepended to a Nat-only program. Representation checks follow the
code actually lowered, excluding impossible arms and tails after an exit.
Any remaining runtime `U8` or `Int` value is still rejected, not silently erased.

## Bytes: `u8.fn`

Prepend `nat.fn`, then `u8.fn`. All functions are ordinary source definitions.
`U8` has eight `Bool` fields, **least significant bit first**:

```text
U8(True False False False False False False False)
```

This is one. There are exactly 256 constructible values. Faun has no constructor
privacy, so a public `U8(Nat)` wrapper would not enforce a byte invariant; eight
bits do, even when callers construct values directly. The fields describe a
semantic representation, not a promise about memory layout.

- `u8_zero()` returns zero; `u8_to_nat(byte)` returns a natural in `0..255`.
- `u8_from_nat_wrapping(n)` returns `n` modulo 256, even for huge naturals.
- `u8_from_nat_checked(n)` returns `U8Value(byte)` for `n < 256`, otherwise
  `U8Overflow`. Checked narrowing never silently wraps.
- `u8_add_wrapping(a b)`, `u8_sub_wrapping(a b)`, and `u8_mul_wrapping(a b)`
  operate modulo 256. In particular, byte `0 - 1` is 255, not natural monus zero.
- `u8_equals(a b)` and `u8_less_than(a b)` compare the unsigned representatives
  and return `Bool`.

For example, concatenating both files before this program computes 255:

```text
main!(h) ->
  one = u8_from_nat_wrapping(Succ(Zero))
  exit!(h u8_to_nat(u8_sub_wrapping(u8_zero() one)))
```

The explicit wrapping/checked distinction follows Ori's modular-byte approach,
but the finite structural representation does not depend on module privacy.
There is no byte literal syntax, implicit conversion, or spelling-based compiler
intrinsic. Division, remainder, bitwise operations, and checked arithmetic are
not provided yet.

## Signed integers: `int.fn`

Prepend `nat.fn`, then `int.fn` (independently of `u8.fn`). Both libraries can also
be concatenated together after a **single** copy of `nat.fn`; all new functions
and helper names are prefixed `u8_` or `int_`. Helpers remain publicly callable
because there are no modules yet.

`Int = Pos(Nat) | NegSucc(Nat)`, following Ori's inductive signed representation:

- `Pos(n)` means `n`, including the unique zero `Pos(Zero)`.
- `NegSucc(n)` means `-(n + 1)`; `NegSucc(Zero)` is minus one, **not** minus zero.

Every constructible `Int` has a unique mathematical value, so canonical zero
requires no hidden invariant or compiler rewrite of observable constructors.

- `int_zero()`, `int_from_nat(n)`, and `int_negate(a)` construct integers.
- `int_abs(a)` returns a natural magnitude; `int_is_negative(a)` returns `Bool`.
- `int_to_nat_checked(a)` returns `IntNatural(n)` for nonnegative values,
  otherwise `IntNegative`; it neither clamps nor drops the sign.
- `int_add(a b)`, `int_sub(a b)`, and `int_mul(a b)` implement unbounded signed
  arithmetic with no overflow/wrapping. Signed subtraction is not monus.
- `int_equals(a b)` and `int_less_than(a b)` return `Bool`; ordering reverses the
  natural magnitudes for two negatives.

Signed division/remainder are deliberately absent: neither truncating nor
Euclidean semantics have been selected by these definitions. Parsing, formatting,
and signed literals are also outside this slice.

The library tests validate the concatenated source, enumerate every byte
representation, exercise wrap/checked boundaries and signed zero/sign cases,
and evaluate/fold large magnitudes beyond host-word limits. They also rename
types/functions and reorder constructors to check that meaning is structural.
