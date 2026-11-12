# Floats

This note owns `F32` and `F64`, IEEE 754 binary32 and binary64: how a float
is written, what each operation answers, how floats compare and hash, and
how they run. The standard library's `float/format.fn` points here for the
contract as a whole.

## Writing a float

A numeral with a point is a float, and only a float: `1.5`, `0.1`,
`1.0e-12`, `2.5E2`. Its position makes it an `F32` or an `F64`, and where
nothing decides it is an `F64`. It is built through the float's
`of_decimal(digits, scale)`, which is `digits / 10^scale` correctly rounded.
`-1.5` is its `neg`. A numeral without a point is never a float:

```
error: a numeral with no point is not a float: write the `F64` with one, as `3.0`
```

A decimal is refused at a `Nat` or a word, and it cannot be a pattern; a
clause tests a float in a guard. Integers become floats through explicit,
correctly rounded conversions: `of_nat`, `of_int`, and `of_u8` through
`of_u64`. `from_nat` and `from_int` answer `Err(Inexact)` rather than round,
so `F64.from_nat(2.pow(53) + 1)` is `Err(Inexact)`.

## The contract

Every exported operation keeps these rules. `examples/floats/` asks each of
them of both widths as expectations whose answers are the host FPU's.

- **Correctly rounded.** `add`, `sub`, `mul`, `div`, `sqrt` and `fma`
  compute the exact result and round it once, to nearest, ties to even, as
  the standard specifies. So do the conversions and the roundings to an
  integer value (`trunc`, `floor`, `ceil`, `round`, `round_even`).
  `integer_part` answers the integer exactly, or `Err(NotFinite)` for a NaN
  or an infinity.
- **One rounding, always.** There is no rounding mode, no status flag and no
  trap. An invalid operation answers the NaN, overflow an infinity, and a
  nonzero over zero a signed infinity. Subnormals are values like any other.
- **No contraction.** `a * b + c` rounds twice on every target. `fma(a, b,
  c)` rounds once, and is the only way to get that.
- **One NaN.** A NaN's sign and payload are not part of its value. The only
  methods that read a pattern, `to_bits`, `cmp` and `sign_bit`, read every
  NaN as one, `0x7ff8000000000000` for an `F64`.
- **Text round-trips.** `to_str` writes the shortest decimal that reads back
  as the value, always as a float literal: `1.0`, `0.1`, `-0.0`, `NaN`,
  `Infinity`, `1.5e21`. `from_str` reads any decimal correctly rounded, so
  the two compose to the identity. `to_fixed`, `to_exponent` and
  `to_precision` round the exact value once at the chosen digit.

```ruby
expect 0.1 + 0.2 != 0.3
expect 0.1.add(0.2).to_str() == "0.30000000000000004"
expect F32.add(0.1, 0.2) == 0.3
expect 0.1.fma(10.0, -1.0) != 0.1 * 10.0 - 1.0
expect 1.0 / 0.0 == F64.infinity & (0.0 / 0.0).is_nan()
expect 1234.5678.to_fixed(2) == "1234.57"
```

The standard library has constants (`nan`, `infinity`, `zero`, `largest`,
`smallest_normal`, `smallest_subnormal`, `epsilon`, `pi`), `abs`,
`copy_sign`, `min`, `max`, `of_bits`, and the tests `is_nan`,
`is_infinite`, `is_finite`, `is_zero` and `is_subnormal`. It has no
transcendental functions: no `exp`, `log` or `sin`.

## Equality and order

`cmp` is the standard's total order (IEEE 754 clause 5.10) over values with
one NaN: `-Infinity`, the negatives, `-0.0`, `0.0`, the positives,
`Infinity`, then NaN. As for every ordered type, `equals` and `<` are views
of `cmp` ([operators](../forms/operators.md)). The hardware's comparisons
have their own names:

```ruby
expect F64.nan == F64.nan & -0.0 != 0.0 & -0.0 < 0.0
expect F64.numeric_equals(-0.0, 0.0) & !F64.numeric_equals(F64.nan, F64.nan)
expect F64.partial_cmp(F64.nan, 1.0) == Err(Unordered)
expect [F64.nan, 1.0, 0.0, -0.0].sort() == [-0.0, 0.0, 1.0, F64.nan]
expect Map.of_list([(F64.nan, 1)]).get_or(F64.nan, 0) == 1
expect Set.of_list([0.0, -0.0, 0.0]).len() == 2
```

`partial_cmp` agrees with `cmp` except on a NaN, which is `Err(Unordered)`,
and on the two zeros, which are `Ok(Eq)`. `min` and `max` follow the total
order, so `F64.nan.max(1.0)` is the NaN. `hash_into` feeds `to_bits`, so
equal values hash alike.

## How floats run

`F32` and `F64` are Faun source under `standard/float/`. The core,
`format.fn`, takes a format as a record: the precision, the exponent range,
the sign bit. It unpacks each operand into sign, mantissa and exponent,
computes the exact result on unbounded naturals, and rounds once. `f32.fn`
and `f64.fn` are thin wrappers over a private `U32` or `U64` holding the
bit pattern. The definitions came over from Ori whole.

`add`, `sub`, `mul`, `div` and `sqrt` are the one place the compiler takes a
meaning from a name. Lowering tells Barb that these five, at each float's
own type, compute that IEEE 754 operation (a claim). The definition stays,
and answers wherever nothing faster does:

- **x86-64** emits one SSE2 instruction, `addsd` or `sqrtss` and so on.
- **wasm32 and the 6502** have no float instructions in Faun today, and run
  the definitions.
- **Constant folding** answers a claimed call with the compiler's host
  arithmetic.

A hardware NaN may be any NaN's pattern, which no program can tell. The
expectations in `examples/floats/` are asked twice, once compiled for the
machine and once of the definitions alone, and must agree.

`of_nat` below `2^52` (`2^23` for `F32`) is a claimed subtraction too: the
pattern of `2^52 + n` less `2^52`, both exact. What is left in software,
`fma`, `of_decimal`, the other conversions and the text, costs thousands of
instructions an operation. A decimal numeral is folded at compile time, but
slowly, and n-body still calls `of_decimal` at startup for a few long
literals ([n-body](../nbody-performance.md)).

## Rationale

### Why is `3` never an `F64`?

Because a plain numeral means an exact integer, and every type it may be
holds the value or refuses it. An `F64` holds every integer only up to
`2^53`, so `9007199254740993` at an `F64` would silently be one less. The
point says which arithmetic is in play. A reader of `x * 2` knows it is
exact, and of `x * 2.0` that it rounds. `1.5` is never a `Nat`, for the
same reason in reverse.

The cost lands on generic code. `double(x) -> x.mul(2)` serves every
integer type but is refused at `F64`, since its `2` cannot be a float. Write
`x + x`, or take the constant as a parameter. Haskell's `fromInteger` lets
`3 :: Double` through, and with it every integer literal into rounded
arithmetic.

### Why does a NaN equal itself?

Because `equals` is what `Map`, `Set`, `contains` and derived record
equality use, and they need an equivalence. Under the hardware's `==` a NaN
key can be inserted and never found, and a `Set` can hold it many times;
Python's `float('nan')` keys show both. In Faun every ordered type has
`equals` from its `cmp`, so the two cannot disagree. The standard already
defines a total order, so none was invented. The same reasoning makes
`-0.0` and `0.0` two values, as their patterns are.

The cost is that `-0.0 == 0.0` is false, and that `<` is the total order's,
so `1.0 < F64.nan` is true where the hardware says false. Code that wants
the hardware's answers names them: `numeric_equals`, `partial_cmp`,
`is_nan`. It costs little time: an `F64`'s place in the order is its
pattern with the bits of a negative one flipped and the sign bit of any
other set, a word, so a comparison is one of two words. Worked out as a
natural, as the core's `rank` gives it, a positive pattern's place lies
past a word, and mandelbrot's escape test ran eight times slower.

### Why one NaN?

Hardware disagrees about NaN bits. x86 and ARM answer `0.0 / 0.0` with NaNs
of different signs, and wasm leaves the bits open. Faun answers the same on
every target, so those bits must not reach a program. Making every
operation fix its NaN up would cost a compare and a blend after each one.
Instead the three methods that read a pattern read every NaN as one, which
costs the hardware nothing per operation. The cost: a codec writing floats
as bits does not round-trip NaN payloads, and what `neg` does to a NaN's
sign cannot be seen.

### Why no rounding modes or exception flags?

Both are state. A mode changes what every later operation means, and a flag
records what earlier ones did; a pure function can hold neither. The cost
is that inexactness and underflow cannot be detected after the fact, and
interval arithmetic would need directed operations of its own, which do not
exist.

### Why are floats software-defined, with five operations claimed?

So the definition is the specification, and it runs. Written over unbounded
naturals, each operation is its exact result and one rounding, with the
standard's special cases as clauses. It answers the same bits on every
target, including those with no float unit, and in the compiler's own
folding. Ori's oracle harness held these definitions to the host FPU over
roughly 166,000 adversarial cases per width before Faun ported them, so
selecting an instruction is a checked optimization, not the semantics.

The claim exists because recognition cannot reach this far. Barb
recognizes `Nat`'s addition by checking its equations by induction, but no
such check shows that a file of unpacking and rounding is IEEE 754 addition.
So the frontend says so, for five operations at two types, and the
expectations are asked both ways to keep the claim honest.

The cost is speed wherever a claim does not reach. In spectral-norm,
`F64.of_nat` rounding in software was four-fifths of a 6.31 s run; made a
claimed subtraction, the run took 1.04 s
([spectral-norm](../spectralnorm-performance.md)). With every operation in
its loop claimed, n-body's x86-64 code uses `addsd`, `mulsd`, `divsd` and
`sqrtsd`. A million steps take 0.05 s against scalar C's 0.03 s, and most
of what remains of the gap is its lists.

### Why not contract `a * b + c` into an `fma`?

Because it changes the answer. `0.1 * 10.0 - 1.0` is `0.0`, and
`0.1.fma(10.0, -1.0)` is about `5.55e-17`. A compiler that fused when the
machine allowed it would answer differently on different machines. `fma` is
there to ask for one rounding, and it runs in software today, since it is
not claimed.

## Related

- [Numbers](numbers.md): numerals without a point, and the integers floats
  convert from
- [Operators](../forms/operators.md): `cmp`, and `equals` and `<` as its
  views
- [Collections](collections.md): hashing, and why keys need a lawful
  `equals`
- [Architecture](../machine/architecture.md): how a claimed call reaches a
  target's instruction
- [N-body](../nbody-performance.md) and
  [spectral-norm](../spectralnorm-performance.md): float speed, measured
