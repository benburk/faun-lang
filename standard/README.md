# Standard libraries

## Ori-compatible bootstrap prelude

`standard/ori/standard.ori` is the first usable module prelude for the primary
frontend. It defines the Ori-compatible representations of `Nat`, `Int`, `U8`,
`List`, and `Str`, plus `Int.of_nat` and `Int.neg`, which contextual literal
elaboration needs. It is deliberately a bootstrap representation slice, not a
claim to be the complete Ori standard library.

```sh
ORI_STD=standard/ori/standard.ori cargo run -- check notes/examples/literals.ori
```

The loader treats this as an ordinary disk-backed package. Its exported names
are implicit in the checked program; private `Str` and `U8` wrappers remain
available only to blessed string construction.

## Arithmetic for the simple frontend

These `.fn` libraries belong to the archived `faun-simple` frontend. They remain
ordinary source definitions rather than compiler intrinsics. `nat.fn` provides:

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

The pipeline is validation/totality checking → bounded Barb optimization →
arithmetic recognition and range analysis → machine lowering/validation →
target preparation/runtime legalization → target acceptance and emission.

`barb::optimize` runs each stage once: structural normalization, nonrecursive
helper inlining, recognized arithmetic identities, constant folding, then
cleanup. `OptimizeOptions` and `read_with_options` expose pass controls without
bypassing validation. Inlining has per-function/program expansion budgets;
folding has aggregate work, encoded-size, and depth budgets. Exhaustion leaves
computation in place, not a numeric limit on the language. Constant evaluation
uses compact arbitrary-precision magnitudes rather than expanded unary trees.
Cleanup removes unused inert bindings while preserving eager calls and effects.

Recognition checks structural recursion equations, never function/type/constructor
names. Constructor order is irrelevant, including the order of `True` and `False`.
Unsupported equivalent spellings remain ordinary functions rather than being
guessed at. Arithmetic laws preserve monus and zero-divisor semantics; `x / x`
is not unconditionally one. Optional optimization does not authorize dropping
or reordering platform effects.

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

## Machine IR and execution checks

Machine-IR validation checks pool references, lexical value scope, operation
classes/arity, function signatures, and structured branch/loop transfers. These
are structural checks, not proofs of arithmetic bounds or memory safety; native
ABI and capacity limits are checked separately by targets.

`ir::evaluate` provides a deterministic reference interpreter with 16-, 32-, and
64-bit word configurations, checked memory access, host callbacks, and explicit
fuel/size limits. It evaluates `Natural` exactly and reports failed `Fixed` fit
assertions. Interpreter support does not imply native target support.

### Guarded runtime expression probes

The [shared expression corpus](../crates/faun/tests/support/expressions.rs) uses
`argc!` with a guard requiring `count < 32`; rejected counts exit with status 100.
Normal optimization stays enabled: constants fold, while input-dependent
addition chains, shared intermediates, constant-left addition, carry and monus
remain runtime computations. No argument-string access or parsing is needed.

Each backend compiles each case once and runs the same artifact with several
numbers of dummy arguments. Counts include the program name. Tests cover both
sides of the guard and arithmetic boundaries; the carry probe subtracts 255 from
`n + 250`, so an incorrect wrapped high byte cannot hide behind an eight-bit exit
status. They also check that the guard avoids runtime naturals and constant-only
multiplication disappears from machine IR.

The [6502 cost tests](../crates/mos6502-sim65/tests/expression_cost.rs) record image
size and cycle ceilings for the same corpus. These are whole-program costs,
including startup, argument-count acquisition, the guard and exit, not isolated
expression costs. Run the probes with
`nix develop --command cargo test --workspace guarded_argc_expressions`.

## Current target boundary

Unknown or overflowing bounds select machine IR's `Class::Natural`, never
silently `Word`. Large constants use `NaturalConstant` with compact magnitudes.
Finite bounds select `Fixed` widths; arithmetic must fit those widths. An exact
zero bound selects `Fixed { bits: 0 }`, whose only value is zero. It remains a
scalar in parameters, results and joins, not an erased unit or a license to drop
eager effects. Storage and ABI slots remain target decisions; a zero required
at a wider class is still valid. Explicit conversions, not natural arithmetic,
request truncation. Host arguments need a fit proof: passing a natural to an
effect does not request modulo conversion.

Multiplication, division, and remainder remain machine operations until target
selection. x86-64 and wasm32 use native unsigned instructions with zero-divisor
guards. The 6502 uses word-bit-bounded shift/add multiplication and restoring
division, not repeated addition/subtraction proportional to the operand value.
Monus retains its underflow guard.

Runtime `Natural` is supported on x86-64 Linux and wasm32 WASI through shared
runtime legalization. It uses exact byte-limb magnitudes and a reusable,
reference-counted private heap, **64 KiB by default**. Allocation or reference-count
exhaustion exits with **status 2**, never a wrapped or fabricated result. The heap
has fixed capacity; it does not grow through an OS allocator. AArch64 macOS is
currently limited to its syscall baselines, and native 6502 runtime naturals
remain disabled pending audited image/frame/hardware-stack capacity, even though
the shared runtime can be exercised by the 16-bit interpreter.

`Fixed` values wider than the target word are still rejected, even when a
`Natural` object could hold the magnitude. Native calling-convention and frame
limits also apply; runtime naturals do not remove them.

Use `Target::compile` (as the CLI does), or `Target::prepare` to inspect the
legalized, target-accepted IR. Raw `emit` requires already validated, accepted
scalar IR and does not legalize `Natural`. See [runtime naturals](../notes/runtime-naturals.md)
for configuration, ownership, and target limitations.

## Source-library representation boundary

Unused library types/functions do not require runtime representations: all three
files may be prepended to a Nat-only program. Pure compile-time `U8`/`Int` uses
work through folding and dead-binding cleanup. Representation checks follow the
code actually lowered, excluding impossible arms and tails after an exit.

Any remaining runtime `U8` or `Int` value is still rejected, not silently erased.
The definitions below do not add runtime product/sum packing or signed machine
lowering, nor do they make unbounded signed magnitudes fit a machine word.

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
