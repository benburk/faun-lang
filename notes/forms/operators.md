# Operators

This note owns Faun's operators: each one as a call of a named method on
its left operand, the four orderings read from one `cmp`, `&`, `|`, `^` and
`!` on `Bool` and on bits, the right side `&` and `|` skip on `Bool`, and
precedence. The members behind `==` and `<` are owned by
[methods](methods.md); `is` by [pattern matching](pattern-matching.md).

## Operators are methods

Every operator is a method of its left operand's type, found as a dot call
is, except that on `Bool`, `&` and `|` also choose whether their right side
runs (below):

| Written              | Calls                        |
| -------------------- | ---------------------------- |
| `a + b`, `a - b`     | `a.add(b)`, `a.sub(b)`       |
| `a * b`, `a / b`     | `a.mul(b)`, `a.div(b)`       |
| `a % b`              | `a.mod(b)`                   |
| `a == b`, `a != b`   | `a.equals(b)`, and its `not` |
| `a < b` and the rest | `a.cmp(b)`, read as below    |
| `a & b`, `a \| b`    | `a.and(b)`, `a.or(b)`        |
| `a ^ b`              | `a.xor(b)`                   |
| `-a`, `!a`           | `a.neg()`, `a.not()`         |

A type gets an operator by having the method, and generic code asks for it
by a `where` bound on the same member:

```ruby
Money : [Cents(Int)].(
  add : (Money, Money) -> Money
  add(Cents(a), Cents(b)) -> Cents(a + b)

  neg : Money -> Money
  neg(Cents(a)) -> Cents(-a)

  cmp : (Money, Money) -> Order
  cmp(Cents(a), Cents(b)) -> a.cmp(b)
)

total : List(a) -> a where a.zero : a, a.add : (a, a) -> a
total(xs) -> xs.fold(a.zero, |sum, x| sum + x)

expect Cents(5) + Cents(7) == Cents(12)
expect -Cents(5) < Cents(0)
expect total([1, 2, 3]) == 6
```

There is no operator declaration: the set of operators and their
precedence are fixed, and nothing else is symbolic. Shifts and rotations are
named, `shift_left`, `rotate_right`, and the rest. `Nat`, `Int` and the
words define the arithmetic; what `/` and `%` answer, by zero among other
cases, is owned by [numbers](../values/numbers.md).

## Orderings

A type is ordered by one `cmp : (T, T) -> Order`, `Order` being
`[Lt, Eq, Gt]`. The four orderings are fixed views of its answer:

| Operator | Holds where `cmp` answers |
| -------- | ------------------------- |
| `<`      | `Lt`                      |
| `<=`     | `Lt` or `Eq`              |
| `>`      | `Gt`                      |
| `>=`     | `Gt` or `Eq`              |

No type defines `<` itself, and a type with no `cmp` has none:
`Small < Large` on a `Size` without one says "`Size` has no field or method
`cmp`". `Order`'s own `lt`, `le`, `gt`, `ge`, `eq` and `ne` are the same
views, for code holding an `Order`. On orders, `|` is `Order.or`: the first
order, or the second where the first is `Eq`, which chains a comparison
field by field, `a.major.cmp(b.major) | a.minor.cmp(b.minor)`.

## `&`, `|`, `^` and `!`

`&`, `|` and `^` are `and`, `or` and `xor`: logical on `Bool`, bitwise on
`Nat` and the words. `!` is `not`, logical on `Bool` and every bit flipped
on a word. `Int` has no bitwise operations. `|` also keeps the first that
did not give up: on `Order`, the first that is not `Eq`, so
`a.x.cmp(b.x) | a.y.cmp(b.y)` orders by `x` and then `y`; on `Result`, the
first that is `Ok`, so `(parse(a) | parse(b))` tries each in turn. They sit looser than the
comparisons, so a condition reads without parentheses and a mask needs
them:

```ruby
flags : (Nat, Nat) -> Bool
flags(x, y) -> x == 3 & y == 5

masked : U8 -> Bool
masked(b) -> (b & U8.of_nat(8)) == U8.of_nat(8)
```

Without the parentheses, `b & U8.of_nat(8) == U8.of_nat(8)` is
`b & (… == …)`, a `U8` and a `Bool`, and is refused: "argument 1 of `and`
should be `U8`, but is `Bool`".

`&` binds before `|`, so `b & c | !b & d` is `(b & c) | (!b & d)`. `^`
has no order with either: beside `&` or `|` it takes parentheses, and
`a ^ b & c` is refused as it is read, "`^` and `&` need parentheses
together: write `(a ^ b) & c` or `a ^ (b & c)`". It chains with itself,
`a ^ b ^ c`, read left first.

### On `Bool`, the right side waits

On `Bool`, `&` and `|` work out their right side only where the left has
not decided the answer. This is promised:

```ruby
odd : Nat -> Bool
odd(n) -> n != 0 & !odd(n - 1)
```

stops at nought, and `1 == 1 | spin(0)` answers `True` even where `spin`
never comes back. The compiler makes the operator a match on the left
side, with the right side only in the arm that needs it. The method call
`a.or(b)` is not the operator: it is an ordinary call, and works out both
arguments first, as every call does.

Three rules follow from the right side perhaps not running. `?` on the
right of `&` or `|` is refused, since it would leave from a side that may
not be worked out; `=` binds no name of the body there; and a name a test
on the left binds is seen on the right, along an `&`, only because the
right runs only where the test held: `r is Ok(v) & v < 100`.

For any other type an operator's right side is an argument like any other.
Where the method reads it on some paths only, the optimizer may leave it
unworked on the others, as `Order.or` reads its second order only on a tie,
but that is not promised.

## What an operator should mean

An operator is a method, and a method may take and answer any types, so the
language asks nothing more of one: `price * 3` may call
`mul : (Money, Int) -> Money`. What a reader expects of a symbol is more,
and a type's operators keep to it by convention:

- **One obvious meaning.** Define an operator only where it has one meaning
  nobody would mistake, and give anything less certain a name. A type has
  one `sub`, so where two subtractions are both natural, the difference of
  two instants and an instant moved back by a duration, neither is `-`:
  they are `later.since(earlier)` and `instant.minus(duration)`.
- **Closed, by default.** `+`, `-`, `*`, `/`, `%`, `&`, `|` and `^` take
  two of a type and answer that type, as numbers do, `Order.or` does and
  `Result.or` does. A fallback that answers a different type is a method,
  `ok_or`, not `|`.
- **The most natural partner, where not closed.** A quantity is scaled by a
  plain number, `Money * Nat -> Money`, since `Money * Money` means nothing;
  an offset moves a point, `Instant + Duration -> Instant`. Pick the one
  pairing the type is used with, and name the rest.
- **The laws its symbol suggests.** `+` and `*` associate, `+` commutes, a
  zero adds nothing and a one multiplies by nothing, `&` and `|` associate,
  and `a == b` holds exactly where `a.cmp(b)` is `Eq`. None is checked, as
  `cmp`'s are not, and an `expect`, or a property test over many values,
  is how a type shows it keeps them.

## Precedence

Loosest first; each level is left-associative:

| Level | Operators                                         |
| ----- | ------------------------------------------------- |
| 1     | `\|`, and `^` (beside `&` or `\|`, parenthesized) |
| 2     | `&`                                               |
| 3     | `is`                                              |
| 4     | `==`, `!=`, `<`, `<=`, `>`, `>=`                  |
| 5     | `+`, `-`                                          |
| 6     | `*`, `/`, `%`                                     |
| 7     | prefix `-` and `!`                                |
| 8     | calls, `.member`, `?`                             |

So `True | False & False` is `True | (False & False)`, and `!!True` is
`!(!True)`. `^` is at `|`'s level against everything but `&` and `|`:
`x == 1 ^ y == 2` is `(x == 1) ^ (y == 2)`. Beside `&` or `|`, as
`a ^ b & c`, `a & b ^ c`, `a ^ b | c` or `a | b ^ c`, it is refused at the
second operator, which offers both groupings, `(a ^ b) & c` and
`a ^ (b & c)`. A prefix takes the whole call after it:
`-x.abs()` is `-(x.abs())`; where that fails to check, the compiler's help
offers `(-x).abs()`. A test tested again or compared,
`x is A is B` or `x is 3 == y`, is refused. A line beginning with an infix
operator goes on with the line before, so a long condition may break before
its `&`.

## Rationale

### Why are operators method calls?

So that an operator means one inspectable definition. `a + b` is the `add`
in `a`'s type's block and nothing else: no overload set, no operator
declaration, and no instance to register. The right operand is whatever
that method takes, so a `Money` with `mul : (Money, Int) -> Money` may be
written `price * 3`. A type gains `+` by defining `add`, and a generic
definition asks for `+` by the same `where` bound it would write for a call
of `add`. The tower is closed, so a reader never meets a new symbol or a
new precedence level in someone's library.

The cost is a small fixed table to learn, and no way to give a symbol to an
operation the table lacks, such as a dot product. That is a named method.

### Why do the four orderings come from one `cmp`?

An order is one fact. Four functions answering `Bool` are four views of it
that nothing stops from disagreeing, with `a < b` and `a > b` both true.
Reading all four from one `Order` makes that unwritable: they read the same
value, and exactly one of `Lt`, `Eq` and `Gt` holds because `Order` has
three constructors. A type writes one definition rather than four, generic
code asks one bound rather than four, and a sort or a merge needing all
three outcomes asks once.

The cost: `Order` is a total order. A partial order, such as sets under
inclusion, has no `cmp` and so no `<`, and uses named methods. One `cmp`
also does not make an order lawful: that it is transitive, or that
`a.cmp(a)` is `Eq`, is still the author's to get right.

### Why does one `&` serve logic and bits?

On `Bool`, logical and is bitwise and on a single bit, so the two are one
operation. Faun has one method per type, `and`, so one symbol is enough,
and `&&` and `||` would be second spellings of the same call. Word
operators, `and` and `or`, which would leave `|` to patterns, were
considered with conditions and declined: every `Bool` expression
would change.

### Why do `&`, `|` and `^` sit looser than comparisons?

Because combining comparisons is what conditions do: `x == 3 & y == 5` and
`n == 0 | odd(n - 1)` need no parentheses. C puts its bitwise operators
at the same place, and the cost is the one C has, that a mask test needs
parentheses, `(b & mask) == mask`. In C the unparenthesized form compiles
and does the wrong thing; in Faun it is a `U8` and a `Bool` handed to one
`and`, which is a type error. The error is a type's, at the operand, so it
says what the precedence is and what to write:

```text
error: mismatched types
 --> flate.fn:3:30
  |
3 | compressed(flags) -> flags & 4 == 0
  |                      -----   ^^^^^^ expected `Nat`, found `Bool`
  |                      |
  |                      expected because this is `Nat`
  |
  = help: `&` binds looser than `==`: write `(flags & 4) == 0`
```

and the same for `|` and `^`, and for a comparison on the left,
`0 == flags & 4`, which is `(0 == flags) & 4`.

The alternative is Rust's: the bit operators on a level of their own above
comparison, `+` and `-` < `&` < `^` < `|` < `==`, with `&` on `Bool` then
binding tighter than `==` too. A mask test would need no parentheses, but
`a == 1 & b == 2` would read `(a == (1 & b)) == 2`, a type error, so
every condition joining comparisons would need them instead:
conditions are written far more often than masks. Splitting the symbol,
`&&` for `Bool` loose and `&` for bits tight, would answer both at the cost
of a second spelling of one method, which the previous answer declines.
The inflate that met the trap wrote ten mask tests unparenthesized before
parenthesizing all of them; with the help, each costs one reading of a
refusal rather than a search.

### Why has `^` no order with `&` and `|`?

Because languages disagree on it, while they agree on the rest. C, Rust, Go
and Python all bind and before or, as Boolean algebra writes products
before sums, so `a & b | c` is `(a & b) | c` in each and in Faun. Where `^`
goes they do not agree: C, Rust and Python put it between `&` and `|`, Go
at `|`'s level, beside `+`. So `a | b ^ c` is `a | (b ^ c)` to a reader
from C and `(a | b) ^ c` to a reader from Go, and neither is wrong about
their language. So Faun refuses it rather than guess, and the parentheses
say which is meant. This is Carbon's rule, "if in doubt, leave it out": an
operator pair whose order a reader may doubt has none, and takes
parentheses.

The cost is parentheses where `^` meets `&` or `|`, as in a hash that
masks a mixture, `(a ^ b) & mask`, which is where C's order once let one
through unmasked (in the [compression note](../compression.md)). `^` with
itself, `a ^ b ^ c`, needs none, since `xor` associates, and against
comparisons and arithmetic it stands where `|` does.

### Why do `&` and `|` on `Bool` skip their right side?

Conditions are written to rely on it. A recursion's base case is the left
side, `n == 0 | odd(n - 1)`, and a test on the left binds names the right
side reads, `xs.first() is Ok(x) & x > 10`, where the right side has no
`x` to read unless the test held. Without the promise, every such line
would be an `if` or a guard. The cost is that `&` and `|` on `Bool` are the
one place an operator is not an ordinary call, which is why `?` on their
right is refused.

### Why may an operator's operands differ in type?

Because an operator is a method, and a method's types are its own: a rule
that `+` must be `(T, T) -> T` would make the operator table the one place
a method's signature is not its author's to choose. The few useful
exceptions, scaling a quantity and moving a point by an offset, would then
need names for operations everyone writes with a symbol. What makes
overloading in other languages hard to read is several definitions of one
operator chosen by argument types, which Faun does not have: a type has one
`mul`, found from the left operand alone, so `a * b` always means one
definition a reader can find. The expectations above are conventions
because they are judgements, whether a meaning is obvious or a partner
natural, that a compiler cannot make.

The cost is that nothing stops an odd operator, and that `price * 3` does
not make `3 * price` work: that is `Int`'s `mul`, which takes no `Money`.
A lint flagging an operator that is neither closed nor one of the familiar
pairings is an open question.

### Why may no program define operators?

A program reads the same whatever it imports: the symbols, their meaning
as method names, and their precedence are fixed by the language. Haskell's
and Scala's user operators trade that away for libraries that read like
their domain. Faun keeps the trade the other way; a named method says what
it does.

## History

- **2026-11-20:** `^` lost its place between `|` and `&`: beside either
  it is refused without parentheses, and against everything else it
  stands at `|`'s level, chaining with itself. `&` before `|` is kept. No
  program mixed them.
- **2026-11-17:** a type error at the operand of `&`, `|` or `^` whose
  other side, or whose right, is a comparison written without parentheses
  came to say the precedence and the parenthesized form, after inflate met
  "expected `Nat`, found `Bool`" at `header & 1 == 1`. The precedence
  itself is unchanged; Rust's, above, is the alternative.

## Related

- [Methods](methods.md): `equals` and `cmp`, derived or written, and why a
  type has at most one
- [Pattern matching](pattern-matching.md): `is`, and the names a test binds
  along `&`
- [Numbers](../values/numbers.md): arithmetic, words, and division by zero
- [Floats](../values/floats.md): a total `cmp`, and IEEE 754's comparisons
  by name
- [Types](../types.md): `where` bounds, which ask for an operator's method
- [Pattern matching](pattern-matching.md): `if`, `is`, and `&` and `|`
  binding along a condition
