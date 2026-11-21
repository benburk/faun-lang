# Operators

This note owns Faun's operators: each one as a call of a named method on
its left operand, the four orderings read from one `cmp`, `&`, `|`, `^` and
`!` on `Bool` and on bits, the shifts `<<` and `>>`, the right side `&` and
`|` skip on `Bool`, and precedence, with what other languages do and the
designs considered. The members behind `==` and `<` are owned by
[methods](methods.md); `is` by [pattern matching](pattern-matching.md).

## Operators are methods

Every operator is a method of its left operand's type, found as a dot call
is, except that on `Bool`, `&` and `|` also choose whether their right side
runs (below):

| Written              | Calls                                 |
| -------------------- | ------------------------------------- |
| `a + b`, `a - b`     | `a.add(b)`, `a.sub(b)`                |
| `a * b`, `a / b`     | `a.mul(b)`, `a.div(b)`                |
| `a % b`              | `a.mod(b)`                            |
| `a == b`, `a != b`   | `a.equals(b)`, and its `not`          |
| `a < b` and the rest | `a.cmp(b)`, read as below             |
| `a & b`, `a \| b`    | `a.and(b)`, `a.or(b)`                 |
| `a ^ b`              | `a.xor(b)`                            |
| `a << b`, `a >> b`   | `a.shift_left(b)`, `a.shift_right(b)` |
| `-a`, `!a`           | `a.neg()`, `a.not()`                  |

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
precedence are fixed, and nothing else is symbolic. Rotations, powers and
conversions are named, `rotate_right`, `2.pow(n)`, `U64.of_nat(n)`. `Nat`,
`Int` and the words define the arithmetic; what `/` and `%` answer, by zero
among other cases, is owned by [numbers](../values/numbers.md).

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

## Shifts

`<<` and `>>` are `shift_left` and `shift_right`, on `Nat` and the unsigned
words. The count is a `Nat` whatever the word, so a numeral count is typed
from the method's parameter, `b << 3`, and a word count is converted,
`b << n.to_nat()`. `>>` brings in noughts from the top: there are no signed
words, and `Int` has no shifts. A word shifted by its width or more is
nought, `U8.of_nat(1) << 8 == 0`; a `Nat` has no width and grows,
`1 << 100`.

A shift binds tighter than a comparison, so `x << 3 == y` is
`(x << 3) == y`, and has no order with anything else that combines two
values: beside `+`, `-`, `*`, `/`, `%`, `&`, `|`, `^` or another shift it
takes parentheses, as bit-twiddling code is written anyway:

```ruby
field : U16 -> U16
field(op) -> (op >> 5) & U16.of_nat(7)

word : (U8, U8) -> U16
word(hi, lo) -> (U16.of_u8(hi) << 8) | U16.of_u8(lo)
```

Without them, `hi << 8 | lo` is refused at the second operator: "`<<` and
`|` need parentheses together: write `(hi << 8) | lo` or
`hi << (8 | lo)`". A shift does not chain: `x << a << b` is refused with
"`<<` does not chain: write `(x << a) << b`". The names stay, and
`x.shift_left(3)` is the same call as `x << 3`.

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
  `ok_or`, not `|`. A shift takes its type and a count of places,
  `(U8, Nat) -> U8`, and answers its type.
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

Loosest first; each level is left-associative, but for the shifts:

| Level | Operators                                          |
| ----- | -------------------------------------------------- |
| 1     | `\|`, and `^` (beside `&` or `\|`, parenthesized)  |
| 2     | `&`                                                |
| 3     | `is`                                               |
| 4     | `==`, `!=`, `<`, `<=`, `>`, `>=`                   |
| 5     | `<<`, `>>` (beside 1, 2, 5, 6 or 7, parenthesized) |
| 6     | `+`, `-`                                           |
| 7     | `*`, `/`, `%`                                      |
| 8     | prefix `-` and `!`                                 |
| 9     | calls, `.member`, `?`                              |

So `True | False & False` is `True | (False & False)`, and `!!True` is
`!(!True)`. `^` is at `|`'s level against everything but `&` and `|`:
`x == 1 ^ y == 2` is `(x == 1) ^ (y == 2)`. Beside `&` or `|`, as
`a ^ b & c`, `a & b ^ c`, `a ^ b | c` or `a | b ^ c`, it is refused at the
second operator, which offers both groupings, `(a ^ b) & c` and
`a ^ (b & c)`. A shift is ordered only against comparisons and what binds
tighter: `x << 3 == y` is `(x << 3) == y`, and `-x << 3` is `(-x) << 3`.
Beside arithmetic, `&`, `|`, `^` or another shift, as `x << 3 + 1`,
`x + 1 << 3` or `x << 3 | y`, it is refused at the second operator, which
offers both groupings, and `x << a << b` is refused as a chain. A
comparison between orders both: `a & x << 3 == y` is
`a & ((x << 3) == y)`. A prefix takes the whole call after it:
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
and `&&` and `||` would be second spellings of the same call. A second
symbol would not settle the mask either: C has both `&` and `&&`, and
still reads `x & 2 == 2` as `x & (2 == 2)`. On `Bool`, `&` already does
what Python's `and` keyword does, working out its right side only where
the left has not decided the answer. Word
operators, `and` and `or`, which would leave `|` to patterns, were
considered with conditions and declined: every `Bool` expression
would change.

### Why this precedence?

Faun wants as little syntax as it can have, and rules a reader can apply
the same way every time, or work out in their head without a table. For
precedence that means two things: every grouping the language makes for
you should be one most programmers already make, and where programmers
genuinely disagree, the language should ask rather than guess. A third
wish pulls against the second: a line should not be so noisy with
parentheses that it stops reading like the condition it is.

So the order is derivable: arithmetic as at school, then compare, then
combine, and "and" before "or" as in Boolean algebra. What is left to
remember is that `^` and the shifts have no place among the combining
operators and arithmetic, and the compiler says so when it matters. Every
grouping the language makes for you is one the languages around it make
too, and those they disagree on are the ones it refuses.

It keeps lines quiet where they are most common. Conditions join
comparisons far more often than code masks bits, and they need no
parentheses. A mask needs them, `(flags & 4) == 0`, and forgetting them is
a type error that names the fix rather than a program that runs wrong.

The table stays short because only what is written often is symbolic, and
`&`, `|` and `^` are each one method, `and`, `or` and `xor`, on whatever
type their left operand has: on `Bool` they are logic, on a word they are
bits, and the symbol means the same call either way. Rotations, powers and
conversions are named methods, and a call binds tightest, so none of them
has a place in it.

### What do other languages do?

| Language    | Bits vs `==` | `&` vs `\|` | `^`       | Shifts    | Mixing  |
| ----------- | ------------ | ----------- | --------- | --------- | ------- |
| C, Java, JS | looser       | `&` first   | between   | under `+` | warned  |
| Rust        | tighter      | `&` first   | between   | under `+` | allowed |
| Go          | tighter      | `&` first   | with `\|` | with `*`  | allowed |
| Python      | tighter      | `&` first   | between   | under `+` | allowed |
| Swift       | tighter      | `&` first   | with `\|` | over `*`  | allowed |
| Gleam, Roc  | none         |             |           | named     | named   |
| Carbon      | ordered      | refused     | refused   | unordered | partial |
| Pony, Pyret | none         | refused     | refused   | refused   | refused |

"Between" is between `&` and `|`. "Looser" means `a & b == c` is
`a & (b == c)`; "tighter", `(a & b) == c`. "Under `+`" is looser than `+`
and `-` and tighter than `&`, as C, C++, C#, Java, JavaScript, Rust and
Python all have it. C and C++ compilers allow every mix and warn on some
under `-Wall`; Carbon refuses a pair its partial order leaves unordered;
Pony and Pyret refuse any two different operators side by side.

Four things stand out. Languages agree that `&` binds before `|`, the
order Boolean algebra gives "and" and "or". They agree that a shift binds
tighter than a comparison. They disagree about `^`: `a | b ^ c` means one
thing in C and another in Go; and about shifts against arithmetic:
`1 << n - 1` is `1 << (n - 1)` in C and `(1 << n) - 1` in Go. And the C
trap, `flags & 4 == 0` meaning `flags & (4 == 0)`, is common enough that
GCC and Clang warn on it under `-Wall`, as they warn on `&&` inside `||`,
and that Carbon's
[precedence proposal](https://docs.carbon-lang.dev/proposals/p000555-operator-precedence.html)
names both as rules developers do not reliably remember. Carbon's answer is
a partial order: a rule only where "most or all developers" would
reliably remember it, and otherwise none, so the expression is refused;
when in doubt, leave the rule out, since one can be added later and not
easily taken away.

### What else was considered?

Counted over the repository's Faun code when the order of `&`, `|` and `^`
was decided: about 450 lines join comparisons with `&` or `|`, about 75 use
`&`, `|` or `^` on bits, 17 mix `&` with `|`, and none mixes `^` with
either.

- **C's order, as it was.** Bits looser than comparisons, `&` before `^`
  before `|`. A mask written without parentheses is a type error with a
  hint, not a silent wrong answer, which is better than C. But the order of
  `^` is one nobody remembers.
- **`&` and `|` for `Bool` only, bits as named methods**, as Gleam and Roc
  have no bit operators at all. It removes the mask trap outright and
  matches the shifts, which were then methods too. Declined: `&` would stop
  being plain sugar for `.and()` on every type, an exception to a rule
  that otherwise has none.
- **A separate spelling for logic**, `&&` and `||` as in Rust or `and` and
  `or` as in Python, with the bit operators tighter than comparisons.
  Masks read naturally. Declined: a second spelling of one method, and
  every condition rewritten.
- **Every mix parenthesized**, as Pony and Pyret do. One rule with no
  table. Declined: `i * 4 + 3 < len` would become `((i * 4) + 3) < len`,
  noise for groupings nobody misreads.
- **A partial order with `&`, `|` and `^` unordered against comparisons.**
  The mask trap could not be written. Declined: since one `&` means both
  logic and bits, and the parser cannot tell which before types are
  known, every joined condition would need parentheses,
  `(x == 3) & (y == 5)`, about 270 lines.
- **Compare, then combine, with `&`, `|` and `^` unordered among
  themselves.** Carbon's design read onto Faun, whose `&` and `|` are its
  `and` and `or`. Built first, then relaxed: and-before-or is the one
  ordering among the three that languages agree on, and refusing it buys
  little, while a line such as MD5's `b & c | !b & d` reads naturally to
  anyone who knows it.
- **Compare, then combine; and before or; `^` unordered with both.** The
  order kept, to which the shifts were later added, ordered only against
  comparisons.

### What does the precedence risk?

It leaves three groupings to the reader that a stricter rule would ask
about:

- **And and or mixed in a condition.** `x == 0 | y == 1 & z == 2` is
  `x == 0 | (y == 1 & z == 2)`. That is the order Boolean algebra gives,
  but it is the mix GCC warns about, because someone sometimes means the
  other. Faun chose quiet lines over that warning.
- **A comparison of Booleans beside `&`, `|` or `^`.** Where every operand
  is a `Bool`, `a & b == c` is `a & (b == c)` and checks. It follows the
  rule, and comparing two Booleans with `==` is rare, but nothing flags it.
- **A shift inside a comparison beside `&`, `|` or `^`.** `a & x << 3 == y`
  is `a & ((x << 3) == y)`, each pair ordered, and so is
  `a == x << 3 & y`. A reader from Go, whose `&` and `<<` share a level
  above `==`, reads both otherwise; on numbers the type of `and` refuses
  them, with the parenthesized form as help, but on `Bool` the first
  checks.

A [linter](../lints.md) could flag them without the language refusing
them. The tree-sitter grammar keeps an order for `^` and the shifts, C's,
and accepts them mixed, so an editor does not underline them; the compiler
refuses them.

### Where are parentheses asked for, and where do types answer?

A grouping can go wrong in two ways. Where one reading fails to check, the
type checker already settles it: `x & 2 == 2` hands a number and a `Bool`
to one `and`, so it is refused with the parenthesized form as help, as
Java and C# refuse it, and no parenthesis rule is needed. Where both
readings check, nothing settles it but the text. `1 << n - 1` is a number
either way, `1 << (n - 1)` in C and `(1 << n) - 1` in Go, and `a ^ b & c`
on words is a word either way. Those are the places Faun asks, and the
only ones.

So most lines need no parentheses at all. Rounding half to even in the
standard library reads the same with or without them:

```ruby ignore
up = (dropped > half) | ((dropped == half) & (kept % 2 == 1))
up = dropped > half | dropped == half & kept % 2 == 1
```

and the lines that need them are the ones a reader would otherwise have to
stop at:

```ruby ignore
seen = if (bits & U64.of_nat(0x7fffffffffffffff)) > U64.of_nat(0x7ff0000000000000)
mix(b, c, d, i) -> (c ^ (b | !d), 7 * i % 16)
opcode = (byte >> 5) & 7
address = (hi << 8) | lo
```

A common way to say what precedence should be is by type: operations from
numbers to numbers first, then from numbers to `Bool`, then from `Bool` to
`Bool`. Faun's table is that order, with one exception it chooses: `&`,
`|` and `^` are one symbol each for bits and logic, so on numbers they sit
in the `Bool`-to-`Bool` place, and a mask needs its parentheses. The type
checker refuses the mask written without them.

### Who are the parentheses for?

For the reader. A writer who knows a rule can apply it, and one who does
not can add parentheses; the reader of someone else's code can do neither.
The reader is often not a beginner. It is anyone reading code in a
language other than the one they use most, which for most programmers is
often: reviewing a change, porting from C or Go, skimming a library. An
expert who has the rule right in one language has it wrong in the next,
and GCC and Clang warn on these groupings under `-Wall` because experts
get them wrong. Faun spends a pair of parentheses where two common
languages disagree and the types cannot tell, and nowhere else.

### Why not take the reading that checks?

Where only one grouping checks, the compiler could take it, and the
programmer would never see an error. Faun does not, because that makes
the parse depend on types. A reader could not see an expression's shape
without knowing every operand's type; a change of type elsewhere, a `Bool`
becoming a `U8`, could regroup an expression with no error; and editors,
formatters and highlighters could not parse a line without running the
type checker. The grouping is read from the text, and where the text
leaves it open the compiler says so.

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

### Why are `<<` and `>>` operators, and why do they take parentheses?

Because bit-heavy code reads like the references it is written from. An
emulator decodes `(op >> 5) & 7` and joins `(hi << 8) | lo`, as the
hardware manual and the C beside it write them, and
`op.shift_right(5) & 7` and `hi.shift_left(8) | lo` make the reader
translate each one. The cost of two more symbols in a closed table is
small, and they keep the rule that an operator is a method: `x << 3` is
`x.shift_left(3)`, and both spellings stay.

Where a shift binds, languages disagree. C, C++, C#, Java, JavaScript, Rust
and Python put shifts looser than `+` and `-` and tighter than comparisons
and than `&`, `^` and `|`. Go puts them at the multiplication level, so
`1 << n - 1` is `(1 << n) - 1` there and `1 << (n - 1)` in C. Swift binds
them tighter than multiplication. Carbon leaves them unordered with
arithmetic. All agree that a shift binds tighter than a comparison. So by
the principle that took `^` out of order with `&` and `|`, a shift is
ordered only against comparisons, and against what binds tighter than
every operator, calls and prefixes. Beside arithmetic, `&`, `|` or `^` it
takes parentheses, which bit-twiddling code mostly writes anyway, and
`x << a << b` does not chain, as in Carbon: a chain is rare, and each
reading of it is easy to write. A comparison between orders both sides,
since every language puts the shift inside it.

The count is a `Nat`: a count of places, never negative and with no
width. `x << 3` types its `3` from the method's parameter, as any numeral
argument is typed, so a literal count costs nothing, and a count held as
a `Nat` costs nothing at run time either, since range analysis keeps a
bounded `Nat` a word. A count of a word type would ask which word, and
would have to wrap or refuse.

Only `Nat` and the unsigned words shift, so `>>` is always a logical
shift and there is no `>>>`: a sign to carry would need a signed word,
which Faun does not have, and `Int` has no bitwise operations, since a
two's complement bit pattern is not its value. A shift by the width or
more is nought, as the bits shifted out are gone, where C leaves it
undefined and x86 shifts by the count modulo the width.

The cost is parentheses in `x << 3 | y`, which C reads without them, and
in `1 << n - 1`, which Faun reads neither way; the refusal names both
groupings.

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

- **2026-11-21:** `<<` and `>>` became operators, `shift_left` and
  `shift_right` as every operator is a method, on `Nat` and the unsigned
  words. A shift binds tighter than a comparison and has no order with
  arithmetic, `&`, `|`, `^` or another shift: beside any of them it is
  refused without parentheses, and it does not chain. No program changed;
  the named calls stay. The operator precedence note, with what other
  languages do and the designs considered, was merged into this one.
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
- [Syntax](syntax.md): the grammar's goals
- [Lints](../lints.md): what a linter should flag and the compiler leaves
  alone
- [Carbon: operator precedence](https://docs.carbon-lang.dev/proposals/p000555-operator-precedence.html)
- [Pony: operator precedence](https://tutorial.ponylang.io/expressions/ops)
