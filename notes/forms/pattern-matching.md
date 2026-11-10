# Pattern matching

This note owns taking values apart: the patterns themselves, where they
stand, the `is` test and its arms, the leaving lines that go with them, what
the compiler checks a group of clauses or arms to cover, and how a name in a
pattern binds. The long exploration that led here is
[pattern matching](pattern-matching-domain.md); the decided designs are the
[conditions](../proposals/approved/conditions.md),
[blocks](../proposals/approved/blocks.md) and
[loops](../proposals/approved/loops.md) proposals.

## Where a pattern stands

- **A clause's parameters,** with an optional guard, `if condition`. A
  clause whose patterns or guard fail falls to the next clause.
- **A test,** `value is pattern`, a `Bool`, and **arms,** `value is ( … )`,
  which answer by the first arm that matches.
- **A binding, a lambda's parameters and a `for`'s element.** These cannot
  fail, so their pattern must match whatever it is handed: names, records,
  tuples, and the constructor of a type that has no other.

```ruby
describe : Result(Nat, [Missing]) -> Str
describe(Ok(v)) if v > 100 -> "large"
describe(Ok(_)) -> "small"
describe(Err(Missing)) -> "missing"
```

## What a pattern may be

| Form               | Example                  | Notes                      |
| ------------------ | ------------------------ | -------------------------- |
| Name, wildcard     | `x`, `_`                 | a name always binds        |
| Constructor        | `Ok(v)`, `Order.Lt`      | qualified where ambiguous  |
| Numeral, character | `0`, `-1`, `'a'`         | a test but on `Nat`, `Int` |
| String             | `"get"`                  | a test                     |
| Range              | `0..9`, `_..-1`          | inclusive; a test          |
| List               | `[a, b, *rest]`, `[]`    | the rest may go unnamed    |
| List's end         | `[*init, last]`          | clauses only               |
| Record, tuple      | `{x, y: p, *}`, `(a, b)` | `*` leaves other fields    |
| Alternatives       | `Circle(n) \| Square(n)` | same names, same types     |
| Whole and parts    | `right is [y, *_]`       | binds the whole as `right` |
| Equal to a name    | `Ok(==node)`             | a part, outside any `\|`   |
| A name twice       | `[a, a, *_]`             | asks the two parts equal   |

The ranges are described in full in the standard README's Ranges section.

## Tests and arms

`value is pattern` answers whether the value has the pattern's shape. What
it binds is seen only where the test is known to have held: along the rest
of an `&` chain, in the `then` of an `if`, in a clause's body from its
guard, and on the lines below an `else` line. Past `|`, a name both sides
bind is seen; one only a side binds, or one under `!`, is not, and a use
there is refused, naming what hid it.

```ruby
doubled(r) -> if r is Ok(v) & v < 100 then v * 2 else 0
```

Alternatives after `is` are parenthesized, `x is (A | B)`, since `|` is
also the `Bool` or. Several values are tested at once as a tuple, `(a, b)
is (Ok(x), Ok(y))`.

Arms answer by the first arm, a line apiece, whose pattern matches and
whose guard holds. An arm's value follows `then`, or a leave stands in its
place: `P return value`, `P continue`, `P break`.

```ruby
area(shape) -> shape is (
  Circle(r) then 3 * r * r
  Rect(w, h) then w * h
  Dot then 0
)
```

Clauses suit a body that is the dispatch; arms suit a value worked out
partway through one; the ternary suits a choice of two values. Which to
write where is a [lint's](../lints.md) concern, not the compiler's.

## Leaving lines

A block's line `condition else return value` goes on where the condition
holds, its names seen below, and leaves the clause where it fails. A line
`if condition return value` leaves where the condition holds. `continue`
and `break` leave the same way inside loops. `return`, `continue` and
`break` stand nowhere else, so every way out of a body is a line saying
one.

```ruby
first_over(xs, k) -> (
  if k == 0 return 0
  xs is [x, *_] else return 0
  x / k
)
```

## Coverage

A definition's clauses, and the arms of an `is`, must cover every value
they take apart. A clause or arm with a guard covers nothing, since the
guard may fail; so does any pattern that is a test of equality or order:
a range, a string, a numeral of anything but `Nat` or `Int`, and a name
written twice. A list's end that tests its elements, `[*rest, Leave(n)]`,
covers where every list pattern beside it reads the same from the end, as
`[]`, `[a, b]` and `[*_, x]` do: those are judged as the list turned round.
Beside a front that tests, `[Enter(n), *rest]`, it covers nothing. A
missing case is refused with a witness:

```text
error: this `is` does not cover every case
  |
6 | area(shape) -> shape is (
  |                ^^^^^ no arm matches `Square(_)`
  |
  = help: add an arm matching `Square(_)`, or `_ then …` for the rest
```

A numeral on `Nat` stands for its constructors, so `0` and `Succ(n)` cover a
`Nat`; numerals alone never do. Clauses, or an `is`'s arms, that take a tag row
apart with no catch-all close it, so a caller cannot hand them a tag nothing
matches. An `if … is … then … else` closes nothing, since its `else` takes
everything the test does not match.

## Comparing in a pattern

A name in a pattern always binds. To compare with a name from outside the
pattern, write `==name`; to ask two parts of one pattern equal, write the
name twice. Both are asked by the type's `equals`, after the rest of the
pattern has matched and before the guard.

```ruby
found(r, node) -> r is Ok(==node)

strip_prefix([byte, *rest], [byte, *prefix]) -> strip_prefix(rest, prefix)

merge([x, *xs], right is [y, *_]) if x <= y -> [x, *merge(xs, right)]
```

`==name` compares a part, never a test's whole pattern, which is `x == y`.
`[a, ==a]` is refused: `==` reads as reaching outside the pattern.

## Binding again

`=` binds a name from that line on, whether or not it was bound before, as
Python's does: past the branch it was bound in and into a loop's next round.
On a straight line the name may change type; where paths meet it has one
type, if anything reads it there. A test's or an arm's pattern binds a name
in scope again the same way, where it matched. A lambda's parameters shadow
names around it within the lambda.

```ruby
capped(limit, r) -> (
  r is Ok(limit) else return 0
  limit
)
```

## Rationale

### Why `is` and no `match` or `when`?

One operator asks one question, whether a value has a shape, at every
arity. `r is Ok(v)` is the test; `r is ( … )` with arms is the many-way
match. A test grows into arms without changing keyword, and the language
spends no keyword on a second spelling of "matches". The form still says
whether coverage is checked: the parentheses and `then` arms are, a bare
test in a condition is not.

Ori kept `when` beside `if … is` so that the keyword told a reader the
checker would break this code when the type grew. Faun keeps that signal in
the shape of the form instead. The cost is the parentheses around
alternatives, `x is (A | B)`, since `|` is also the `Bool` or.

### Why do tests bind names along `&`?

So a body can test a value it computed and go on with what it found,
without a helper. Before tests, the heap and graph libraries carried
helpers such as `visiting`, `drained`, `stepped` and `climb_past` that
existed only to take apart one computed value, each with a made-up name and
a signature longer than its body. Ori's own code showed the same pressure:
an arm whose body at once matched another computed value appeared 72
times, mostly two-way steps in parsers.

A name is seen only where its test is known to have held, which `&`
working out its right side only where the left held makes sound. The cost
is flow-sensitive scope: where a name is seen depends on `&` and `else`
lines, not only on blocks. A use where it is hidden is refused with the
reason.

### Why leaving lines instead of nesting?

An early exit closes a case: once `popped is Ok(…) else return state` has
run, nothing below thinks about an empty heap, where a nested branch holds
the case open to the end of its `else`. Dijkstra's `back` became three flat
lines. The two lines do two jobs: an `else` line passes names down, an `if`
line bails out on a case, and neither is negated to fit the other.

The cost is that the leave is at the line's end. `return`, `continue` and
`break` stand only in a leaving line or an arm, so a search for them finds
every exit.

### Why not `let … else`, as Rust has?

`Ok(v) = x else return 0` puts the pattern first where every other test
puts the value first. In Faun the order says whether a line can fail: `P =
expr` cannot, `expr is P` can, and a binding whose pattern can fail is
refused with advice to write the test.

### Why don't guards count toward coverage?

A guard is any `Bool`, and no checker can say which values an arbitrary
predicate admits. Leaving guards out keeps coverage decidable, quick
(Maranget's usefulness algorithm), and able to name a missing value. The
same holds for every pattern that is really a test: a range is two
comparisons, a string or a word's numeral is `equals`.

The cost is a final unguarded clause even where the guards plainly tile the
values, as `n < 10` and `n >= 10` do. The recourse is to say the shape in
the pattern rather than the guard: what a pattern says, the checker checks.

### Why is a missing case still an error, now that termination is not checked?

Ori refused a missing case because a match that can get stuck is a partial
function, and Ori had none. Faun gave up proving that calls come back; it
did not give up saying what every match does.

- **There is nowhere for a missed value to go.** Faun has no exceptions,
  and a Barb match has an arm for every constructor with no
  default. Accepting a missing case would mean inventing a trap that every
  target answers with some exit status: hidden control flow, which Faun
  has none of.
- **The check is cheap and certain.** Proving termination was slow and
  fragile, and refused good programs; coverage is decidable, local to one
  group of clauses, and its diagnostic names the value missed.
- **It is the alarm when a type grows.** A constructor added later breaks
  every match that does not handle it. A `_` opts out, and says so.
- **Rows depend on it.** Clauses or arms with no catch-all close a tag row, so
  callers may not pass them a tag nothing matches.

The cost is writing a case that cannot happen. The recourse is a type that
cannot hold it.

### Why `==name`?

A pattern should read one way whatever is in scope, so a name in it always
binds. Comparing needs its own mark, and `==` already means equal. The
alternatives were a guard, which is what Ori asked for, and Elixir's pin,
`^name`, a new sigil. `==` touches the name it compares, so `a ==b` is
refused and a missing comma is never read as a comparison.

### Why does a name written twice ask for equality?

A pattern cannot bind one name to two values, so the only meaning left is
that the two are equal. Written so, the clause reads as its definition:
`strip_prefix([byte, *rest], [byte, *prefix])`. Ori refused a name twice
and asked for a guard; in Faun, guards asking two parameters' parts equal
became repeated names. The cost is that such a clause covers only equal
values, so another must cover the rest.

### Why are patterns spelled as the expressions that build them?

One spelling to learn, and a pattern is a picture of the value it matches:
`[x, *rest]` builds a list and takes one apart, `Ok(v)` builds and tests a
result, `(a, b)` swaps. A value written by `to_str`, `Invalid(3)` or `[1,
2, 3]`, is also the pattern that matches it.

The exceptions are the tests, which build nothing: ranges, `==name`, a
name written twice, `name is pattern`, and a list's end, `[*init, last]`,
which takes a list apart from the end but is refused where a list is
built, offering `init.append(last)`.

### Why does `=` bind again, Python's way?

Loops carry state in names: `count = count + 1` is a step, and a round is a
call of the loop with the names its body bound again. Faun first refused
binding a name twice, which cost a fresh name for every step and, in a
worklist, a `ready = rest` that a `continue` above it skipped forever. The
loops draft's `$` variables put a sigil on every mention of what a loop
changes. Shadowing, as Ori had it, hides the new binding at the end of its
block, so a branch's `count = count + 1` would vanish after the branch
without a word.

The cost is that a reader meeting a name must look above for every line
binding it, and a typo, `totl = total + 1`, binds a new name. An unused
binding is a [lint](../lints.md), not yet built. Values have no identity, so
`snapshot = order` stays what it was when `order` is bound again.

## Related

- [Conditions](../proposals/approved/conditions.md): the decided design for
  `is`, arms, leaving lines and binding again, with its errata
- [Pattern matching, the domain](pattern-matching-domain.md): the exploration,
  other languages' spellings, and the designs weighed
- [Loops](../proposals/approved/loops.md): `for`, `while`, and names carried
  across rounds
- [Effects](effects.md): how a test takes apart a value holding a file
- [Tags](../values/tags.md): rows, and how coverage closes them
- [Lints](../lints.md): the choices between forms left to a linter
