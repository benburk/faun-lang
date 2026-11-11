# Pattern matching

This note owns taking values apart: the patterns themselves, where they
stand, the `is` test and its arms, the leaving lines that go with them, what
the compiler checks a group of clauses or arms to cover, and how a name in a
pattern binds, with the blocks those lines and names live in. The long
exploration that led here, with the designs weighed and the superseded
`when` draft, is [pattern matching, the domain](pattern-matching-domain.md);
why there are no loops is [iteration's](../iteration.md).

## Where a pattern stands

- **A clause's parameters,** with an optional guard, `if condition`. A
  clause whose patterns or guard fail falls to the next clause.
- **A test,** `value is pattern`, a `Bool`, and **arms,** `value is ( … )`,
  which answer by the first arm that matches.
- **A binding and a lambda's parameters.** These cannot fail, so their
  pattern must match whatever it is handed: names, records, tuples, and the
  constructor of a type that has no other.

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
is (Ok(x), Ok(y))`; a chain, `x is Ok(y) & f(y) is Ok(z)`, is for a test
reading what an earlier one bound. A test is neither chained nor compared:
`a is P is Q` and `x is 3 == y` are refused, saying to join with `&` or to
parenthesize. `?` on the right of `&` or `|` is refused, since that side may
not be worked out.

Arms answer by the first arm, a line apiece, whose pattern matches and
whose guard holds. An arm's names are seen by its guard and its value, and
the arms answer one type. An arm's value follows `then`, or a leave stands
in its place, `P return value`, adding nothing to the arms' type. An arm
may leave only where its `is` is a line's value, a binding's or a body's
answer; inside an operand or an argument it is refused. Arms on a line of
their own answer `{}`, so each arm that goes on must answer `{}`.

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

## Blocks

A body of more than one line is a block: its lines in parentheses,
bindings and effect calls, then the answer. A body of one expression needs
none. A block stands wherever an expression does, with no rule of its own:
a clause's or a lambda's body, an argument, a binding's value, a guard, an
`expect`, a `return`'s value. After `(` and one expression, the next token
says which it is: `=` a binding, `,` a tuple, `)` a grouping, a line end the
next line of a block.

```ruby
edges.fold(state, |inner, edge| (
  target = edge.target
  discover(target, inner)
))
```

A block's bindings are seen by its later lines and its answer, and nowhere
else, so a nested block's names leave with it. Its value is its last line,
or `{}` where that line is a binding or a leaving line. A line that is
neither a binding nor the last must be an [effect](effects.md) call; a value
worked out and thrown away is refused. `?` and `return` answer from the
clause or lambda the block is in, not from the block: a block is not a
function.

## Leaving lines

A block's line `condition else return value` goes on where the condition
holds, its names seen below, and leaves the clause where it fails. A line
`if condition return value` leaves where the condition holds. `return`
stands nowhere else, so every way out of a body is a line saying one, an
arm, or `?`. In an `if` line, what the condition binds is seen by the leave
alone, `if r is Err(e) return Err(e)`, since below the line it failed. A
line `r is Ok(v)` missing its `else` throws a `Bool` away and is refused.
`return`'s value may be a block doing its effects first, and the condition
may test what an effect answered (see [effects](effects.md)).

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

`=` binds a name on the lines below, to the end of the block it stands in,
whether or not it was bound before: a name bound again shadows the one
before it there, at any type, and the one before is seen again after the
block. A branch's, an arm's and a lambda's bindings are their own, so none
is seen after them, and no two ways meet holding a name. A test's or an
arm's pattern binds a name in scope again the same way, where it matched. A
binding that binds a name again, and that nothing reads, is refused: it is
what an assignment lost at the end of a branch would be.

```ruby
tally(xs, strict) -> (
  count = xs.len()
  (count, total) = if strict then (count + 1, xs.sum() * 2) else (count, xs.sum())
  (count, total)
)
```

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

The draft before it proposed `when value ( clauses )`, after Kotlin, its
arms written as a definition's clauses. It cost a keyword, and `match`,
the familiar one, is a name parsers and templates want; `when x(` read as a
call of `x`, so the space before `(` would have mattered; and an unclosed
`when` ran on through every clause after it, which have the same tokens as
arms. `is` with arms did the same work with none of those, and so
superseded it before it was built. The draft and the other spellings
weighed are in [the domain](pattern-matching-domain.md#the-when-draft).

Ori kept `when` beside `if … is` so that the keyword told a reader the
checker would break this code when the type grew. Faun keeps that signal in
the shape of the form instead. The cost is the parentheses around
alternatives, `x is (A | B)`, since `|` is also the `Bool` or; freeing `|`
by making the `Bool` operators words, `and` and `or`, would change every
`Bool` expression to save them.

### Why do tests bind names along `&`?

So a body can test a value it computed and go on with what it found,
without a helper. Before tests, the heap and graph libraries carried
helpers such as `visiting`, `drained`, `stepped`, `climb_past`, `sink_past`
and `enter` that existed only to take apart one computed value, each with a
made-up name, a signature longer than its body, and its caller's context
passed in by hand: `stepped` took `settled`, `node` and `route` only because
it could not see them, and `sink_past` took six parameters. The heap's
sift-down, one loop with one comparison in a textbook, was read across
`sink`, `cheaper`, `either` and `sink_past`. Ori's own code showed the same
pressure: an arm whose body at once matched another computed value
appeared 72 times, mostly two-way steps in parsers.

Dijkstra's walk back along a path shows the difference:

```ruby
# With a helper
back(settled, node, route) -> (
  step = settled.get_or(node, Err(Unreachable))
  stepped(settled, node, step, [node, *route])
)

stepped : (Settled(e), Nat, Result(Step(e), [Unreachable]), List(Nat)) -> Result(List(Nat), [Unreachable])
stepped(_, _, Err(Unreachable), _) -> Err(Unreachable)
stepped(_, node, Ok({from, *}), route) if from == node -> Ok(route)
stepped(settled, _, Ok({from, *}), route) -> back(settled, from, route)

# With a test
back(settled, node, route) -> (
  settled.get_or(node, Err(Unreachable)) is Ok({from, *}) else return Err(Unreachable)
  walked = [node, *route]
  if from == node then Ok(walked) else back(settled, from, walked)
)
```

Not every helper was of this kind: a guard on a definition's own
parameters, or a step any language would name, stays clauses.

A name is seen only where its test is known to have held, which `&`
working out its right side only where the left held makes sound. The cost
is flow-sensitive scope: where a name is seen depends on `&` and `else`
lines, not only on blocks. A use where it is hidden is refused with the
reason.

### Why leaving lines instead of nesting?

An early exit closes a case: once `popped is Ok(…) else return state` has
run, nothing below thinks about an empty heap, where a nested branch holds
the case open to the end of its `else`. Dijkstra's `back` became three flat
lines.

The cost is that the leave is at the line's end: a line begins like any
expression and says it leaves only at `else return`. `return` stands only
in a leaving line or an arm, so a search for it finds every exit but `?`.

### Why two leaving lines?

They do two jobs. An `else` line takes a value apart or checks what should
hold, its names going on below: `r is Ok(v) else return 0`. An `if` line
bails out on a case, nothing going on from it: `if n is Bot return Bot`.
With one direction only, every leave an `else` line, a line bailing out
had to be negated to fit, `!(n is Bot) else return Bot`, `n == 0 else
return 0`. The cost is a second form a reader learns, each reading its
own way round.

Neither line begins with a keyword of its own. Both fresh designs drawn up
for [the domain](pattern-matching-domain.md#decided) chose `guard`, and the
line was first built as `expect condition else …`; but `return` already
marks the leave and `else` the direction, and `expect` in a body would have
meant both an assumption and a leave, told apart at the line's end. `if c
else return x` was turned down for the same reason: a keyword where the
`else` already says it.

### Why no `return` expression?

So every exit is a line saying so. A `return` anywhere in an expression,
or `??` with an exit as Zig's `orelse` is, `v = x ?? return 0`, would let a
leave hide inside an operand; `??` would also serve only a `Result`, a
second way to write what an `else` line writes. Syntax is spent on what a
method cannot do, leaving a clause or bringing names into scope; choosing a
value is a method's job, so a default for a failed `Result` is `ok_or`,
not an operator.

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

A name in scope written in a pattern was at first refused, to guard against
meaning a comparison. That made a pattern's names read by what was in
scope, and cost steps: a worklist taken apart as `ready is [node, *rest]`
needed `ready = rest` after it. With `==name` to say compare, the refusal
went on 2026-10-11.

### Why `is` for the whole and its parts?

`right is [y, *_]` names the whole value and takes it apart, after Finch's
penultimate conditional syntax: `is` means "which is" there as it does in a
test. Rust's and Haskell's `@` is a token for it, and OCaml's and Roc's
`as` a keyword; Faun needed neither.

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

### Why does `=` bind again, as a shadow?

A step is a name bound again: `degrees = degrees.put(target, degree)`, or
`(seen, group) = walk(graph, [start], seen, [])`. Faun first refused binding
a name twice, which cost a fresh name for every step, `degrees2`. Binding
from here on, Python's way, carried a branch's assignment past the branch
and a loop's into its next round, which cost resolution a merge of every
name each way bound again; with loops gone
([iteration](../iteration.md)), only `if c then (x = a)
else {}` needed it, which `x = if c then a else x` says in one line.
Shadowing alone would let a branch's `count = count + 1` vanish after the
branch without a word, which is why a binding again that nothing reads is
refused.

The cost is that a reader meeting a name must look above for every line
binding it, and a typo, `totl = total + 1`, binds a new name. A name bound
for the first time and never read is a [lint](../lints.md), not yet built.
Values have no identity, so `snapshot = order` stays what it was when
`order` is bound again.

### Why one `=`, and no `:=` or sigil for a step?

A separate operator for binding again, `x := x + 1`, would show every step
on its line and refuse a typo rather than leave it to a lint; but it is a
second binding operator for what one `=` says. The loops draft marked a
name a loop changed with `$` at every use, `$order.append(node)`, a sigil
on every mention. A name holding one type everywhere, as first built,
needed a fresh name for each step of a straight line converting a value,
`Str` to `Nat`; a shadow takes any type.

### Why is `order.append(node)` alone on a line refused?

Nothing changes in place: a method answers a new value and changes nothing
it was given, so a step is `order = order.append(node)`. Writing the
answer back to `order` would make whether a line changes a name hang on
the line's shape and the method's type. A list nothing else holds is still
written where it lies, so the step costs what a mutation would
([memory](../machine/memory.md)).

### Why parentheses for a block?

A clause is `pattern -> expression`, and a block makes a body of several
lines one expression. Before blocks, a body was the lines after its
clause's `->`, and a pass after parsing decided which lines were whose. A
body may hold an effect call on a line of its own anywhere, so after a
body ending in one, `Edge(e) = {target: Nat, weight: e}` could be a binding
in the body or an alias, and only indentation, which the grammar ignores,
told which. With blocks the top level holds no bindings, every item is
whole when the parser reads it, the grammar stays LL(1), and lambdas get
bodies, which ended helpers such as the graph library's `relax`,
`discover` and `gather` written partly to hold an intermediate value. A
block is a node an editor can select and fold.

Braces, as Ori's blocks are, would clash with records: `{x}` puns a field.
Parentheses already group, and after the first expression the next token
says whether they hold a grouping, a tuple or a block. Layout, a line at
column 0 as an item, is ruled out by the [syntax](syntax.md) goals.

The cost is a `)`, in practice a line, on every body of several lines:
536 of about 3,165 clauses changed when blocks came in. A missing `)` can
run far, so an unclosed block is told at its `(` where a line in it runs
into a clause's `->` or a signature's `:`, neither of which a block holds.
One meaning changed: inside parentheses, `(a` then `-b` on the next line is
two lines, as at the top level, where it had been `a - b`.

### Why does a block ending in no value answer `{}`?

So a block whose last line is a binding or a leaving line needs no `{}`
line written after it, as Rust's block ending in a statement answers `()`.
Arms that only do effects, and a block ending where a leaving line goes on,
end plainly. The cost is that a body ending in a binding by mistake is a
type mismatch where its answer is used, not a refusal at the line, and
where nothing is declared it may go unnoticed until a caller uses it; the
mismatch notes that such a block answers `{}`, and points at its last line.

## History

- **2026-09-29:** blocks were proposed, approved and built the same day,
  after the graph library's `Edge(e) = {target: Nat, weight: e}` would not
  parse. Every body of several lines and every `where` list of several
  lines was migrated by script, and the pass grouping lines into items
  went.
- **2026-10-01:** a draft proposed `when value ( clauses )` for branching
  on a computed value. Discussing its further steps led to the conditions
  proposal on 2026-10-03, and to the exploration in
  [the domain](pattern-matching-domain.md) on 2026-10-04.
- **2026-10-04 to 10-07:** conditions were built a part at a time: `if c
  then a else b` and short-circuiting `&` and `|` (10-04); `is` as a test,
  and a refusal of binding a name already in scope (10-05); `name is
  pattern`, `==name`, and guards whose test binds for the clause's body
  (10-06); then arms, join points so `?` and leaves work from any branch,
  `if` leaving lines, and `=` binding a name from here on, past branches and
  across a loop's rounds (10-07). The leaving line was first built as
  `expect condition else …`; the keyword went on 10-07.
- **2026-10-11:** a pattern binds a name in scope again where it matched,
  as `=` did, ending the refusal of 10-05.
- **2026-10-12:** an effect's answer may be tested where an `if` or `is`
  stands; a name bound again on ways that meet is held to one type only
  where it is read after they meet.
- **2026-10-14:** conditions were approved, superseding the `when` draft,
  and a test or arms of a value holding a resource were built.
- **2026-10-16:** an arm's value follows `then`, not `->`, and an arm may
  leave in its place. Parsing a value of several fields from keyed input
  asked for it: an arm for each key, and one leaving with the error.
- **2026-10-18:** a block ending in a binding or a leaving line answers
  `{}`, where it had been refused as having no answer.
- **2026-11-10:** with loops removed, binding from here on became
  shadowing, and a binding again that nothing reads is refused; `continue`
  and `break`, which leaving lines and arms had taken beside `return`, went
  with loops ([iteration](../iteration.md)).

## Related

- [Pattern matching, the domain](pattern-matching-domain.md): the exploration,
  other languages' spellings, the designs weighed and the `when` draft
- [Iteration](../iteration.md): walks, and why there are no loops
- [Effects](effects.md): effects in tests, and how a test takes apart a
  value holding a file
- [Tags](../values/tags.md): rows, and how coverage closes them
- [Types](../types.md): aliases with parameters, which blocks made possible
- [Lints](../lints.md): the choices between forms left to a linter
