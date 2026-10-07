# Proposal: Conditions that bind

- **Status:** Draft
- **Created:** 2026-10-03
- **Affects:** the lexer's keywords, `grammar.ebnf`, the parser, the
  tree-sitter grammar, name resolution, the checker, pattern compiling,
  lowering to Barb, every helper that exists only for a two-way test or a
  destructuring that can fail

---

## Summary

One operator and one line form, as the
[pattern matching survey](../../pattern-matching.md) decided.

- **`value is pattern`** is a `Bool` that binds the pattern's names where
  it holds: along the rest of an `&` chain, into an `if`'s `then` branch, a
  guard's clause body, an arm's value, and the lines below an `else` line.
- **`condition else …`**, a block's line, goes on where the condition
  holds, keeping what it bound for the lines below, and otherwise leaves the
  clause, a round or a loop.
- **`value is ( arms )`** answers by the first arm that matches.
- **`is` inside a pattern** binds a value and takes it apart: `right is [y,
  *_]`; **`==name`** in a pattern compares with a name from outside it.
- **Assignment, not shadowing.** `name = value` on a name in scope changes
  it from there on, past branches and across a loop's rounds. Patterns only
  ever declare names.

Built already, as parts of this proposal: `if c then a else b`, and `&` and
`|` on `Bool` working out their right side only where the left has not
decided.

| Form                 | Today       | Proposed                           |
| -------------------- | ----------- | ---------------------------------- |
| Test a shape         | `r.is_ok()` | `r is Ok(_)`                       |
| Test and bind        | a helper    | `if r is Ok(v) then v else 0`      |
| Take apart, or leave | a helper    | `r is Ok(v) else return 0`         |
| Leave on a test      | a helper    | `n != 0 else return 0`             |
| Choose by shape      | a helper    | `r is (Ok(v) -> v`, `Err(_) -> 0)` |
| Whole and parts      | rebuild it  | `right is [y, *_]`                 |
| Compare in a pattern | a guard     | `r is Some(==node)`                |
| A step               | a new name  | `order = order.append(node)`       |

```
# Today
back(settled, node, route) -> (
  step = settled.get_or(node, Err(Unreachable))
  stepped(settled, node, step, [node, *route])
)

stepped : (Settled(e), Nat, Result(Step(e), [Unreachable]), List(Nat)) -> Result(List(Nat), [Unreachable])
stepped(_, _, Err(Unreachable), _) -> Err(Unreachable)
stepped(_, node, Ok({from, *}), route) if from == node -> Ok(route)
stepped(settled, _, Ok({from, *}), route) -> back(settled, from, route)

# Proposed
back(settled, node, route) -> (
  settled.get_or(node, Err(Unreachable)) is Ok({from, *}) else return Err(Unreachable)
  walked = [node, *route]
  if from == node then Ok(walked) else back(settled, from, walked)
)
```

## Motivation

A Faun body cannot test a value it computed and go on with what the test
found: only a definition's clauses take values apart, and only its
parameters. So each such test is a definition of its own, with a made-up
name, a signature longer than its body, and its caller's context passed in
by hand. In the heap and graph libraries, `visiting`, `drained`, `stepped`,
`climb_past`, `sink_past` and `enter` exist only for that; `sorted` and
`either` did, until `if` folded them.

An early exit closes off a case: once `popped is Ok(…) else return state`
has run, nothing below has to think about an empty heap. A nested branch
holds the case open to the end of its `else`.

## Design

### Syntax earns its place by control flow

An operator or keyword is added only for what a method cannot do: leave a
clause early, or bring names into scope. Choosing a value is a method's
job, so a default for a failed `Result` stays `ok_or`.

### `is`

- **Syntax.** `expr is operand`, at a level of its own between `&` and the
  comparisons:

  ```
  infix levels, loosest first:
    |   ^   &   is   == != < <= > >=   + -   / % *
  ```

  The right side is one operand, made a pattern by `lines::pattern`, which
  makes a clause's head one; so `is` takes every pattern a parameter does.
- **Or-patterns are parenthesized:** `acct is (Admin(name) | User(name))`.
  Unparenthesized, the `|` is an or of a test and a constructor, and the
  message says to group it.
- **Not chained, and not compared.** `a is P is Q` is refused, saying to
  join tests with `&`; so is `x is 3 == y`, saying to parenthesize the test.
- **Several values** are tested as a tuple, `(a, b) is (Ok(x), Ok(y))`; a
  chain, `x is Some(y) & f(y) is Some(z)`, is for a test reading what an
  earlier one bound.
- **Meaning.** `True` where the value matches; the value is worked out once.
- **Scope.** What a pattern binds is seen where the test is known to have
  held: by the operands to its right along `&`, and, where the whole
  condition is such a chain, by an `if`'s `then` branch, a guard's clause
  body, and the lines below an `else` line. Past an `|`, a name both sides
  bind, from whichever held; under `!` or an argument, nowhere. A use where
  a name is not seen is refused, naming what hid it.
- **A pattern declares.** A pattern may not bind a name already in scope:
  `r is Ok(limit)` with `limit` in scope reads as a comparison and would be
  a fresh binding, so it is refused, offering `Ok(==limit)` to compare or a
  fresh name to bind. Changing a name is `=`'s alone; see
  [Names](#names-assignment-not-shadowing).
- **`==name`** in a pattern matches a value equal, by its type's `equals`,
  to a name from outside the pattern, binding nothing: `r is Some(==node)`.
  Within one pattern, a clause's parameters too, a name written twice asks
  its two parts equal, `[a, a, *_]`; `[a, ==a]` would read as if `a` were
  bound before the pattern, and is refused.
- **`?` on the right of `&` is refused,** as in a branch: it would be worked
  out before the left had decided, and before the left's names exist.
- **`=` against `is`.** A binding, `P = expr`, cannot fail, and a pattern
  that can is refused, the message offering `expr is P else return …`.
  Which a line writes says whether it can fail.

### `is` inside a pattern

`name is pattern`, where a pattern stands, binds `name` to the whole value
and takes it apart with `pattern`, after Finch's penultimate conditional
syntax:

```
merge([x, *xs], right is [y, *_]) if x <= y -> [x, *merge(xs, right)]
```

### Arms

`value is ( arms )`, an arm a line, `pattern if guard -> value`, answers by
the first arm whose pattern matches and whose guard holds. An arm's names
are seen by its guard and its value; the arms cover every value, as
clauses do, and answer one type.

```
area(shape) -> shape is (
  Circle(r) -> 3 * r * r
  Rect(w, h) -> w * h
  Dot -> 0
)
```

Clauses where the body is the dispatch; arms where a value worked out
partway through a body is.

### `else` lines

- **Syntax.** A block line, `condition "else" out`, with `out = "return"
  expr | "continue" | "break" | block`, a block's last line being one of
  the others; `continue` and `break` come with [loops](loops.md). Not an
  expression, and not a block's last line.
- **Meaning.** Where the condition holds, the block goes on, what it bound
  in scope for every line below. Where it fails, the `else` runs and leaves:
  `return x` answers `x` from the clause or lambda the block is in, as `?`
  does, its type that clause's; a block may do its effects first.

  ```
  config is Ok(settings) else (
    log!("no config, using defaults")
    return defaults
  )
  ```
- **One direction.** A line says what should hold. A plain test reads
  `n != 0 else return 0`; a shape to leave on is negated, `!(n is Bot) else
  return Bot`, and binds nothing.
- **Every way out is marked.** `return`, `continue` and `break` stand only
  after a line's `else`, so a body leaves only on a line saying `else
  return`, `else continue` or `else break`. A line `r is Ok(v)` missing its
  `else` throws away a `Bool`, which is refused.
- **`expect` stays a test.** At the top level, `expect` is a test, as
  before. In a body it will be an assumption: checked in development and in
  tests, skipped in optimized builds, binding nothing, changing nothing a
  program does. It is not built yet, and a body's line beginning `expect`
  is refused, saying how to leave.
- **Which to write.** An `else` line for a check before the main work; the
  ternary for the answer itself, on a body's last line: `if done then
  Ok(order) else Err(Cycle)`; arms for a choice among shapes; clauses where
  the whole body is the dispatch.
- **Leave, not exit.** A program ends with `host.exit!`; an `else` leaves a
  clause, a round or a loop.

### Names: assignment, not shadowing

- **`name = value` on a name in scope assigns it.** From that line on the
  name holds the new value: on the lines below, after the branch or arm it
  was assigned in, and in a loop's next round and after the loop. `x = x +
  1` is a step, as in Python.
- **A name keeps its type.** Assigning a value of another type is refused.
- **Patterns declare.** A name in a pattern, a clause's head, a lambda's
  parameters, a test or an arm, is a new one, and one already in scope is
  refused. Only `=` assigns. A destructuring binding assigns the names it
  holds that are in scope and declares the rest: `(a, b) = (b, a)` swaps.
- **Nothing changes in place.** A method answers a new value and changes
  nothing it was given: `order = order.append(node)`, never a bare
  `order.append(node)`, which throws its answer away and is refused. A list
  nothing else holds is still written where it lies, so a step costs what a
  mutation would.
- **No aliasing.** `snapshot = order` stays a snapshot when `order`
  changes: values have no identity.
- **A lambda assigns only its own names.** One assigning a name of the body
  around it is refused: a callee may call it any number of times, or none.
- **Meaning.** Each assignment is a new version of the name. Where branches
  meet, after an `if`, an `is` with arms, or an `else` line's block, the
  names a branch assigned are the parameters of the code after it, a join
  point; a loop's round is a call of the loop with the names its body
  assigned. So a function with assignments is as pure as one without.

### Built

- **`if c then a else b`,** 2026-10-04: an expression beginning an
  expression, its branches values; `?` in a branch refused. `Order.then`
  became `Order.or`, `then` being a keyword.
- **`&` and `|` on `Bool`** work out their right side only where the left
  has not decided, 2026-10-04.
- **`is` as a test,** 2026-10-05: binding along `&` and into `then`,
  tuples, grouped alternatives, the shadowing rule, and `?` refused on the
  right of `&` and `|`. Lowering makes each test a decision of its own
  rows, a row for each alternative and one for any other value, its `else`
  copied to each test of a chain. Left for later: a test of a value holding
  a resource, refused for now; a type taken apart by its own name, as
  `U8(…)`, which only a clause's head expands.
- **`expect … else`,** 2026-10-06, then **`… else`,** 2026-10-07: `return`
  and a block's `else` line, leaving by `return` or by a block ending in
  one, from a block answering its clause or lambda; elsewhere refused until
  join points. Where its block answers, an `else` line is an `if` holding
  the lines after it, so it needed no lowering of its own; `?` in an `if`
  branch answering its clause came with it. Dijkstra's `back` is three flat
  lines; the heap's `visiting` and `drained`, proptest's step, and `Map`'s
  `removed` became `else` lines, and `split_step`, `recalled` and clap's
  `custom_value` became `if … is`. The line first began with `expect`; the
  keyword went once `return` was seen to mark the leave.
- **Patterns and guards,** 2026-10-06: `name is pattern` and `==name` in a
  clause's head and a test; a guard's test binding for its clause's body; a
  name both sides of an `|` bind seen past it. `==name` becomes a fresh
  name asked equal after the pattern matches, as a name repeated in a head
  already was. A guard's test is a column of its own in the clause's
  decision, worked out where the head has matched, so a failure falls to
  the next clause; its `|` is tried as one among a head's parameters, the
  right where the left or what follows it fails. An `|` in a test copies its
  `then` to each side. Guards asking two parameters' parts equal became a
  name written twice, and clauses rebuilding what their head took apart
  name it whole, as the standard list's merge does; the parser library's
  number reader lost two clauses.
- **Arms,** 2026-10-07: `value is ( arms )`, a line apiece, with guards.
  Arms read where a parenthesized expression's first one is followed by
  `->` or `if`, and are refused after parsing where no `is` takes them. One
  decision tests the value for every arm, a row for each alternative, each
  arm's body a block as an `if`'s branch is; arms cover every value, as
  clauses do, and a resource is not yet taken apart by them.
- **Join points,** 2026-10-07: `?` and `else` lines leave from any branch,
  arm or block. In a function's tail, an `if` or arms with a branch that
  may leave is made to answer the function: the lines after it become a
  function of the branch's value and what they read, each branch going on
  calls it, and a `return` answers where it stands. `return` stays a node
  until then. No change to Barb.
- **Assignment,** 2026-10-07: a binding naming a name in scope assigns it,
  a new local from there on, held to the old one's type. After an `if`,
  arms or an `else` line, each name a branch going on assigned is a new
  local every such branch binds last; a block's assignments stay. Lowering
  hands those out of a branch as a tuple beside its value where no branch
  leaves, and as the join point's parameters where one does. Refused: an
  assignment in a condition or the right of `&` or `|`, and a lambda
  assigning its body's name.
- **No rebinding,** 2026-10-05: a binding or a test binding a name already
  in scope is refused; a lambda's and a clause's patterns already were. The
  parser library's example and AoC 2015 day 19 took names of their own.
  Assignment replaces it for `=`; patterns keep the refusal.

## Costs

- **Keywords.** `is` and `return` now, `continue` and `break` with loops.
  No program uses one as a name.
- **The leave is at the line's end.** A line begins like any expression and
  says it leaves only at `else return`. A search for exits looks for
  `return`, `continue` and `break`, which nothing else spells.
- **Two orders.** `P = expr` puts the pattern first, `expr is P` the value.
  The order marks the meaning: one cannot fail, the other can.
- **Flow-sensitive scope.** Where a name is seen depends on `&` and on
  `else` lines, not only on blocks and clauses.
- **Leaving on a shape reads negated:** `!(n is Bot) else return Bot`.
- **A name may change.** A reader meeting `order` must look above for the
  lines assigning it, where a name meaning one value spared that. A typo,
  `totl = total + 1`, declares a new name, which an unused-name lint
  catches.
- **A shared failure branch.** In `if a is P & b is Q then x else y`, `y`
  is reached from either test. Lowering copies it to each place it is
  reached from until join points share it.

## Alternatives considered

- **`expect condition else …`,** the line form first built. A keyword
  leading every exit, where `return` already marks one; and `expect` in a
  body would have meant both an assumption and a leave, told apart at the
  line's end.
- **`if` lines in both directions,** `if c return x` and `if c else return
  x`. Two forms for one job; both designs drawn up afresh from the survey's
  brief chose a single line form.
- **`guard`,** the keyword both fresh designs chose. A keyword where `else`
  and `return` already say it.
- **`&` guards,** `f(Move(d)) & d > 100 ->`, reading as `is P & c`. A
  hundred guards migrate, and `|` in a guard needs parentheses.
- **`let … else`,** `Ok(v) = x else return 0`. Pattern-first where a test
  is value-first.
- **`??` with an exit,** `v = x ?? return 0`, as Zig's `orelse`. Only for a
  `Result`; a second way to write that case.
- **A general `return` expression.** Exits anywhere in an expression.
- **`@` or `as`** for the whole and its parts: a token or a keyword where
  `is` already means "which is".
- **A pin, `^name`,** to compare in a pattern: a new sigil where `==`
  already means equal.
- **No rebinding, with `$` variables for loops,** as built first and as the
  loops draft had it. A name meant one value for its whole scope, at the
  price of a fresh name for every step and a sigil on every mention of what
  a loop changes.
- **Shadowing,** a name bound again hiding the one before for the rest of
  its block. Straight-line code reads the same as assignment, but a branch's
  `count = count + 1` would vanish after the branch, silently.
- **Writing back,** a bare `order.append(node)` changing `order`. Whether a
  line changes a name would hang on the line's shape and the method's type.
- **Word operators, `and` and `or`,** freeing `|` for patterns. Every
  `Bool` expression changes.
- **`??` for a default.** It is `ok_or`: a value, not control flow.

The survey compares these as whole designs.

## Implementation impact

1. **`is` as a test.** The lexer's keyword; the `is` level in the grammar,
   `grammar.ebnf` and tree-sitter; resolution scoping names along `&` and
   into a `then` branch; the checker typing the pattern against the value;
   lowering each `if` whose condition binds into the matches it needs, its
   failure branch copied to each test. Built.
2. **`else` lines.** `return`; resolution keeping a line's names for the
   lines below; lowering a line as a match whose failure arm leaves. Built
   where the block answers.
3. **`is` and `==name` inside patterns, arms,** and guards whose `is` binds
   for the clause body. Built.
4. **Join points.** Lowering to Barb makes the rest of a body after a
   branch an ordinary function of the names live there, called in tail
   position from each branch that goes on, so a branch can leave instead:
   `?` and `else` lines anywhere, and no copied branches. No change to Barb.
5. **Assignment.** Resolution makes each assignment a new version of the
   name and records, for each branch and loop, the names it assigns; those
   are the join point's parameters. The no-rebinding refusal for `=` goes;
   patterns keep theirs.
6. **Programs.** Helpers that branch partway through their caller folded;
   those whose body is the dispatch kept as clauses; steps that took fresh
   names may assign.

## Testing

- `ebnf.rs` probes for each form; refused probes for `is` chained or
  compared, an unparenthesized or-pattern, and an `else` line ending a
  block.
- Refused cases with their `.err`: a name used where `|` or `!` hid it, a
  pattern binding a name in scope, `?` on the right of `&`, `return` outside
  a line's `else`, an assignment changing a name's type, a lambda assigning
  its body's name.
- Running cases across the three backends: tests in `if`, chains, tuples,
  a test as a value, `else` lines, arms, `==name`, and a name assigned in a
  branch and read after it.

## Origin

Discussion of the [branching](branching.md) draft's further steps
(2026-10-03), then the [pattern matching survey](../../pattern-matching.md)
(2026-10-04), which compared five designs and took two ideas from the
ultimate and penultimate conditional syntaxes. On 2026-10-07 the `expect`
keyword left the line form, and assignment replaced no-rebinding and the
loops draft's `$` variables.
