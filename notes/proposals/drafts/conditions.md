# Proposal: Conditions that bind

- **Status:** Draft
- **Created:** 2026-10-03
- **Affects:** the lexer's keywords, `grammar.ebnf`, the parser, the
  tree-sitter grammar, name resolution, the checker, pattern compiling,
  every helper that exists only for a two-way test or a destructuring that
  can fail

---

## Summary

One operator and one line form, as the
[pattern matching survey](../../pattern-matching.md) decided.

- **`value is pattern`** is a `Bool` that binds the pattern's names where
  it holds: along the rest of an `&` chain, into an `if`'s `then` branch, a
  guard's clause body, and the lines below an `expect` line.
- **`expect condition else …`** goes on where the condition holds, keeping
  what it bound for the lines below, and otherwise leaves the clause, a
  round or a loop.
- **`is` inside a pattern** binds a value and takes it apart: `right is [y,
  *_]`; **`==name`** in a pattern compares with a name in scope.
- **No rebinding.** A name means one value for its whole scope.

Built already, as parts of this proposal: `if c then a else b`, and `&` and
`|` on `Bool` working out their right side only where the left has not
decided.

| Form                 | Today       | Proposed                          |
| -------------------- | ----------- | --------------------------------- |
| Test a shape         | `r.is_ok()` | `r is Ok(_)`                      |
| Test and bind        | a helper    | `if r is Ok(v) then v else 0`     |
| Take apart, or leave | a helper    | `expect r is Ok(v) else return 0` |
| Leave on a test      | a helper    | `expect n != 0 else return 0`     |
| Whole and parts      | rebuild it  | `right is [y, *_]`                |
| Compare in a pattern | a guard     | `r is Some(==node)`               |

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
  expect settled.get_or(node, Err(Unreachable)) is Ok({from, *}) else return Err(Unreachable)
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

An early exit closes off a case: once `expect popped is Ok(…) else return
state` has run, nothing below has to think about an empty heap. A nested
branch holds the case open to the end of its `else`.

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
  body, and the lines below an `expect` line. Under `|`,
  `!` or an argument, nowhere; a use there is refused, naming what hid it.
- **No rebinding.** A pattern may not bind a name already in scope, here
  or anywhere: `r is Ok(limit)` with `limit` in scope reads as a comparison
  and would be a fresh binding, so it is refused, offering `Ok(==limit)` to
  compare or a fresh name to bind. `step is Ok(step)` takes a fresh name
  too. Variables written `$name`, with [loops](loops.md), are the only names
  that change.
- **`==name`** in a pattern matches a value equal, by its type's `equals`,
  to a name in scope, binding nothing: `r is Some(==node)`.
- **`?` on the right of `&` is refused,** as in a branch: it would be worked
  out before the left had decided, and before the left's names exist.
- **`=` against `is`.** A binding, `P = expr`, cannot fail, and a pattern
  that can is refused, the message now offering `expect expr is P else
  return …`. Which a line writes says whether it can fail.

### `is` inside a pattern

`name is pattern`, where a pattern stands, binds `name` to the whole value
and takes it apart with `pattern`, after Finch's penultimate conditional
syntax:

```
merge([x, *xs], right is [y, *_]) if x <= y -> [x, *merge(xs, right)]
```

### `expect … else`

- **Syntax.** A block line, `"expect" condition "else" out`, with `out =
  "return" expr | "continue" | "break" | block`, a block's last line being
  one of the others; `continue` and `break` come with [loops](loops.md). Not
  an expression, and not a block's last line.
- **Meaning.** Where the condition holds, the block goes on, what it bound
  in scope for every line below. Where it fails, the `else` runs and leaves:
  `return x` answers `x` from the clause or lambda the block is in, as `?`
  does, its type that clause's; a block may do its effects first.

  ```
  expect config is Ok(settings) else (
    log!("no config, using defaults")
    return defaults
  )
  ```
- **One direction.** A line says what should hold. A plain test reads
  `expect n != 0 else return 0`; a shape to leave on is negated, `expect
  !(n is Bot) else return Bot`, and binds nothing.
- **Bare `expect`, later.** `expect` with no `else`, in a body, will be an
  assumption: checked in development and in tests, skipped in optimized
  builds, binding nothing, changing nothing a program does. It is not built
  yet, and `expect` in a body takes an `else` until it is. At the top level,
  `expect` stays what it is: a test.
- **Which to write.** `expect … else` for a check before the main work; the
  ternary for the answer itself, on a body's last line: `if done then
  Ok(order) else Err(Cycle)`; clauses where the whole body is the dispatch.
- **`return` is not an expression.** It stands only in an `expect`'s
  `else`, so every way out of a body is on a line beginning `expect`.
- **Leave, not exit.** A program ends with `host.exit!`; an `expect` leaves
  a clause, a round or a loop.

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
  `U8(…)`, which only a clause's head expands; and a guard's test binding
  for its clause's body.

## Costs

- **Keywords.** `is` and `return` now, `continue` and `break` with loops;
  `expect` already is one. No program uses one as a name.
- **One keyword, two meanings later.** A bare `expect` will assert, and one
  with `else` leaves; the difference is at the line's end. A bare one binds
  nothing, so a line meant to bind and missing its `else` is refused where
  its names are used.
- **Two orders.** `P = expr` puts the pattern first, `expr is P` the value.
  The order marks the meaning: one cannot fail, the other can.
- **Flow-sensitive scope.** Where a name is seen depends on `&` and on
  `expect` lines, not only on blocks and clauses.
- **Leaving on a shape reads negated:** `expect !(n is Bot) else return Bot`.
- **No rebinding** costs a fresh name where a program reused one, and
  programs that shadow today migrate.
- **A shared failure branch.** In `if a is P & b is Q then x else y`, `y`
  is reached from either test. Lowering copies it to each place it is
  reached from until a branch can be shared.

## Alternatives considered

- **A bare `else` line,** `r is Ok(v) else return 0`. The exit hides at the
  end of the line.
- **`if` lines in both directions,** `if c return x` and `if c else return
  x`. Two forms for one job; both designs drawn up afresh from the survey's
  brief chose a single line form.
- **`guard`,** the keyword both fresh designs chose. `expect` reads as well
  and is a keyword already, and its bare form has a use to come.
- **`&` guards,** `f(Move(d)) & d > 100 ->`, reading as `is P & c`. A
  hundred guards migrate, and `|` in a guard needs parentheses.
- **`let … else`,** `Ok(v) = x else return 0`. A second form for a plain
  test, and pattern-first where a test is value-first.
- **`??` with an exit,** `v = x ?? return 0`, as Zig's `orelse`. Only for a
  `Result`; a second way to write that case.
- **A general `return` expression.** Exits anywhere in an expression.
- **`@` or `as`** for the whole and its parts: a token or a keyword where
  `is` already means "which is".
- **A pin, `^name`,** to compare in a pattern: a new sigil where `==`
  already means equal.
- **Shadowing refused only for the same type,** or for all but the tested
  name. Finer, but either keeps a rule to learn where none is the simplest.
- **Word operators, `and` and `or`,** freeing `|` for patterns. Every
  `Bool` expression changes.
- **`??` for a default.** It is `ok_or`: a value, not control flow.

The survey compares these as whole designs.

## Implementation impact

1. **`is` as a test.** The lexer's keyword; the `is` level in the grammar,
   `grammar.ebnf` and tree-sitter; resolution scoping names along `&` and
   into a `then` branch; the checker typing the pattern against the value;
   lowering each `if` whose condition binds into the matches it needs, its
   failure branch copied to each test.
2. **`expect … else` lines.** `return`; resolution keeping a line's names
   for the lines below; lowering a line as a match whose failure arm
   leaves.
3. **`is` and `==name` inside patterns,** and guards whose `is` binds for
   the clause body.
4. **No rebinding,** refused in resolution, the corpus migrated.
5. **Programs.** Helpers that branch partway through their caller folded;
   those whose body is the dispatch kept as clauses.

## Testing

- `ebnf.rs` probes for each form; refused probes for `is` chained or
  compared and an unparenthesized or-pattern.
- Refused cases with their `.err`: a name used where `|` or `!` hid it, a
  rebinding, `?` on the right of `&`, `return` outside an `expect`'s `else`,
  a bare `expect` in a body.
- Running cases across the three backends: tests in `if`, chains,
  tuples, a test as a value, `expect … else` lines, `==name`.

## Origin

Discussion of the [branching](branching.md) draft's further steps
(2026-10-03), then the [pattern matching survey](../../pattern-matching.md)
(2026-10-04), which compared five designs and took two ideas from the
ultimate and penultimate conditional syntaxes.
