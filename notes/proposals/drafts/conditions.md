# Proposal: Conditions that bind

- **Status:** Draft
- **Created:** 2026-10-03
- **Affects:** the lexer's keywords, `grammar.ebnf`, the parser, the
  tree-sitter grammar, name resolution, the checker, pattern compiling,
  every helper that exists only for a two-way test or a destructuring that
  can fail

---

## Summary

One operator and one line form, from the
[pattern matching survey](../../pattern-matching.md)'s design E.

- **`value is pattern`** is a `Bool` that binds the pattern's names where
  it holds: along the rest of an `&` chain, into an `if`'s `then` branch, a
  guard's clause body, and the lines below an `if` line.
- **An `if` line leaves** the clause, a round or a loop: `if c return x`
  where `c` holds, `if c else return x` where it fails, keeping what `c`
  bound for the lines below.
- **`is` inside a pattern** binds a value and takes it apart: `right is [y,
  *_]`.

Built already, as parts of this proposal: `if c then a else b`, and `&` and
`|` on `Bool` working out their right side only where the left has not
decided.

| Form                    | Today              | Proposed                      |
| ----------------------- | ------------------ | ----------------------------- |
| Test a shape            | `r.is_ok()`        | `r is Ok(_)`                  |
| Test and bind           | a helper's clauses | `if r is Ok(v) then v else 0` |
| Take apart, or leave    | a helper's clauses | `if r is Ok(v) else return 0` |
| Leave on a test         | a helper's clauses | `if n == 0 return 0`          |
| The whole and its parts | rebuild it         | `right is [y, *_]`            |

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
  if settled.get_or(node, Err(Unreachable)) is Ok({from, *}) else return Err(Unreachable)
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

An early exit closes off a case: once `if popped is Ok(…) else return
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
  body, and the lines below an `if` line leaving where it fails. Under `|`,
  `!` or an argument, nowhere; a use there is refused, naming what hid it.
- **Shadowing.** A pattern may rebind the name it tests, `step is
  Ok(step)`. It may not bind any other name already in scope: `r is
  Ok(limit)` with `limit` in scope is refused, since it reads as a
  comparison and is a fresh binding; the message offers `r is Ok(n) & n ==
  limit`.
- **`?` on the right of `&` is refused,** as in a branch: it would be worked
  out before the left had decided, and before the left's names exist.
- **`=` against `is`.** A binding, `P = expr`, cannot fail, and a pattern
  that can is refused, the message now offering `if expr is P else return
  …`. Which a line writes says whether it can fail.

### `is` inside a pattern

`name is pattern`, where a pattern stands, binds `name` to the whole value
and takes it apart with `pattern`, after Finch's penultimate conditional
syntax:

```
merge([x, *xs], right is [y, *_]) if x <= y -> [x, *merge(xs, right)]
```

### `if` lines

- **Syntax.** A block line beginning `if` takes, after its condition, one
  of three:

  ```
  "if" condition ( exit                       # leave where it holds
                 | "else" exit                # leave where it fails
                 | "then" expr "else" expr )  # a value either way
  exit = "return" expr | "continue" | "break"
  ```

  The token after the condition decides, so the grammar stays LL(1). The
  first two are lines of a block, not expressions; `continue` and `break`
  come with [loops](loops.md).
- **Meaning.** `return x` answers `x` from the clause or lambda the block is
  in, as `?` does; its type is that clause's. Leaving where the condition
  fails keeps what it bound for every line below.
- **Which to write.** Leave where it holds for a plain test, `if n == 0
  return 0`; leave where it fails where the condition binds what follows
  uses, `if r is Ok(v) else return 0`. A choice of the answer itself, on a
  body's last line, is the ternary: `if done then Ok(order) else
  Err(Cycle)`.
- **`return` is not an expression.** It stands only after an `if` line's
  condition or `else`, so every exit in a body begins a line with `if`.

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

- **Keywords.** `is` and `return` now, `continue` and `break` with loops. No
  program uses one as a name.
- **Two orders.** `P = expr` puts the pattern first, `expr is P` the value.
  The order marks the meaning: one cannot fail, the other can.
- **Flow-sensitive scope.** Where a name is seen depends on `&` and on `if`
  lines, not only on blocks and clauses.
- **Two directions for a plain test.** `if n == 0 return 0` and `if n != 0
  else return 0` mean the same; the style is the first.
- **A shared failure branch.** In `if a is P & b is Q then x else y`, `y`
  is reached from either test. Lowering copies it to each place it is
  reached from until a branch can be shared.

## Alternatives considered

- **A bare `else` line,** `r is Ok(v) else return 0`. The exit hides at the
  end of the line; an `if` line puts every exit at the margin.
- **`&` guards,** `f(Move(d)) & d > 100 ->`, reading as `is P & c`. A
  hundred guards migrate, and `|` in a guard needs parentheses.
- **`let … else`,** `Ok(v) = x else return 0`. A second form for a plain
  test, and pattern-first where a test is value-first.
- **`??` with an exit,** `v = x ?? return 0`, as Zig's `orelse`. Only for a
  `Result`; a second way to write that case.
- **`guard`.** A keyword where `if` serves.
- **A general `return` expression.** Exits anywhere in an expression.
- **`@` or `as`** for the whole and its parts: a token or a keyword where
  `is` already means "which is".
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
2. **`if` lines.** `return`; resolution keeping a failing line's names for
   the lines below; lowering a line as a match whose failure arm answers.
3. **`is` inside patterns,** and guards whose `is` binds for the clause
   body.
4. **Programs.** The heap's `visiting`, `drained`, `climb_past` and
   `sink_past`, and the graph library's `stepped` and `enter`, folded.

## Testing

- `ebnf.rs` probes for each form; refused probes for `is` chained or
  compared and an unparenthesized or-pattern.
- Refused cases with their `.err`: a name used where `|` or `!` hid it, a
  shadowing test, `?` on the right of `&`, `return` outside an `if` line.
- Running cases across the three backends: tests in `if`, chains,
  tuples, a test as a value, early exits in both directions.

## Origin

Discussion of the [branching](branching.md) draft's further steps
(2026-10-03), then the [pattern matching survey](../../pattern-matching.md)
(2026-10-04), which compared five designs and took two ideas from the
ultimate and penultimate conditional syntaxes.
