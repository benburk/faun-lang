# Proposal: Conditions that bind

- **Status:** Draft
- **Created:** 2026-10-03
- **Affects:** the lexer's keywords, `grammar.ebnf`, the parser, the
  tree-sitter grammar, name resolution, pattern compiling, how `&` and `|`
  on `Bool` are compiled, every helper that exists only for a two-way test
  or a destructuring that can fail

---

## Summary

One new operator and two forms built on it. `value is pattern` is a `Bool`
that binds the pattern's names where it holds. `if c then a else b` is an
expression. A block line `condition else return value` answers the clause
early where the condition fails, and leaves what the condition bound to the
lines after it. A guard is any condition, so `is` serves there too. On
`Bool`, `&` and `|` evaluate their right side only where the left has not
decided.

| Form                   | Today              | Proposed                  |
| ---------------------- | ------------------ | ------------------------- |
| Test a shape           | `r.is_ok()`        | `r is Ok(_)`              |
| Two-way choice         | a helper's clauses | `if c then a else b`      |
| Fallible destructuring | a helper's clauses | `v is P else return x`    |
| Answer early on a test | a helper's clauses | `c else return x`         |
| Bind in a guard        | a helper's clauses | `f(v) if v is P & c -> …` |

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
  step = settled.get_or(node, Err(Unreachable))
  step is Ok({from, *}) else return Err(Unreachable)
  walked = [node, *route]
  if from == node then Ok(walked) else back(settled, from, walked)
)
```

## Motivation

A Faun body cannot test a value it computed and go on with what the test
found: only a definition's clauses take values apart, and only its
parameters. So each such test is a definition of its own, with a made-up
name, a signature longer than its body, and its caller's context passed in
by hand.

Most of these helpers are one of two shapes:

- **A two-way test.** The heap's `either` picks the cheaper child,
  `climb_past` and `sink_past` decide whether the hole moves, and the graph
  library's `sorted` whether toposort ordered every node. Each is a `Bool`
  and two answers.
- **A destructuring that can fail, the failure answering early.** The
  heap's `visiting` and `drained` take apart `heap.pop()`, where
  `Err(Empty)` ends the walk; `stepped` takes apart a `Result` whose `Err`
  passes straight back.

Seven definitions in the heap and graph libraries are of these shapes, and
each folds into its caller, in its caller's order. The heap's `drain`:

```
# Today
drain(heap, state, visit) -> visiting(heap.pop(), state, visit)

visiting : (Result({key: k, value: v, rest: Heap(k, v)}, [Empty]), s, (s, k, v) -> (s, List((k, v)))) -> s where k.cmp : (k, k) -> Order
visiting(Err(Empty), state, _) -> state
visiting(Ok({key, value, rest}), state, visit) -> (
  (next, added) = visit(state, key, value)
  grown = rest.push_all(added)
  grown.drain(next, visit)
)

# Proposed
drain(heap, state, visit) -> (
  popped = heap.pop()
  popped is Ok({key, value, rest}) else return state
  (next, added) = visit(state, key, value)
  grown = rest.push_all(added)
  grown.drain(next, visit)
)
```

and `cheaper`, with `either` gone:

```
cheaper(entries, left, count, fallback) -> (
  right = left + 1
  (left_key, _) = entries.get_or(left, fallback)
  (right_key, _) = entries.get_or(right, fallback)
  if right < count & right_key < left_key then right else left
)
```

An early answer closes off a case: once `popped is Ok(…) else return
state` has run, nothing below it has to think about an empty heap. Nested
branches instead hold the case open to the end of the `else`.

## Design

### Syntax earns its place by control flow

An operator or keyword is added only for what a method cannot do: leave a
clause early, or bring names into scope. Choosing a value is a method's
job. So `is` and `else` lines are syntax, and a default for a failed
`Result` stays `ok_or`.

### `is`

- **Syntax.** `expr is operand`, at a level of its own between `&` and the
  comparisons:

  ```
  infix levels, loosest first:
    |   ^   &   is   == != < <= > >=   + -   / % *
  ```

  `is` does not chain. Its right side is one operand, so the pattern ends
  at the next infix operator, and nothing after `is` parses differently
  from anywhere else.
- **Patterns** are made from the operand by `lines::pattern`, the function
  that makes a clause's head a pattern, so `is` takes everything a clause's
  parameter takes: constructors, literals, ranges, lists, records, tuples.
- **Or-patterns are parenthesized:** `acct is (Admin(name) | User(name))`.
  The parentheses group the operand as anywhere else, and `lines::pattern`
  turns the `|` inside into alternatives, as in a clause's head, where the
  argument's commas and `)` bound the pattern instead. Unparenthesized,
  `acct is Admin(name) | User(name)` is `(acct is Admin(name)) |
  User(name)`, and where the right of that `|` would be a pattern the
  message says to parenthesize.
- **Meaning.** `True` where the value matches. The value is worked out once.
- **Scope.** The names a pattern binds are seen where the `is` is known to
  have held: by the operands to its right across `&`, and, where the whole
  condition is such an `&` chain, by an `if`'s `then` branch, a guard's
  clause body, and the lines after an `else` line. Names bound under `|`,
  `^` or `!`, or inside an argument, are seen by nothing; a use of one is
  refused, the message naming the operator that hid it. This is C#'s rule
  for `is` and Rust's for `let` chains.
- **Shadowing.** A pattern may bind the name it tests, `step is Ok(step)`:
  bindings already shadow, and the `Result` becomes the value it held.
- **`=` against `is`.** A binding, `P = expr`, cannot fail. A pattern that
  can is refused, as today, the message now saying to write `expr is P else
  return …`. Which of the two a line uses says whether it can fail.

### `&` and `|` on `Bool`

On `Bool`, `&` evaluates its right side only where its left is `True`, and
`|` only where its left is `False`. On integers they stay bitwise, both
sides evaluated. One operator serves both because the type decides, not the
place the operator stands, and pure code cannot see the difference except
by not terminating:

```
even(n) -> n == 0 | odd(n - 1)
odd(n) -> n != 0 & even(n - 1)
expect even(4)
```

overflows the stack today, since `even(0)` still calls `odd`. `is` needs
the rule regardless: in `x is Some(n) & n > 0`, `n` does not exist where
the left fails. No program that answers today answers differently.

Built on 2026-10-04: emission matches on the left and works out the right
only in the arm that needs it.

### `if`

- **Syntax.** `expr = "if" expr "then" expr "else" expr | operand
  expr-tail`. An `if` takes everything after its `else`, so it begins an
  expression and is no operand: `1 + (if c then a else b)`, and `1 + if
  …` is refused with that advice. As an operand, what followed its `else`
  could belong to the branch or to the expression around it, and the
  grammar would no longer be LL(1). The `else` is required: an `if` always
  answers. `if a then b else if c then d else e` chains with no rule of its
  own.
- **Lines.** Where items are written, a line beginning `if` goes on with
  the line before, as a guard; a block holds no clauses, so there it begins
  an `if`. Lines beginning `then` and `else` go on with the line before.
- **`?` in a branch is refused.** A branch is a value; the advice is to
  answer a `Result` from both branches and ask `?` of the whole `if`.
- **`then` is required.** Without it, `if n -1 else 0` reads as `n - 1`.
- **Meaning.** The condition is a `Bool`; both branches have one type; the
  `then` branch sees what the condition bound. A branch is a value, never
  an exit: `else` lines exit.
- **A guard** stays `if expr`, unchanged in the grammar; an `is` in it binds
  for the clause's body as `then` does. Several conditions are joined with
  `&`.

  ```
  greeting(acct) if acct is (Admin(name) | User(name)) & name != "root" -> "Hello, {name}"
  greeting(_) -> "Hello"
  ```

Built on 2026-10-04, as above, with `Order.then` renamed `Order.or`, since
`then` became a keyword; `|` on orders now reads it.

### `else` lines

- **Syntax.** A block line, not its last, may be `expr else exit`, and an
  exit is `"return" expr`:

  ```
  statements = expr [ "=" expr NEWLINE statements
                    | "else" exit NEWLINE statements
                    | NEWLINE statements ] ;
  exit       = "return" expr ;
  ```
- **Meaning.** The condition is a `Bool`. Where it holds, the block goes on,
  with what it bound in scope for every line after. Where it fails,
  `return value` answers `value` from the clause or lambda the block is in,
  as `?` answers from there; its type is that clause's.
- **`return` is not an expression.** It is written only after `else`, so
  every early answer in a body sits at the start of an exit, after the
  condition it answers. An `if` branch, an argument and an operand cannot
  hold one.
- **One rule for three idioms.** `value is P else return x` is Rust's `let
  … else`; `test else return x` is Swift's `guard`; `value is P & test else
  return x` is both. `?` stays the short form for a `Result` whose `Err`
  passes through.

## Costs

- **Four keywords.** `is`, `then`, `else` and `return` can no longer be
  names. No program uses them as names.
- **Two orders.** `P = expr` puts the pattern first, `expr is P` the value.
  The order marks the meaning: one cannot fail, the other can.
- **Flow-sensitive scope.** Where a name is seen depends on `&` and on
  which line an `else` sits, not only on blocks and clauses. The rule is
  short, and each refusal names the operator that hid the name.
- **Parentheses for or-patterns** after `is`, which a clause's parameter
  does not need.
- **`&` reads two ways** to someone from C or Rust, who may expect both
  sides evaluated. The only programs that notice are ones that would
  otherwise not terminate.

## Alternatives considered

- **`pattern = expr else fallback`,** Rust's spelling. The pattern first
  hides that the line can fail until its end, and a second line form would
  be needed for a plain test.
- **`pattern = expr if guard else fallback`.** Reads as Python's
  conditional expression, `x = a if c else b`, a value for `x`.
- **A bare fallback, `c else x`.** Nothing in the line says it leaves the
  clause, and inside a loop the way out is not a value at all.
- **`if c return x`.** Familiar, but its condition is written the way the
  test fails, so it cannot bind: the names of `if !(v is Ok(e)) return x`
  would have to leak out of a `!`.
- **A general `return` expression,** so `if c then return x else …` and
  `f(return x)` work. Exits anywhere in an expression; one place for them
  is easier to find.
- **Comma conditions in guards,** `if a, P = e, b ->`. A rule of its own
  for guards, where `is` and `&` work everywhere.
- **`|` after `is` continuing the pattern,** so `x is A | B` needs no
  parentheses. Then `|` binds tighter than `&` after an `is` and looser
  everywhere else.
- **`x is A(n) | x is B(n)`.** A second spelling of an or-pattern, and a
  scoping rule for `|` as well as `&`.
- **Word operators, `and` and `or`,** as Roc has, leaving `|` to
  or-patterns alone. Removes the clash at its root, but changes every
  `Bool` expression in the corpus.
- **`&&` beside `&`.** C needs both because it has no `Bool`: truth is a
  nonzero integer, so an operator on integers cannot tell bits from truth.
  B before it chose by where the operator stood, which C's authors
  replaced. Rust keeps a `bool` `&` that evaluates both sides for their
  side effects; pure code has none.
- **`??` for a default,** as Roc has. It is `ok_or`: a value, not control
  flow.
- **An `if` without `else`.** An `if` would then sometimes answer nothing;
  `else` lines are that form, at block level.

## Implementation impact

1. **The lexer** gains `is`, `then`, `else` and `return`.
2. **The grammar.** `grammar.ebnf` and the tree-sitter grammar gain the
   `is` level, `if … then … else`, and `else` lines. The parser makes an
   `is`'s operand a pattern with `lines::pattern`, and lets an or-pattern
   stand there, which only a clause's parameters take today.
3. **Resolution** scopes an `is`'s names along `&` chains, into `then`
   branches, guard bodies and later block lines.
4. **Lowering.** `&` and `|` on `Bool` become branches. An `is` is a
   two-way decision tree, its failure `False`; an `if` and an `else` line
   are Barb's match on a `Bool`, or a decision tree where the condition
   holds an `is`.
5. **Programs.** The heap's `visiting`, `drained`, `climb_past`,
   `sink_past` and `either`, and the graph library's `stepped` and
   `sorted`, fold into their callers.
6. **Documentation.** `notes/syntax.md`, the standard library README, and
   the language tests.

## Testing

- `crates/faun/src/ebnf.rs` probes: `is` with an or-pattern in parentheses,
  `is` in a guard, an `else` line, an `else if` chain, and `if` as a
  binding's value.
- Refused cases, each with its `.err`: `x is A | B` unparenthesized, a name
  used where `|` hid it, an `else` line as a block's last line, `is`
  chained, a refutable `=` naming `is … else return`, `return` outside an
  `else` line, and an `if` with branches of two types.
- A running case across all three backends: `even` and `odd` above, the
  heap with its helpers folded, `is` as a plain value, a guard binding
  through `is`, and an `else` line in a lambda answering the lambda.

## Open questions

- **A comparison after `is`.** `x is 3 == y` compares a `Bool` with `y`. A
  dedicated message, or refused outright?

## Origin

Discussion of the [branching](branching.md) draft's further steps
(2026-10-03): guard conditions, `else` lines and a destructuring `if` were
three rules for one idea, a test that may bind. `is` makes it one operator,
and the forms around it follow. Writing `even` and `odd` to check the
short-circuit question showed `&` and `|` evaluate both sides today.
