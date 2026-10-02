# Proposal: Branching on a computed value

- **Status:** Draft
- **Created:** 2026-10-01
- **Affects:** the lexer's keywords, `grammar.ebnf`, the parser, the
  tree-sitter grammar, pattern compiling, every helper definition that
  exists only to take a computed value apart

---

## Summary

A Faun body cannot branch on a value it computed: only a definition's
clauses take values apart, and only its parameters. So every such branch is
a definition of its own, with a signature. This proposes a `when`
expression: a value, then clauses in parentheses, written as a definition's
clauses are.

| Form                       | Today              | Proposed                 |
| -------------------------- | ------------------ | ------------------------ |
| Branch on a parameter      | clauses            | unchanged                |
| Branch on a computed value | a helper's clauses | `when value ( clauses )` |
| Arms                       | —                  | a line each              |
| Guards, `?`, blocks        | —                  | as in a clause           |

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
  step = settled.get_or(node, Err(Unreachable))?
  walked = [node, *route]
  when step.from (
    from if from == node -> Ok(walked)
    from -> back(settled, from, walked)
  )
)
```

## Motivation

Taking a computed value apart means writing a function for it. In the graph
and heap libraries alone, eight definitions exist only for that:

- `visiting` and `drained` take apart `heap.pop()`
- `stepped` takes apart the step a path walks back through
- `sorted` takes apart whether toposort ordered every node
- `climb_past`, `sink_past`, `cheaper` and `either` take apart the heap's
  comparisons

They share the same signs:

- **The name is made up.** `stepped`, `visiting`, `drained` and `either`
  name no idea of their own; each is the second half of the definition that
  calls it. The grammar's claim, that a forced helper is a named step, does
  not hold for them.
- **The signature is longer than the body.** `visiting` and `drained` each
  repeat a `Result({key, value, rest}, [Empty])` and a `where` list around
  two lines of logic.
- **Context is passed by hand.** `stepped` takes `settled`, `node` and
  `route` only because it cannot see them; `sink_past` takes six
  parameters.
- **One step is read across several definitions.** The heap's sift-down is
  one loop with one comparison in any textbook, and here is `sink`,
  `cheaper`, `either` and `sink_past`.

Not every helper is of this kind. A guard on a definition's own parameters,
`enter`'s "seen before, so nothing" or `release`'s "this was its last edge
in", is an early return with a name, and reads better as clauses than it
would as a branch inside a body. `root`, `joined`, `gathered` and
`drain_stack` are steps any language would name. This proposal leaves them
as they are.

## Design

- **Syntax.** `when` an expression, then its arms in plain parentheses:

  ```
  untyped-primary  += "when" expr "(" arms ")" ;
  arms              = expr clause [ NEWLINE [ arms ] ] ;
  ```

  An arm is a clause line, `pattern [if guard] -> expr`, and `clause` is
  the rule a definition's clauses already use. After the value, a plain `(`
  cannot go on with an expression, so it opens the arms, and the grammar
  stays LL(1).
- **Arms are parted by line ends,** as a block's lines and a method block's
  lines are, and never by commas. The lexer already makes a line end inside
  a plain `(`, and a line already runs on after `->`, so an arm's body may
  go on to the next line. A two-armed branch on one line, on a `Result` or a
  `Bool`, is usually better as a method call, and one arm to a line is one
  thing for the formatter to do.
- **Arms need delimiters.** Without the closing `)`, a `when` at the end of
  a top-level body would take the next definition's clauses as arms, which
  have the same tokens; inside a block, a line after the arms could be the
  next statement or another arm until an `->` arrives, which is not LL(1);
  and a `when` inside another would take the outer one's later arms.
- **Patterns** are made from expressions as a clause's head is, once the
  `->` or `if` says the line is an arm. A name an arm binds is seen by its
  guard and its body, and nowhere else.
- **Meaning.** The value is worked out once, and the first arm whose pattern
  matches and whose guard holds gives the answer. The arms are checked for
  exhaustiveness as a definition's clauses are, every arm's body has one
  type, and pattern compiling makes them a decision tree as it does
  clauses.
- **`?`** in an arm answers early from the clause or lambda the `when` is
  written in, as in a block: a `when` is not a function.
- **Where it goes:** anywhere an expression goes, with no rule of its own: a
  clause's body, a binding's value, a lambda's body, an argument, a guard,
  an arm.
- **The keyword is `when`,** after Kotlin's `when (x) { … }`. `match` is
  left free as a name, which parsers, regular expressions and templates
  want. Faun's guards are `if`, so `when` does not read as a guard, as it
  does in Elixir, F# and OCaml. No program uses `when` as a name today.
- **The space before `(` matters.** `when x(` is a call to `x`, as
  anywhere: the lexer reads a `(` straight after an operand as a call's.
  The formatter always writes the space, and where a `when`'s value is a
  call followed by anything but `(`, the parser says that is the likely
  mistake.
- **An unclosed `when`** runs on through every clause after it, since a
  top-level clause reads as an arm. It ends at a signature's `:`, an
  `expect`, a directive or the end of the file, and is told at the `when`'s
  `(`. The blocks errata tells an unclosed block where a line in it runs
  into an `->`; that still holds for an `->` anywhere but directly inside a
  `when`'s parentheses.
- **Style.** The `(` ends the line holding `when`, each arm is a line
  indented one step, and the `)` stands at the indentation of the line that
  opened it, as a block's does.

## Costs

- **Two ways to take a parameter apart.** `f(x) -> when x (…)` does what
  clauses do, and nothing in the grammar says which to write. See the open
  questions.
- **Nesting.** A `when` may hold another, and languages with match
  expressions, Gleam, Elixir and OCaml, tend to nest them. Binding a
  `when`'s answer to a name keeps a body flat; the grammar does not insist.
- **Less pressure to name each step.** A helper that was a real step may be
  folded into its caller where it should have stayed. Style and review hold
  this, not the grammar.
- **A keyword.** `when` can no longer be a name.
- **An unclosed `when` reaches far,** further than an unclosed block, above.

## Alternatives considered

- **Keep the current grammar.** The cost is visible and bounded, a helper
  and its signature for each branch on a computed value, but it falls
  hardest on data structures, where most of a step is comparisons partway
  through a loop: five of the heap's definitions exist only for that.
- **`match` as the keyword.** Familiar from Rust, Scala and Python, and a
  name programs want more than `when`.
- **A postfix form with no keyword,** reusing the method block's token:
  `heap.pop().( Err(Empty) -> …, Ok(e) -> … )`. A type's `.( )` holds its
  definitions' clauses, and an expression's would hold clauses applied to
  it, so it adds no keyword or token. It reads as cryptic, and its gain is
  chaining, which the habit of naming each step works against.
- **Lambdas of more than one clause,** handed to a method:
  `popped.match(|Err(Empty)| -> …, |Ok(e)| -> …)`. Keeps one construct for
  branching in name, but means what a `when` means with a heavier spelling.
- **Commas between arms,** for one-line branches. They would parse, since an
  arm's body holds no bare comma, but blocks and method blocks take line
  ends only, and the one-line case is better served by a method.
- **No separator between arms.** Almost parses, since nothing goes on from
  an arm's body but the next arm, except a pattern starting with `-`:
  `n -> a -1 -> b` reads as a subtraction.
- **`if` expressions.** `if c then a else b` is a `when` on a `Bool`, and
  many of the helpers above are two-way tests on a comparison: `sorted`,
  `either`, `climb_past`. Left for after `when`, to see whether `when` with
  a guard is enough.
- **Lambdas bound to names,** `walk = |stack, walked| …`, called or passed
  but never stored, lifted to a top-level definition with what they read as
  extra parameters. They would end the passing of context by hand, as
  Haskell's `where` and Erlang's named funs do. A separate proposal.
- **Every function a lambda,** `main = |host| …`. Costs a level of nesting
  in every definition of several clauses, and makes functions look like
  values, which Faun's are not.

## Implementation impact

1. **The lexer** gains the keyword `when`.
2. **The grammar.** `grammar.ebnf` and the tree-sitter grammar gain `when`
   and its arms; the parser reads arms with the clause parsing it has.
3. **Pattern compiling** makes a `when` a decision tree, as it does a
   definition's clauses; Barb already has a match term, so lowering is
   mostly reuse. Exhaustiveness is checked as for clauses.
4. **Programs.** The helpers listed above fold back into the definitions
   that call them, in the graph and heap libraries first.
5. **Documentation.** `notes/syntax.md`, the standard library README, and
   the language tests.

## Testing

- `crates/faun/src/ebnf.rs` holds `grammar.ebnf` to the parser, with probes
  for: a `when` as the last line of a top-level body, a `when` as a
  binding's value, one inside another, an arm whose body is a block, a
  guard on an arm, and an unclosed `when`.
- The parser's own tests and tree-sitter's refused corpus: an unclosed
  `when`, told at its `(`; `when f(x)` with no arms.
- Refused cases, each with its `.err`: arms that miss a case, and arms of
  two types.
- A running case in the language tests: a `when` on a `Result`, a guard, a
  nested `when`, a `?` in an arm answering the clause, and a `when` in a
  lambda's body. Across all three backends.

## Further steps

Discussed alongside `when`, not part of it, and recorded for when this
draft is taken up again (2026-10-02). The aim behind them: one way to write
each thing, and the classic algorithms as short and plain as their Python.

- **Guard conditions.** A guard becomes conditions parted by commas, each a
  `Bool` or a binding, `pattern = expr`, whose names the later conditions
  and the body see; any that fails falls to the next clause or arm, which
  is Haskell's pattern guards and Rust's `if let` chains with the next arm
  as their shared `else`. One change to `clause`, so definitions and `when`
  arms both get it:

  ```
  clause     = [ "if" conditions ] "->" expr ;
  conditions = expr [ "=" expr ] [ "," conditions ] ;
  ```

  The heap's `climb_past` folds into `climb`:

  ```
  climb(entries, hole, (key, value)) if hole > 0,
    above = (hole - 1) / 2,
    (parent_key, parent) = entries.get_or(above, (key, value)),
    key < parent_key ->
    climb(put(entries, hole, (parent_key, parent)), above, (key, value))
  climb(entries, hole, entry) -> put(entries, hole, entry)
  ```

- **`else` lines.** Any line of a block may end `else fallback`: a binding
  whose pattern fails, Rust's `let … else`, or a `Bool` that is false,
  Swift's `guard`, answers the fallback from the clause or lambda, as `?`
  does. A binding that can fail is refused today, and would be refused
  without its `else`, the message saying so. `?` stays as the short form
  for a `Result`. Lines stack, so a body stays flat; the heap's `visiting`
  and `drained` fold into `drain` and `empty_onto`:

  ```
  drain(heap, state, visit) -> (
    Ok({key, value, rest}) = heap.pop() else state
    (next, added) = visit(state, key, value)
    grown = rest.push_all(added)
    grown.drain(next, visit)
  )
  ```

  Answering the innermost block instead would make a block Rust's `if let`
  expression, but `?` and `else` would then leave from different places.

- **A destructuring `if`,** `if conditions then a else b`, taking the
  conditions a guard takes. Left until `when`, guard conditions and `else`
  lines are in, which cover most of what it would.

- **One way to write each kind of definition.** At the top level, a
  function with parameters is clauses, and a value is a binding, `pi =
  3.14159`, worked out once, in place of a definition of no parameters.
  In a body, a local function is a binding of a lambda, `walk = |stack|
  …`, which may call itself. Clauses stay the top-level form: a third of
  the corpus's 1,974 definitions have several clauses, each of which would
  become a `when` on a tuple of its parameters if a lambda were the only
  form, and a name bound to a lambda reads as a value, which a function is
  not.

- **Local lambdas need no lambda sets** if what is bound must be a lambda
  written there or a named function: each name then stands for one known
  function, and `callbacks.rs` lifts it as it lifts a lambda passed to a
  call. Lambda sets come in only where a name could hold one of several
  functions, or a function is stored in data.

- **Functions in data** would cost lambda sets, and every call being a
  static edge, which `callbacks.rs` relies on. Equality, hashing and
  ordering are no obstacle: a type holding a function answers none of
  them, as in Rust, Haskell and Roc. Nothing written so far wants it.

- **Loops that rebind,** after Lean 4's `do` notation: local mutable names,
  `for`, `break` and `continue`, lowered to folds that carry what they
  rebind. With the rest above, `connected` comes out at Python's length and
  in its order; what is still longer than Python is threading several
  tables through nested loops, Dijkstra's relaxation, union-find, dynamic
  programming over a grid, and only this closes it. A list nothing else
  holds is already written in place, so it would cost no speed.

## Open questions

- **How much does it cost now?** Count, across the ported programs and the
  libraries, the definitions that exist only to take a computed value
  apart, against those that take apart their parameters.
- **A `when` on a bare parameter.** Refuse a body that is only a `when` on
  one of its parameters, saying to write clauses, so parameters are taken
  apart one way? Or leave it to style?

## Origin

Comparing the standalone components example with the Python cookbook's
`connected`, after the termination check went and its step limits with it,
left the helper definitions as the largest difference that was syntax
rather than the absence of mutation. Writing the graph library's
`DiGraph` and `UnGraph`, and the heap under its Dijkstra, showed where the
helpers fall: few in the algorithms, which are a worklist and a heap, and
most in the heap, whose steps are comparisons partway through a loop.
