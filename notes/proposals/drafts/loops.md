# Proposal: Loops and variables

- **Status:** Draft
- **Created:** 2026-10-04
- **Affects:** the lexer's tokens and keywords, `grammar.ebnf`, the parser,
  the tree-sitter grammar, name resolution, the checker, lowering, the
  standard library's lists, the graph library, the HTML library's `for`

---

## Summary

A function may declare variables, names written with a leading `$`, and
loop over them with `for`, `while` and `loop`. A variable is rebound only
inside the function that declares it; a loop carries every variable it
rebinds into its next round and out of it. A line that is only a method
chain on a variable updates it: `$order.append(node)` is `$order =
$order.append(node)`. A pattern may bind into a variable. `else continue`
and `else break` leave a round or a loop. Each loop compiles to a local
recursive function whose parameters are its variables, so a function with
loops is as pure as one without.

| Form               | Today                     | Proposed               |
| ------------------ | ------------------------- | ---------------------- |
| Loop state         | a record type of its own  | `$names`               |
| Walk a list        | a fold and a visit helper | `for P in list ( … )`  |
| Worklist           | `drain_stack` and a visit | `while $s is [x, *$s]` |
| Skip an item       | a helper's guarded clause | `c else continue`      |
| Update a value     | `next = put(state, …)`    | `$state.put(…)`        |
| Unconditional loop | a recursive helper        | `loop ( … )`           |

## Motivation

Graph algorithms are worklists: take an item, update two or three tables,
add to the worklist, until it is empty. Faun writes each as a fold over a
state record, and the graph library shows what that costs. `toposort.fn`
is 48 lines for Kahn's algorithm:

- **A record type that exists only to hold loop state:** `Walk`, `Found`,
  `Kahn` and `Leaving`, one per algorithm.
- **A visit helper that takes the state apart and builds it again:**
  `enter`, `connected`, `take`, `release`.
- **The graph passed by hand** to every helper, since none can see it.
- **A fold inside a fold** where the algorithm has a loop inside a loop,
  each lambda threading its own record.

Python writes the same algorithm in 15 lines, in the textbook's order:

```python
def toposort(graph):
    count = graph.node_count()
    degrees = [graph.in_degree(n) for n in range(count)]
    ready = [n for n in range(count) if degrees[n] == 0]
    order = []
    while ready:
        node = ready.pop()
        order.append(node)
        for edge in graph.edges_from(node):
            degrees[edge.target] -= 1
            if degrees[edge.target] == 0:
                ready.append(edge.target)
    if len(order) != count:
        raise Cycle
    return order
```

With this proposal Faun writes it in 15:

```
toposort(graph) -> (
  nodes = List.range(graph.node_count())
  $degrees = nodes.map(|node| graph.in_degree(node))
  $ready = nodes.filter(|node| $degrees.get_or(node, 0) == 0)
  $order = []
  while $ready is [node, *$ready] (
    $order.append(node)
    for {target, *} in graph.edges_from(node) (
      $degrees.update(target, |degree| degree - 1)
      $degrees.get_or(target, 0) == 0 else continue
      $ready.prepend(target)
    )
  )
  $order.len() == nodes.len() else return Err(Cycle)
  Ok($order)
)
```

Taking the next item is one line where Python's is two; the cycle check is
one line where Python's is two; the edge's target is taken apart once,
where Python reads `edge.target` three times. Faun spends three lines on
closing parentheses.

### What it keeps that Python gives up

The spelling is Python's; what a reader may assume is not.

- **A call cannot change what it is given.** In Python, `f(order)` may
  append to `order`. Here only a line beginning `$order` changes `$order`.
- **No aliasing.** `snapshot = $order` stays a snapshot when `$order`
  changes; Python's `snapshot = order` does not. No default argument is
  shared between calls, and a lambda captures values, not a loop's
  variable.
- **The function stays pure.** No lambda rebinds a variable, and each loop
  is a recursive function underneath, so `toposort` is a function of
  `graph` alone, as it is today. Effects stay marked by `!`.
- **The failures are checked.** `while $ready is [node, *$ready]` cannot
  take from an empty list; `get_or` cannot raise; `Err(Cycle)` is in the
  signature, where Python's `raise Cycle` is in no signature at all.

A list nothing else holds is already written in place, so the updates cost
what Python's mutation costs.

## Design

### Variables

- **A variable is a name with a leading `$`**, a token of its own, as an
  effectful name ends in `!`. The mark is on the name because changing is
  a property of the name for its whole life: a reader meeting `$degrees`
  partway down a loop knows it may differ from when it was last seen.
- **The first binding of a `$` name in a function declares it;** each later
  one rebinds it. There is no `var`: the `$` says what it would.
- **A variable is rebound only in the function that declares it,** the
  clause or lambda whose body holds its declaration. A lambda inside reads
  it and cannot rebind it. This is what lets a loop compile to a function
  of its variables, and Roc's rule for its `var`s.
- **A variable keeps its type.** Rebinding it to a value of another type is
  refused.
- **No variables at the top level,** and no parameter is a variable.
- **A variable is never shadowed.** A `$` name bound again in the same
  function rebinds; plain names shadow as they do today.

### Changing a variable

Every line that changes `$x` starts with `$x`, or binds it in a pattern:

- **`$x = expr`** rebinds it.
- **A line that is only a method chain starting at `$x`** rebinds it to the
  chain's result, which must have `$x`'s type. `$order.append(node)` is
  `$order = $order.append(node)`; `$order.append(a).append(b)` takes both.
  A line that goes on after the chain, `$degrees.get_or(t, 0) == 0 else
  continue`, reads `$degrees` and changes nothing.
- **A pattern may bind into an existing variable:** `(n, $rng) =
  $rng.int(0, 24)`, `while $ready is [node, *$ready]`. A name with `$` in a
  pattern rebinds; one without is a fresh name, as today.
- **A call inside an expression is a value.** `y = $order.append(node)`
  binds `y` and leaves `$order` as it was.
- **A pure call that is a whole line and changes nothing is refused:** its
  answer would be thrown away. `$order.len()` alone on a line is refused,
  its answer a `Nat` where `$order` is a `List(Nat)`.

The rule is syntactic: whether a line updates is read from the line, never
from the method's signature, which only has to allow it.

### Loops

```
loop-line = "for" operand "in" expr "(" loop-body ")"
          | "while" expr "(" loop-body ")"
          | "loop" "(" loop-body ")" ;
```

- **`for P in list ( … )`** runs its body once for each element, in order,
  `P` a pattern that cannot fail, binding fresh names each round. It walks
  a `List`; a range is `List.range`.
- **`while c ( … )`** runs while `c` holds. `c` may be an `is`, whose names
  the body sees: `while $ready is [node, *$ready]` takes the head off on
  each round.
- **`loop ( … )`** runs until an `else break` or `else return` leaves it.
  It writes the loop whose test is partway through, as in reading until
  input ends.
- **The space before the body's `(` matters,** as anywhere: `while
  done(` is a call to `done`. The formatter writes the space.
- **A loop is a line of a block,** not an expression, and not the block's
  last line, which answers. What a loop computes is left in its variables.
- **A loop's body is block lines with no answer:** bindings, updates,
  `else` lines and loops.

### Leaving a round or a loop

`continue` and `break` are exits, written only after `else`, as `return`
is:

- **`c else continue`** ends the round where `c` fails; the loop goes on.
- **`c else break`** ends the loop where `c` fails; the line after it runs.
- **`c else return x`** answers `x` from the function, from inside any
  loop.

Each applies to the innermost loop. Neither is an expression; neither
stands outside a loop.

### Nesting

Loops nest two deep. A third is refused, and so is a lambda of more than
one line inside a loop's body: what goes deeper is a named step, a helper.
Every body is then at most two levels of indentation below its
function's, and Kahn's algorithm and Dijkstra's keep their textbook shape,
an inner loop over a node's edges.

### Meaning

Each loop is a local recursive function, its parameters the variables its
body rebinds and its answer their values when it ends. `continue` calls
it for the next round; `break` answers; a `return` inside answers a tag
the code after the loop checks. Variables a loop only reads are captured,
as a lambda captures. None of this is visible: a function with loops
answers what the same function written with folds answers.

## Costs

- **The sigil.** `$` on every mention of a variable. It is the price of
  seeing, at each use, that the value may have changed.
- **Two ways to fold.** `for` and `fold` both walk a list. `fold` stays the
  form for an expression of one value; a loop is for several variables, or
  a body of several steps. Style holds this, not the grammar.
- **Six keywords.** `for`, `in`, `while`, `loop`, `break` and `continue`.
  The HTML library's `for` attribute must be renamed.
- **A line starting `$x.` may not change `$x`,** where it goes on after the
  call. A reader sees the difference at the line's end.
- **`y = $x.append(1)` leaves `$x` unchanged,** which someone from Python
  may not expect. Inside an expression, a value is the only reading.
- **Order matters in a body.** Moving a line past an update of the
  variable it reads changes what it reads, as in any language with
  variables.

## Alternatives considered

- **Shadowing alone,** with a loop carrying any name it rebinds. No sigil,
  but whether a body's `seen = …` is a step or the loop's state is
  invisible, and a pattern cannot say whether it binds a fresh name or the
  loop's.
- **A declaration keyword,** `var x` or Lean's `let mut x`, with plain uses.
  The mark is then pages from where a reader meets the name. Roc writes
  both, `var $x`; the `$` alone says it.
- **An update operator,** `$order .= append(node)`, after `+=`. It marks
  the act at the line, but every changing line already starts with `$x`,
  and a whole line that is a pure call has no other meaning to keep apart.
- **`:=` for rebinding,** as Lean has. A second binding operator, where `$`
  already says which names rebind.
- **Writing back from any method call** of the right shape, everywhere.
  Expressions would change their receivers, and whether `xs.map(f)` writes
  back would hang on whether `f` keeps the element type.
- **Writing back from a plain function's first argument,** `put($degrees,
  t, 0)` on a line. The `$` is then not at the line's start; methods are
  the common case, and `$degrees = put($degrees, t, 0)` is plain.
- **Compound assignment,** `$count += 1`. Left out until counting loops ask
  for it; it would keep every changing line starting with `$x`.
- **Rebinding inside lambdas,** as Python and JavaScript allow. A lambda
  could then change its caller's state, and a loop would no longer be a
  function of its variables.
- **One level of loops.** Kahn's algorithm's inner loop would become a
  helper answering two variables at once, `($degrees, $ready)`; two levels
  keep it where the textbook has it.
- **`while` only, no `loop`.** Reading until input ends then reads before
  the loop and again at the end of its body.
- **`loop` only, no `while`.** `while c ( … )` is `loop ( c else break …
  )`, a construct fewer for a line more on every loop.

## Implementation impact

1. **The lexer** gains `$` names as a token kind, and the keywords `for`,
   `in`, `while`, `loop`, `break` and `continue`.
2. **The grammar.** `grammar.ebnf` and the tree-sitter grammar gain loop
   lines and `continue` and `break` as exits.
3. **Resolution** tracks each variable's declaring function, refuses a
   rebinding from a lambda, and marks each loop's variables.
4. **The checker** holds a variable to its type, refuses a whole-line pure
   call that changes nothing, and checks a `for` pattern cannot fail.
5. **Lowering** makes each loop a local recursive function of its
   variables, as `callbacks.rs` lifts a lambda.
6. **The standard library** gains `List.update(list, index, f)`, total,
   leaving a list without that index as it was. A method that can fail,
   such as `set`, answers a `Result` and cannot update a variable.
7. **Programs.** The graph library's walks, components and toposort, and
   the heap's sift loops, written with loops; the HTML library's `for`
   renamed.
8. **Documentation.** `notes/syntax.md`, the standard library README, and
   the language tests.

## Testing

- `crates/faun/src/ebnf.rs` probes: each loop form, loops two deep, an
  update line, a chain update, a pattern binding into a variable, and
  `else continue` and `else break`.
- Refused cases, each with its `.err`: a variable rebound in a lambda, a
  variable retyped, a whole-line pure call that changes nothing, a loop
  three deep, a multi-line lambda in a loop, `break` outside a loop, a `$`
  name at the top level, and a refutable `for` pattern.
- A running case across all three backends: toposort, a depth-first walk,
  a loop with `return` from inside, and a `loop` that reads until a list
  is empty, each against the fold it replaces.

## Open questions

- **`while` and `loop` both,** or one?
- **What `for` walks.** A `List` only, or anything with a `fold`: a `Map`'s
  entries, a `Set`?
- **A variable as a parameter,** `f($acc, x)`, rebinding the caller's? It
  would need the caller to pass a variable, and is left out.

## Origin

Comparing the graph library's walks and toposort with their Python
(2026-10-04), after the [conditions](conditions.md) draft removed the
guard helpers, left the threading of state through folds as the largest
difference. Roc's newer compiler (`docs/mini-tutorial-new-compiler.md` in
roc-lang/roc) writes `var $x`, `for` and `while`, and confines a `var` to
its declaring function; this draft takes the sigil and that rule, and
drops `var`.
