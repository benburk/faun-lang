# Proposal: Loops

- **Status:** Draft
- **Created:** 2026-10-04
- **Affects:** the lexer's keywords, `grammar.ebnf`, the parser, the
  tree-sitter grammar, name resolution, the checker, lowering, the
  standard library's lists, the graph library, the HTML library's `for`

---

## Summary

A body may loop with `for`, `while` and `loop`. A name assigned in a
loop's body, as the [conditions](conditions.md) draft assigns, carries into
its next round and out of it. `else continue` and `else break` leave a
round or a loop. Each loop compiles to a recursive function whose
parameters are the names it assigns, so a function with loops is as pure
as one without.

| Form               | Today                     | Proposed                   |
| ------------------ | ------------------------- | -------------------------- |
| Loop state         | a record type of its own  | names the loop assigns     |
| Walk a list        | a fold and a visit helper | `for P in list ( … )`      |
| Worklist           | `drain_stack` and a visit | `while s is [x, *t] ( … )` |
| Skip an item       | a helper's guarded clause | `c else continue`          |
| Update a value     | `next = put(state, …)`    | `state = state.put(…)`     |
| Unconditional loop | a recursive helper        | `loop ( … )`               |

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

With this proposal Faun writes it in 16:

```
toposort(graph) -> (
  nodes = List.range(graph.node_count())
  degrees = nodes.map(|node| graph.in_degree(node))
  ready = nodes.filter(|node| degrees.get_or(node, 0) == 0)
  order = []
  while ready is [node, *rest] (
    ready = rest
    order = order.append(node)
    for {target, *} in graph.edges_from(node) (
      degrees = degrees.update(target, |degree| degree - 1)
      degrees.get_or(target, 0) == 0 else continue
      ready = ready.prepend(target)
    )
  )
  order.len() == nodes.len() else return Err(Cycle)
  Ok(order)
)
```

The cycle check is one line where Python's is two; the edge's target is
taken apart once, where Python reads `edge.target` three times. Faun
spends three lines on closing parentheses and one on taking the rest of
the worklist.

### What it keeps that Python gives up

The spelling is Python's; what a reader may assume is not.

- **A call cannot change what it is given.** In Python, `f(order)` may
  append to `order`. Here only a line `order = …` changes `order`.
- **No aliasing.** `snapshot = order` stays a snapshot when `order`
  changes; Python's `snapshot = order` does not. No default argument is
  shared between calls, and a lambda captures values, not a loop's names.
- **The function stays pure.** No lambda assigns a name of its body, and
  each loop is a recursive function underneath, so `toposort` is a function
  of `graph` alone, as it is today. Effects stay marked by `!`.
- **The failures are checked.** `while ready is [node, *rest]` cannot take
  from an empty list; `get_or` cannot raise; `Err(Cycle)` is in the
  signature, where Python's `raise Cycle` is in no signature at all.

A list nothing else holds is already written in place, so the updates cost
what Python's mutation costs.

## Design

### Names a loop changes

Assignment is the conditions draft's: `name = value` on a name in scope
changes it, keeping its type, and a lambda assigns only its own names. A
loop adds:

- **A name assigned in a loop's body carries.** Its next round sees the
  value the last one left, and the lines after the loop see the value the
  loop ended with.
- **A name declared in a loop's body is the round's.** It is new each round
  and unseen after the loop.
- **Patterns declare,** so a worklist takes its head into a new name and
  assigns its rest: `while ready is [node, *rest] ( ready = rest …`.

### Loops

```
loop-line = "for" operand "in" expr "(" loop-body ")"
          | "while" expr "(" loop-body ")"
          | "loop" "(" loop-body ")" ;
```

- **`for P in list ( … )`** runs its body once for each element, in order,
  `P` a pattern that cannot fail, binding new names each round. It walks a
  `List`; a range is `List.range`.
- **`while c ( … )`** runs while `c` holds. `c` may be an `is`, whose names
  the body sees.
- **`loop ( … )`** runs until an `else break` or `else return` leaves it.
  It writes the loop whose test is partway through, as in reading until
  input ends.
- **The space before the body's `(` matters,** as anywhere: `while
  done(` is a call to `done`. The formatter writes the space.
- **A loop is a line of a block,** not an expression, and not the block's
  last line, which answers. What a loop computes is left in the names it
  assigned.
- **A loop's body is block lines with no answer:** bindings, assignments,
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

Each loop is a recursive function, its parameters the names its body
assigns and its answer their values when it ends; the lines after it are
the join point it answers to. `continue` calls the loop for the next round;
`break` and the loop's end call the join point; a `return` inside answers
the function. Names a loop only reads are passed in, as a lambda captures.
None of this is visible: a function with loops answers what the same
function written with folds answers.

## Costs

- **Every change is spelled whole.** `order = order.append(node)` where
  Python writes `order.append(node)`. The line says what changes at its
  start.
- **No mark at the use.** A reader meeting `degrees` in a loop's body must
  know whether the loop assigns it.
- **Two ways to fold.** `for` and `fold` both walk a list. `fold` stays the
  form for an expression of one value; a loop is for several names, or a
  body of several steps. Style holds this, not the grammar.
- **Six keywords.** `for`, `in`, `while`, `loop`, `break` and `continue`.
  The HTML library's `for` attribute must be renamed.
- **The worklist's extra line.** A pattern declares, so the rest of the
  list is a new name assigned back: `ready = rest`.
- **Order matters in a body.** Moving a line past an assignment of the name
  it reads changes what it reads, as in any language with variables.

## Alternatives considered

- **`$` variables,** the draft's first design: a sigil on every mention of
  a name that changes, write-back from a line that is only a method chain,
  `$order.append(node)`, and patterns binding into variables, `while $ready
  is [node, *$ready]`. It marked change at each use, at the price of a
  token on every mention, a write-back rule read from the line's end, and a
  second kind of name.
- **Shadowing, with a loop carrying any name it binds again.** A branch's
  assignment would vanish after the branch; assignment is the same rule for
  branches and loops.
- **A declaration keyword,** `var x` or Lean's `let mut x`. A mark pages
  from where a reader meets the name, which says less than reading the
  loop's lines.
- **An update operator,** `order .= append(node)`, after `+=`. A second
  binding operator for what `order = order.append(node)` says.
- **Compound assignment,** `count += 1`. Left out until counting loops ask
  for it.
- **Assigning inside lambdas,** as Python and JavaScript allow. A lambda
  could then change its caller's state, and a loop would no longer be a
  function of its names.
- **One level of loops.** Kahn's algorithm's inner loop would become a
  helper answering two names at once, `(degrees, ready)`; two levels keep
  it where the textbook has it.
- **`while` only, no `loop`.** Reading until input ends then reads before
  the loop and again at the end of its body.
- **`loop` only, no `while`.** `while c ( … )` is `loop ( c else break …
  )`, a construct fewer for a line more on every loop.

## Implementation impact

1. **The lexer** gains the keywords `for`, `in`, `while`, `loop`, `break`
   and `continue`.
2. **The grammar.** `grammar.ebnf` and the tree-sitter grammar gain loop
   lines and `continue` and `break` as exits.
3. **Resolution** records, for each loop, the names its body assigns, and
   refuses `continue` and `break` outside a loop.
4. **The checker** checks a `for` pattern cannot fail.
5. **Lowering** makes each loop a recursive function of the names it
   assigns, and the lines after it a join point, as the conditions draft's
   branches are.
6. **The standard library** gains `List.update(list, index, f)`, total,
   leaving a list without that index as it was.
7. **Programs.** The graph library's walks, components and toposort, and
   the heap's sift loops, written with loops; the HTML library's `for`
   renamed.
8. **Documentation.** `notes/syntax.md`, the standard library README, and
   the language tests.

## Testing

- `crates/faun/src/ebnf.rs` probes: each loop form, loops two deep, and
  `else continue` and `else break`.
- Refused cases, each with its `.err`: a loop three deep, a multi-line
  lambda in a loop, `break` outside a loop, and a refutable `for` pattern.
- A running case across all three backends: toposort, a depth-first walk,
  a loop with `return` from inside, and a `loop` that reads until a list
  is empty, each against the fold it replaces.

## Open questions

- **`while` and `loop` both,** or one?
- **What `for` walks.** A `List` only, or anything with a `fold`: a `Map`'s
  entries, a `Set`?
- **Compound assignment,** `count += 1`, once counting loops are written.

## Origin

Comparing the graph library's walks and toposort with their Python
(2026-10-04), after the [conditions](conditions.md) draft removed the
guard helpers, left the threading of state through folds as the largest
difference. Roc's newer compiler (`docs/mini-tutorial-new-compiler.md` in
roc-lang/roc) writes `var $x`, `for` and `while`, and confines a `var` to
its declaring function; this draft first took the sigil and that rule.
On 2026-10-07 the sigil and write-back gave way to plain assignment, which
the conditions draft makes the rule for every name.
