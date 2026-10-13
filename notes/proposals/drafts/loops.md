# Proposal: Loops

- **Status:** Draft
- **Created:** 2026-10-04
- **Affects:** the lexer's keywords, `grammar.ebnf`, the parser, the
  tree-sitter grammar, name resolution, the checker, lowering, the
  standard library's lists, the graph library, the HTML library's `for`

---

## Summary

A body may loop with `for`, `while` and `loop`. A name bound before a loop
and again in its body, as the [conditions](conditions.md) draft's `=`
binds, carries into its next round and out of it. Leaving lines leave a
round or a loop: `if c continue` and `if c break` where `c` holds, `c else
continue` and `c else break` where it fails. Each loop compiles to a
recursive function whose parameters are the names it binds again, so a
function with loops is as pure as one without.

| Form               | Today                     | Proposed                   |
| ------------------ | ------------------------- | -------------------------- |
| Loop state         | a record type of its own  | names the loop assigns     |
| Walk a list        | a fold and a visit helper | `for P in list ( … )`      |
| Worklist           | `drain_stack` and a visit | `while s is [x, *t] ( … )` |
| Skip an item       | a helper's guarded clause | `if c continue`            |
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

With this proposal Faun writes it in 15, counting the in-degrees itself, so
the graph answers only `node_count` and `neighbors`:

```
toposort(graph) -> (
  nodes = List.range(graph.node_count())
  degrees = Map.counted(nodes.flat_map(|node| graph.neighbors(node)))
  ready = nodes.filter(|node| degrees.get_or(node, 0) == 0)
  order = []
  while ready is [node, *ready] do (
    order = order.append(node)
    for target in graph.neighbors(node) do (
      degrees = degrees.update(target, |degree| degree - 1)
      if degrees.get_or(target, 0) > 0 continue
      ready = ready.prepend(target)
    )
  )
  if order.len() == nodes.len() then Ok(order) else Err(Cycle)
)
```

The in-degrees are one line, `Map.counted` as Python's `Counter`, where a
Python that counts them itself spends four; the cycle check is one line
where Python's is two. Faun spends three lines on closing parentheses and
one on taking the rest of the worklist, and a step is written whole:
`degrees = degrees.update(target, |degree| degree - 1)` where Python
writes `degrees[target] -= 1`.

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
- **The failures are checked.** `while ready is [node, *ready]` cannot take
  from an empty list; `get_or` cannot raise; `Err(Cycle)` is in the
  signature, where Python's `raise Cycle` is in no signature at all.

A list nothing else holds is already written in place, so the updates cost
what Python's mutation costs.

## Design

### Names a loop changes

`=` is the conditions draft's: `name = value` binds the name from that
line on, and `=` in a lambda binds only the lambda's names. A loop adds:

- **A name bound before the loop and again in its body carries.** Its next
  round sees the value the last one left, and the lines after the loop see
  the value the loop ended with. Read in the next round or after the loop,
  it has one type across rounds, as where a branch's paths meet; nothing
  reading it, it may change type, as `for x in xs` naming its element as a
  `Str` before it.
- **A name first bound in a loop's body is the round's.** It is new each
  round and unseen after the loop.
- **A test binds as `=` does,** so a worklist takes its head and binds its
  rest again in one: `while ready is [node, *ready] do (`, carried as any
  name the round binds again is.

### Loops

```
loop-line = "while" expr "do" "(" round ")"
          | "for" operand "in" expr "do" "(" round ")" ;
```

- **`for P in list ( … )`** runs its body once for each element, in order,
  `P` a pattern that cannot fail. It binds a name in scope again, as a
  test does, and that name carries out of the loop as Python's does, the
  last element taken; one first bound there is the round's. It walks a
  `List`; a range is `List.range`.
- **`while c ( … )`** runs while `c` holds. `c` may be an `is`, whose names
  the body sees, and may call an effect, worked out first each round:
  `while source.read!(2)? is Data(bytes) do (`.
- **No `loop`.** A loop whose test is partway through, as in reading
  until input ends, is `while True do ( … if done break … )`.
- **`do` before the body,** as `then` before a branch and `->` before a
  clause's body: every construct puts a word between its head and its body.
  The body is always a block, a round being lines where a branch is a
  value. So no `(` depends on its spacing: a call's `(` touches what it
  calls, and one apart from it is refused.
- **A loop is a line of a block,** not an expression, and not the last
  line of a block that answers. What a loop computes is left in the names
  it bound again.
- **A loop's body, a round, is block lines with no answer:** bindings,
  effects, leaving lines and loops, any of which may be its last; where
  nothing leaves it, the round goes on to the next.

### Leaving a round or a loop

`continue` and `break` are exits, written only in the conditions draft's
leaving lines, as `return` is, `if` leaving where its condition holds and
`else` where it fails:

- **`if c continue`, `c else continue`** end the round; the loop goes on.
- **`if c break`, `c else break`** end the loop; the line after it runs.
- **`if c return x`, `c else return x`** answer `x` from the function, from
  inside any loop.

Each applies to the innermost loop. Neither is an expression; neither
stands outside a loop.

### Nesting

Loops nest as deep as blocks do. How deep is a style's to say, a
linter's, as the conditions draft leaves which form to write; the
compiler refuses no depth. See [lints](../../lints.md). A lambda inside a loop is no part of its
round: a `continue` or `break` in it is refused.

### Meaning

Each loop is a recursive function, its parameters the names its body
binds again, what it reads, and for `for` the rest of the list; the lines
after it are a join point it answers to. `continue` calls the loop for the
next round; `break` and the loop's end call the join point; a `return`
inside answers the function. The call of the loop for the next round is in
tail position, so a round costs a jump. None of this is visible: a
function with loops answers what the same function written with folds
answers.

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
- **Nesting limits,** two loops deep and no multi-line lambda in a round,
  as first drafted. They said what style should, which is a linter's to
  say.
- **A bare one-line body,** `for x in xs do log!(x)`, as a branch may be a
  bare value. A one-line round is nearly always a method already: `sum`,
  `map`, `find`, `count`; only an effect for each element is not, lambdas
  being pure. A body beginning `(` would have had to mean the round's lines
  even where the line was `(a, b) = (b, a)`. The parentheses cost the effect
  case two lines, and a single effect line, which always begins with a name,
  can be added if programs ask for it.
- **No `do`,** the body's `(` alone ending the head. Then `while done (` and
  `while done(x) (` part by the spacing before a `(`, which nothing else
  in the grammar does.
- **`loop` beside `while`,** for a loop whose test is partway through. It
  is `while True ( … if done break … )`, a keyword fewer.
- **`loop` only, no `while`.** `while c ( … )` is `loop ( c else break …
  )`, a construct fewer for a line more on every loop.

## Implementation impact

1. **The lexer** gains the keywords `for`, `in`, `while`, `break` and
   `continue`.
2. **The grammar.** `grammar.ebnf` and the tree-sitter grammar gain loop
   lines and `continue` and `break` as exits.
3. **Resolution** records, for each loop, the names its body assigns, and
   refuses `continue` and `break` outside a loop.
4. **The checker** holds what a loop carries to one type across its
   rounds; lowering refuses a `for` pattern that can fail, as a binding's.
5. **Lowering** makes each loop a recursive function of the names it
   assigns, and the lines after it a join point, as the conditions draft's
   branches are.
6. **The standard library** gains `Map.counted`, `Map.grouped` and
   `update_or`, which the toposort reads.
7. **Programs.** The graph library's walks, components and toposort, and
   the heap's sift loops, written with loops; the HTML library's `for`
   renamed.
8. **Documentation.** `notes/syntax.md`, the standard library README, and
   the language tests.

## Testing

- `crates/faun/src/ebnf.rs` probes: each loop form, loops nested, and
  `else continue` and `if c break`.
- Refused cases, each with its `.err`: `continue` outside a loop, and in a
  lambda inside one, and a refutable `for` pattern.
- A running case across all three backends: a loop with an effect each
  round, `continue`, `break` and a `return` from inside.

## Built

- **Loops,** 2026-10-07: `while` and `for` over a `List`, `continue` and
  `break` in leaving lines, a round's last line free. Resolution reads a
  loop's body once ahead to find the names it binds again, which it then
  carries: a local within a round and another after the loop, each
  `continue` and `break` handing on the versions where it stands. Lowering
  makes every loop answer the function, as the join points do a branch that
  may leave: the lines after it a function of what it carries out, the
  round a function of what it carries in calling itself in tail position,
  so nine million rounds run in constant stack. A loop carrying or walking
  a value holding a resource is refused for now.

## Open questions

- **What `for` walks.** A `List` only, for now; a `Map`'s entries or a
  `Set` later, through their `to_list` or a fold.
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
