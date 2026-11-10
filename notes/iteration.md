# Iteration

This note owns how a Faun program does a thing again and again. There are
no loops: a walk is a function calling itself, a fold, or a list's own
methods. Faun had loops for a month; why they went, what they cost to
lose, and how both ways measured are here too. How a name bound again
behaves, which every step relies on, is
[pattern matching's](forms/pattern-matching.md#binding-again).

## How a walk is written

A walk is a clause for each case, the one going on calling itself on the
rest:

```ruby
summed : (List(Nat), Nat) -> Nat
summed([], total) -> total
summed([x, *xs], total) if x > 100 -> summed(xs, total)
summed([x, *xs], total) -> summed(xs, total + x)
```

- **A call whose answer is its caller's is a jump** on every target, so a
  walk of any length runs in constant stack: four million steps of an
  emulator, or a walk inside a walk two hundred thousand deep.
- **A list nothing else holds grows at either end in place.** A worklist
  takes from its front and puts after the rest for a queue, or before it for
  a stack, and neither copies the rest. So breadth first and depth first are
  one walk, `next` saying where a node's targets go:

  ```ruby
  walk(_, [], seen, order, _) -> (seen, order)
  walk(graph, [node, *rest], seen, order, next) if seen.get_or(node, True) -> walk(graph, rest, seen, order, next)
  walk(graph, [node, *rest], seen, order, next) -> (
    found = targets(graph.edges_from(node))
    walk(graph, next(found, rest), seen.put(node, True), order.append(node), next)
  )
  ```

  `next` is `|found, rest| rest.concat(found)` for breadth first and
  `found.concat(rest)` for depth first. A function handed to a walk is known
  where it is called, so it costs no call of its own.
- **A walk leaves early by answering** instead of calling itself again, by
  `return` from a leaving line or an arm, or by `?`. A fold that may stop is
  `fold_until`, whose step answers `Continue(state)` or `Stop(state)`, and
  one whose step may fail is `try_fold`.
- **A walk inside a walk** answers what it found with the state it was
  handed, and the walk around it takes the pair apart. The groups a
  depth-first search gathers share what every walk has seen:

  ```ruby
  walks(graph, [start, *starts], seen) -> (
    (seen, group) = walk(graph, [start], seen, [], deeper)
    (groups, seen) = walks(graph, starts, seen)
    ([group, *groups], seen)
  )
  ```
- **A list's methods are walks already:** `map`, `filter`, `find`, `count`,
  `fold`, `try_map`, `flat_map` and the rest; a recursion that is one of
  them is better written as it.
- **A walk popping a stack from its end** is covered as one taking it from
  its front: `[]`, `[*rest, Leave(n)]` and `[*rest, Enter(n)]` cover every
  list ([pattern matching](forms/pattern-matching.md#coverage)).

## Measured

Two programs were written with loops and again without, on 2026-11-10.

**An assembler and emulator,**
[faun-assemulator](https://github.com/benburk/faun-assemulator): a lexer, an
expression evaluator, a two-pass assembler with macros and includes, and a
runner stepping a CPU. Its 21 loops were written again as recursion, folds
and clauses; the 17 example programs gave the same output and bytes.

| File       | With loops | Without | Characters, with / without |
| ---------- | ---------- | ------- | -------------------------- |
| lexer      | 129 lines  | 93      | 4,161 / 3,819              |
| expression | 102        | 104     | 3,457 / 3,650              |
| assembler  | 340        | 300     | 15,483 / 15,849            |
| runner     | 135        | 129     | 4,561 / 4,964              |
| **all**    | **706**    | **626** | **27,662 / 28,282**        |

Lines count neither comments, blanks nor `expect`s: 11% fewer lines and 2%
more characters. Stepping a CPU through 4.2 million instructions executed
2,879.3 million x86-64 instructions with loops and 2,879.5 million without.

**The graph library,** written three ways: with loops; with the worklist
combinator it had before them, `drain_stack` handed a visit answering the
state and what it adds; and as recursion. Each passes the library's 40
expectations. The recursion's walks executed the same instructions as the
loops', 115.7 billion against 116.0 billion on a graph of 1.1 million nodes.

| File (lines of code) | Loops   | Combinator | Recursion |
| -------------------- | ------- | ---------- | --------- |
| walk                 | 41      | 45         | 34        |
| toposort             | 20      | 23         | 23        |
| components           | 55      | 53         | 50        |
| dijkstra             | 33      | 33         | 32        |
| **all**              | **149** | **154**    | **139**   |

**Kahn's algorithm,** the case loops were added for, is 15 lines with them,
about 19 without, and 39 in Gleam, formatted by `gleam format`. Half of
Gleam's extra lines are its library and formatter; the other half is the
state, a tuple packed, unpacked and rebuilt in each branch, which Faun's
record patterns with punned fields and binding again take away.

Where each way read better:

- **Recursion, where a walk takes values apart.** The lexer's loops walked
  an index; as clauses, each token is the pattern that spells it, as
  `name_length([':', ':', *rest]) -> 2 + name_length(rest)`, 36 lines fewer.
- **Recursion, where steps differ.** Kosaraju's leaving order pops `Enter`
  and `Leave` steps: a clause for each, where the loop took a step apart
  with `left = if step is Leave(done) then … else left` and then `step is
  Enter(next) else continue`.
- **Recursion, where a fold accumulates.** Data directives and includes
  became `try_map`, `flat_map` and `flatten` over their arguments.
- **Loops, a little, where walks nest sharing state.** Kahn's algorithm, a
  `for` over a node's edges inside a `while` over the ready nodes, became a
  fold inside a recursion with a record of the state between them.
- **Neither, for the combinator.** A visit is a lambda answering a pair, and
  the reader puts the loop back together from `drain_stack`'s definition.

One author wrote both versions, the loop versions first, while learning the
language; some of those loops were clumsy, and part of the gain is the
rewrite.

## What Gleam's users say

Gleam, the nearest language in spirit, has never had loops. A Lobsters
thread and four Hacker News threads on it, and an Advent of Code 2025 report,
were read on 2026-11-10:
[Lobsters](https://lobste.rs/s/4yqgpu/you_should_try_gleam),
[Advent of Code](https://blog.tymscar.com/posts/gleamaoc2025/) and
[its thread](https://news.ycombinator.com/item?id=46255991),
[The Gleam Programming Language](https://news.ycombinator.com/item?id=46611667),
[Gleam Is Pragmatic](https://news.ycombinator.com/item?id=41758915) and
[compiling to Erlang](https://news.ycombinator.com/item?id=49975619).

- **Almost nobody asks for loops.** The Advent of Code author, after 25
  days of loop-heavy puzzles: "Once you stop trying to write loops and you
  let it be functional, the solutions start to feel clearer." His favourite
  feature is `fold_until`: "Early exit without hacks is fantastic in
  puzzles."
- **The one complaint** is a veteran of Erlang's, which has no loops either:
  "at some point the neatness of doing all loops as recursion wears off and
  it's just tiring." An Elixir user prefers `for … reduce:` because "the
  accumulator gets labelled."
- **What draws complaints is elsewhere:** no typeclasses, no derived
  encoders, no `if`, and `use` standing for early return, each a
  workaround made verbose. Faun has `where` bounds, `if`, `return` and `?`.
- **What draws praise** is mostly not the language's shape but its tools,
  and "having one way to do things makes Gleam so much easier to read."

## Rationale

### Why no loops?

One way to do a thing. Recursion, folds and a list's methods were there
before loops, and stayed after; loops were a second way to write every walk,
and a reader had to know both and a writer to choose. Measured, recursion
wrote the same programs as short, ran the same instructions, and read better
wherever a walk takes values apart. Loops also cost the compiler most of name
resolution: carrying names into each round and out of the loop, reading a
loop's body ahead to find what it binds again, handing names on at each
`continue` and `break`, and their own rules for files carried between
rounds. Removing them took six keywords and some 1,700 lines of compiler,
and with them the one reason a branch's assignment had to be carried past
the branch, so a name bound again is now a shadow, one rule
([pattern matching](forms/pattern-matching.md#why-does--bind-again-as-a-shadow)).

The cost is below; the recourse is a fold that stops, `fold_until`, a fold
that fails, `try_fold`, and a walk answering its state beside what it found.

### What does a walk cost that a loop did not?

- **A function and its signature** for each walk, where a loop needed
  none: a three-line round becomes a five-line definition.
- **Every value carried is named,** where a loop names only what changes; a
  walk over six values threads six parameters.
- **Walks inside walks sharing state** answer pairs the walk around takes
  apart, and the outer one goes as deep as there are inner walks, where
  loops went round.
- **An effect cannot be an arm's value,** so a walk dispatching on what an
  effect answered needs a function with a clause per outcome.

Nested record update would shrink the state a walk threads through
records; it is not built.

### Why recursion rather than a worklist combinator?

Before loops, the graph library walked by `drain_stack`, a function handed
a visit that answers the state and the items it adds. It needed no loops and
no recursion in the program, but every walk became a lambda answering a
pair, and the reader put the loop back together from the combinator's
definition. It read worst of the three ways measured. With binding again and
record patterns, plain recursion is shorter and says each case where it
happens.

### Why not keep loops for walks inside walks?

That is where they read a little better, and it is not enough for a second
way to iterate: the two programs measured had five such nests, and each read
about as well answering a pair. Gleam's users, without loops at all, ask for
an early-exit fold rather than loops back.

## History

- **2026-09:** walks were recursion over state records, or the worklist
  combinator, and a name could not be bound twice. Kahn's algorithm took 48
  lines in the graph library: a record type per algorithm, a visit helper
  taking it apart and building it again, the graph passed by hand, and a
  fold inside a fold.
- **2026-10-04 to 10-14:** loops were added: `for`, `while`, `continue` and
  `break`, a name bound before a loop and again in its body carried from
  round to round and out. The draft first marked a carried name with `$` at
  every use, `$order.append(node)`; plain assignment replaced the sigil once
  binding again was allowed everywhere. Files carried across rounds came
  last, each round having to end as it began. Kahn's algorithm took 15
  lines, against Python's 15.
- **2026-11-10:** writing an assembler in Faun, and then the graph library,
  without loops measured what is above. Loops were removed the same day, and
  a name bound again became a shadow: `for`, `while`, `continue`, `break`,
  `do` and `in` are no keywords, and `List.fold_until` and `List.try_fold`
  were added. Writing the recursion found two refusals of good programs,
  since fixed: a stack popped from its end was not seen to be covered, and
  a `return` answering a narrower row than its signature's was refused where
  the body's last line would have been widened.

## Related

- [Pattern matching](forms/pattern-matching.md): clauses, leaving lines,
  coverage, and binding again as a shadow
- [Computation](computation.md): strict evaluation, and why termination is
  not checked
- [Conditions](proposals/approved/conditions.md): `is`, arms, leaving lines
- [Lints](lints.md): a recursion that is a list's method already
