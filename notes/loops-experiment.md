# Loops, measured against recursion

Faun has `for` and `while` since the [loops](proposals/superseded/loops.md)
proposal. Gleam, the nearest language in spirit, has none: recursion, folds
and `use` do their work. This note records an experiment asking what Faun's
loops buy, by writing a real program both ways, and what Gleam's users say
about living without them.

Measured 2026-11-10 on the `assemulator-fixes` branch.

## The program

[faun-assemulator](https://github.com/benburk/faun-assemulator) is an
assembler and emulator for toy CPUs: a lexer, an expression evaluator, a
two-pass assembler with macros, includes and conditional assembly, and a
runner stepping a CPU until it stops, reading lines as it asks for them. It
was written with loops, 21 of them. Every one was then written again as
recursion, folds and clauses, keeping behaviour: the 17 example programs give
the same output and bytes, and the library's 21 expectations hold.

| File       | With loops | Without | Characters, with / without |
| ---------- | ---------- | ------- | -------------------------- |
| lexer      | 129 lines  | 93      | 4,161 / 3,819              |
| expression | 102        | 104     | 3,457 / 3,650              |
| assembler  | 340        | 300     | 15,483 / 15,849            |
| runner     | 135        | 129     | 4,561 / 4,964              |
| **all**    | **706**    | **626** | **27,662 / 28,282**        |

Lines count neither comments, blanks nor `expect`s. Without loops the
program is 11% fewer lines and 2% more characters: about even.

The emulator runs the same work either way: stepping a Photon CPU through
4.2 million instructions executes 2,879.3 million x86-64 instructions with
loops and 2,879.5 million without, `perf stat` counting. The runner's
recursion is two functions calling each other in tail position, four
million rounds deep, in constant stack.

## Where recursion read better

- **Walking bytes.** The lexer's loops walked an index. As clauses over the
  list, each token is the pattern that spells it:
  `name_length([':', ':', *rest]) -> 2 + name_length(rest)`, and a character
  literal is `['\'', '\\', c, '\'', *rest]`. 36 lines fewer.
- **A depth count.** Skipping to a `.if`'s `.else` or `.endif` is one `is`
  on the directive and the depth, each arm calling on with the next depth,
  where the loop carried the depth and left from inside arms.
- **Accumulating.** Data directives, `.strz` and includes became `try_map`,
  `flat_map` and `flatten` over the arguments, where each loop appended to a
  list it carried.

## Where it cost

- **Many names carried.** Substituting a macro's arguments threads five
  values through every clause; stepping the CPU, six through two functions.
  A loop names only what changes.
- **An effect cannot answer an `is` arm.** The runner's loop left by
  `return` from arms on the step's outcome. Recursion needs the call after
  `Continue` in an arm, which an effect may not be, so the dispatch became a
  function of its own with a clause per outcome.
- **A named function for each inner loop.** Each needs a signature, so a
  three-line loop body becomes a five-line definition.
- **Library gaps,** each needing a helper: `List.split_on` (a list parted at
  a separator, as `Str.split` parts text), `filter_map`, `try_fold`, and a
  `chunks(n)` answering a list of lists, where `blocks` answers a record.

## Kahn's algorithm

The loops proposal's motivating case, in
[`syntax/loops.fn`](../crates/faun/examples/syntax/loops.fn), is 15 lines
with loops. Without them it is about 19, against Gleam's 39 for the same
algorithm, formatted by `gleam format`:

```
Kahn = {ready: List(Nat), degrees: Map(Nat, Nat)}

kahn(_, {ready: [], *}, order) -> order
kahn(graph, {ready: [node, *ready], degrees}, order) -> (
  next = graph.get_or(node, []).fold({ready, degrees}, released)
  kahn(graph, next, order.append(node))
)

released({ready, degrees}, target) -> (
  degrees = degrees.update(target, |degree| degree - 1)
  if degrees.get_or(target, 0) > 0 then {ready, degrees} else {ready: ready.prepend(target), degrees}
)
```

Gleam's extra lines are half its standard library and formatter, and half
the loop: a tuple of the state packed, unpacked and rebuilt in each branch.
Faun's record patterns with punned fields, binding a name again, and clauses
take most of that away. The proposal compared loops with the folds Faun had
before binding again was allowed; recursion with it is much closer.

## The graph library

The graph library's walks have been written three ways: with loops, after
the loops proposal; with a worklist combinator, `drain_stack` and
`drain_queue` handed a visit answering the state and what it adds, before
it; and as recursion, which the library is now written in. Every version
passes the library's 40 expectations.

| File (lines of code) | Loops   | Combinator | Recursion |
| -------------------- | ------- | ---------- | --------- |
| walk                 | 41      | 45         | 34        |
| toposort             | 20      | 23         | 23        |
| components           | 55      | 53         | 50        |
| dijkstra             | 33      | 33         | 32        |
| **all**              | **149** | **154**    | **139**   |

Dijkstra's algorithm never had a loop: it drained its heap through the
combinator in both earlier versions, and is now a recursion like the walks.

Line counts are even. Which reads better is not:

- **One walk for both orders.** Breadth first and depth first are one
  recursion, and differ only in where a node's targets go: after the rest,
  a queue, or before it, a stack. A list nothing else holds grows at either
  end in place, so neither copies the rest, where in Haskell `rest ++
  children` copies the queue every step:

  ```
  walk(_, [], seen, order, _) -> (seen, order)
  walk(graph, [node, *rest], seen, order, next) if seen.get_or(node, True) -> walk(graph, rest, seen, order, next)
  walk(graph, [node, *rest], seen, order, next) -> (
    found = targets(graph.edges_from(node))
    walk(graph, next(found, rest), seen.put(node, True), order.append(node), next)
  )
  ```

  `next` is `|found, rest| rest.concat(found)` for breadth first and
  `found.concat(rest)` for depth first. The loops had one walk each, and
  depth first pushed each node's targets reversed onto the end of its
  stack, so the first came off first.
- **A walk whose steps differ reads better recursed.** Kosaraju's leaving
  order pops `Enter` and `Leave` steps. The loop took a step apart with
  `left = if step is Leave(done) then … else left` and then `step is
  Enter(next) else continue`; recursion is a clause for each, the way the
  algorithm is told.
- **Dijkstra's algorithm reads as it is told:** take the cheapest entry; a
  node settled already is passed over; otherwise settle it and push an entry
  for each edge. The combinator split that between a lambda and a function
  answering a pair.
- **Loops in loops sharing state cost recursion the most.** The groups a
  depth-first search gathers are a walk from each start in turn, all
  sharing what was seen: a `while` inside a `for`, both binding `seen`.
  Recursed, each level answers its result with what it saw, and the level
  above takes the pair apart:

  ```
  walks(graph, [start, *starts], seen) -> (
    (seen, group) = walk(graph, [start], seen, [], deeper)
    (groups, seen) = walks(graph, starts, seen)
    ([group, *groups], seen)
  )
  ```

  That reads about as well as the loop, though it is no tail call: it goes
  as deep as there are groups. Kahn's algorithm, a `for` over a node's edges
  inside a `while` over the ready nodes, became a fold over the edges inside
  a recursion, with a record of the ready nodes and the degrees between
  them; the loop is a little clearer there.
- **The combinator reads worst.** A visit is a lambda answering a pair,
  and the reader puts the loop back together from `drain_stack`'s
  definition. It was the price of having neither loops nor recursion that
  read well, and is not needed with either.

Writing it found two refusals of good programs, both fixed. Coverage refused
`[*rest, Leave(node)]` beside `[*rest, Enter(node)]` and `[]`, since a
list's end that tested its elements covered nothing; it now judges a place
whose patterns all read the same from the end as the list turned round. And
a `return` met its signature as a plain unification, so a closed row it
answered was refused where the body's last line would have been rebuilt in
the signature's row; it now meets it as the last line does.

## What the experiment does not settle

- One author wrote both versions, the loop version first, while learning the
  language; some of its loops were clumsy, and part of the gain is the
  rewrite.
- The heap's sifting was already recursion, and is not compared.
- Readability is not line count. A loop names only what changes and keeps
  the steps in order on the page; recursion names every value carried and
  the shape of each step in a signature.

## What Gleam's users say

Read 2026-11-10: a Lobsters thread and the article it discussed, an Advent
of Code 2025 report and its Hacker News thread, and three more Hacker News
threads on Gleam. Quotes are the commenters' own.

- [Lobsters: You should try Gleam](https://lobste.rs/s/4yqgpu/you_should_try_gleam)
  and [the article](https://nchagnet.eu/blog/you-should-try-gleam)
- [Advent of Code 2025 in Gleam](https://blog.tymscar.com/posts/gleamaoc2025/)
  and [its thread](https://news.ycombinator.com/item?id=46255991)
- [The Gleam Programming Language](https://news.ycombinator.com/item?id=46611667)
- [Gleam Is Pragmatic](https://news.ycombinator.com/item?id=41758915)
- [Gleam doesn't compile to Erlang source anymore](https://news.ycombinator.com/item?id=49975619)

### On loops

Almost nobody asks for them. Gleam's users report recursion as a non-issue
or a gain; the one complaint is from a veteran of Erlang, which has no loops
either.

- The Advent of Code author, 25 days of loop-heavy puzzles: "Once you stop
  trying to write loops and you let it be functional, the solutions start to
  feel clearer." His favourite feature is `fold_until`, a fold whose step
  answers `Stop` or `Continue`: "Early exit without hacks is fantastic in
  puzzles."
- The article: guaranteed tail calls give "performance close to an
  imperative `while` loop."
- mahboi, years of Erlang: "at some point the neatness of doing all loops as
  recursion wears off and it's just tiring," and of `reduce`, "Just want to
  insert into my list or whatever."
- sodapopcan prefers Elixir's `for … reduce:` because "the accumulator gets
  labelled," where a fold's argument order is easy to forget.

### On what Gleam does leave out that costs it

The omissions that draw the complaints are elsewhere:

- **No typeclasses or interfaces,** the most argued: "No ad-hoc
  polymorphism… means no standard way of defining how things work." Its
  creator answers that they desugar to passing functions; others call that
  "a hack, not a language feature." Faun has `where` bounds, so this one
  does not apply.
- **No macros, so no derived serialization:** "having to essentially write
  every type three times," the type, its encoder and its decoder. Gleam
  answers with code its language server generates. Faun derives `equals`,
  `to_str` and hashing, not encoders.
- **No `if`:** `case x < 0 { True -> … False -> case … }` nests, and guards
  "cannot contain function calls"; "I feel like that's not a small
  sacrifice." Faun has `if` and guards that call.
- **`use` for early return** divides: "early returning always being weird
  `use` call," against "once you're used to it it's pretty elegant." Faun
  has `return`, `?` and leaving lines.
- **Smaller costs:** qualified names, `list.map`, at every call; no string
  interpolation; no `[first, ..middle, last]`; comparisons answering `Order`
  where a `Bool` was wanted.

What its users praise is mostly not the language's shape: the language
server, the compiler's errors, pipes, `Result` in place of exceptions, `echo`
for debugging, and a language small enough to hold in one's head, or an
LLM's context. "Truly having one way to do things makes Gleam so much easier
to read"; Gleam is "a language of 'no', which if you like that, cool."

### What follows for Faun

The evidence leaves loops optional: their absence is not what Gleam's users
complain of, provided there is a structured early exit like `fold_until`.
The pains are verbosity where an omission forces a workaround: nested `case`
for `if`, `use` for `return`, hand-written encoders. Removing loops would
add one more: a helper per inner loop and every carried name threaded, as
this experiment found. If loops go, `fold_until` and the library functions
above should come first.

## What would close the gap either way

- **Nested record update,** `{asm.macros: m, *cursor}`, shrinks the state a
  recursion threads through records.
- **Effects in arms,** or as arguments, lets a recursive runner dispatch
  inline.
- **The four library functions** above shorten both styles.
