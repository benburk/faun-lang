# Proposal: Recursion, and names bound again as shadows

- **Status:** Approved
- **Created:** 2026-11-10
- **Approved:** 2026-11-10
- **Supersedes:** loops.md
- **Affects:** the lexer's keywords, `grammar.ebnf`, the parser, the
  tree-sitter grammar, name resolution, the checker, linearity, lowering,
  the standard library's lists, every program with a loop or a name bound
  again in a branch and read after it

---

## Summary

Faun drops `for`, `while`, `continue` and `break`: a walk is recursion, a
fold, or a library function. A name bound again shadows the one before it on
the lines below, to the end of the block it is bound in, and no further: a
branch's `x = …` no longer carries past the branch, and nothing carries
across rounds, there being none. A binding that binds a name already in
scope, and that nothing reads, is refused, which is what a vanished
assignment would be.

| Form             | Today                       | Proposed                   |
| ---------------- | --------------------------- | -------------------------- |
| Walk a list      | `for x in xs do (`          | a fold, or a clause a case |
| Worklist         | `while q is [x, *q] do (`   | `walk([x, *q]) -> walk(q)` |
| Leave early      | `if c break`                | `fold_until`, or answer    |
| A step           | `seen = seen.put(n, True)`  | the same                   |
| A branch's value | `if c then (x = a) else {}` | `x = if c then a else x`   |
| Unread binding   | allowed                     | refused                    |

## Motivation

The [loops](../superseded/loops.md) proposal compared loops with folds over
state records, before a name could be bound again. With binding again, the
comparison is recursion, and [loops, measured](../../loops-experiment.md)
made it on two programs:

- **An assembler and emulator,** 21 loops written again as recursion: 11%
  fewer lines, 2% more characters, the same machine instructions executed,
  four million rounds deep in constant stack.
- **The graph library,** now written in recursion: 139 lines where the
  loops took 149. Breadth and depth first became one walk differing only in
  where a node's targets go; Kosaraju's steps a clause each; Dijkstra's
  algorithm the textbook's four lines. Only loops inside loops sharing state
  read a little better as loops.

Loops are little used: outside the graph library, five programs, three of
them the syntax examples. What they cost is a second way to iterate beside
recursion and folds, six keywords, and the largest part of name resolution:
carrying names into rounds and out of loops, reading a loop's body ahead to
find what it binds again, and handing names on at each `continue` and
`break`. Gleam, the nearest language, has no loops, and its users do not
ask for them; they ask for a fold that stops early, which this adds.

Assignment past a branch exists for the same reason loops do: a loop's
round is code after a branch. Without loops it is only `if c then (x = a)
else {}`, which `x = if c then a else x` says in one line, and it costs
resolution a merge of every name each branch bound again.

## Design

### No loops

- **`for`, `while`, `continue` and `break` are gone,** and so is `do`.
  None is a keyword; `in`, which only `for` took, is not one either.
- **Iteration is recursion,** whose tail calls run in constant stack on
  every target, a fold, or a library function.
- **`List.fold_until`** folds while a step answers `Continue(state)` and
  stops at the first `Stop(state)`, answering that state: a fold that leaves
  early, as Gleam's does.
- **`List.try_fold`** folds while a step answers `Ok`, answering the first
  `Err`, as `try_map` maps.

### A name bound again shadows

- **`name = value` binds the name on the lines below, to the end of the
  block it stands in.** Bound before, the earlier binding is hidden there
  and seen again after the block: a branch's, an arm's, a lambda's and the
  lines after an `else` line's are each a block. On a straight line, any
  type, as now: `x = "12"` then `x = Nat.from_str(x)?`.
- **A test binds as `=` does,** where it holds: along an `&` chain, in a
  `then` branch and an arm, and on the lines below an `else` line.
- **Nothing is carried.** No name bound in a branch, an arm or an `else`
  line's block is seen after it, so no two ways meet holding a name, and no
  name must be one type where they meet.
- **A lambda's body is a block.** `=` in one shadows a name of the body
  around it within the lambda; it is no longer refused, since it changes
  nothing outside.
- **A binding binding again that nothing reads is refused:** "`x` is bound
  again here and nothing reads it". Where it stands last in a branch, the
  help says to bind the branch's value: `x = if c then … else x`. A name
  bound for the first time and not read stays allowed, as `said =
  host.println!(…)` is.

### What does not change

`if`, `is` with arms, guards, `return`, `?`, leaving lines, effects, and the
in-place reuse of a value nothing else holds. A join point is still made
after a branch some way of which leaves; it takes the names live there, and
no name a branch bound.

## Costs

- **Loops inside loops sharing state** read a little worse: each level
  answers its result with the state, and the level above takes the pair
  apart, as `walks` in the graph library does.
- **A step names every value it carries,** where a loop names only what
  changes; a walk over six values threads six parameters.
- **A walk needs a function and its signature,** where a loop needed none.
- **A value set in one branch of several** is spelled `x = if … then a else
  x`, the old value written again.

## Alternatives considered

- **Keep loops,** the status quo. The measurements found recursion as short
  and as fast, and loops cost the most machinery in resolution.
- **No binding again at all,** as Faun first had: every step a fresh name,
  `degrees2`, and the worklist bug the conditions proposal recorded, a
  `ready = rest` skipped by a `continue` going round forever.
- **Shadowing without the refusal:** a branch's `count = count + 1` would
  vanish after the branch without a word. The conditions proposal refused
  shadowing for exactly this; the refusal answers it.
- **Refusing every unread binding:** `said = host.println!(…)` and `closed
  = closing?` bind on purpose, to name what is discarded or to ask `?` of
  it. Only binding again unread is a mistake.
- **A worklist combinator,** `drain_stack` as the graph library had before
  loops: a lambda answering a pair reads worse than either.

## Implementation impact

1. **The standard library** gains `fold_until` and `try_fold`, before any
   program needs them.
2. **Programs.** The syntax examples `loops.fn`, `weird.fn` and
   `conditions.fn`, and the file examples `batch.fn` and `trickle.fn`,
   recurse; any program assigning past a branch binds the branch's value.
3. **The refused programs** about loops go; new ones refuse an unread
   binding again, `continue` and `break` as names, and a `for` line.
4. **The lexer and grammar** drop the loop lines and the six keywords;
   `grammar.ebnf` and the tree-sitter grammar change together.
5. **Resolution** drops carried names, reading ahead, and merging names
   bound in branches: a name bound again is a new local for the rest of
   its block. It refuses an unread binding again.
6. **The checker, linearity and lowering** drop loops: a loop's types, its
   rules for resources carried across rounds, and its lowering as a
   recursive function.
7. **Notes.** The pattern-matching note's rationale, the computation and
   effects notes where they mention loops, and the standard library README.

## Testing

- The syntax examples and the graph library, unchanged in what they answer.
- Refused programs, each with its `.err`: an unread binding again in a
  branch, and on a straight line; `while` read as a name.
- Every example program on all three targets, as `just test` runs them.

## Origin

Writing [faun-assemulator](https://github.com/benburk/faun-assemulator) in
Faun, then again without loops, and the graph library after it, recorded in
[loops, measured](../../loops-experiment.md), 2026-11-10.
