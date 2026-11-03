# Totality

A language is total when every call of a pure function comes back with an
answer. Faun is not: termination is not checked, and a pure call may never
come back ([termination proposal](proposals/approved/termination.md)). Ori,
which Faun began as a port of, was total, and enforced it. This note keeps
the whole trade: what totality makes simple, what it makes hard, the
designs in between, and what would change the decision.

## What totality is, and is not

Total means every call answers. It does not mean every call answers soon. A
loop counting to 2^64 is total. So totality is a promise about meaning,
not about time or memory.

Safety-critical rules ask for more. JPL's "Power of Ten" rules for flight
software (Holzmann, 2006) forbid recursion, direct or indirect, and require
every loop to have a fixed upper bound a tool can check; MISRA C forbids
recursion too. What they want is a bound on time and stack, and they get it
by restricting forms and writing bounds out, which is fuel everywhere.
Totality alone would not satisfy them.

There are four ways a language can make the promise:

- **By construction.** Recursion is only through a fixed scheme, such as a
  fold that consumes one constructor each step (Gödel's System T, Dhall).
  Nothing is checked, because nothing else can be written.
- **Structural recursion.** Any recursion is allowed where one argument is
  a part of what was handed in (Agda, Coq by default).
- **Analysis.** The compiler proves descent from the code as written.
  Size-change termination (SCT) composes how each call changes its
  arguments' sizes around every loop, and accepts when every repeating path
  shrinks something. It finds lexicographic and permuted descent on its
  own: `merge`, which shrinks one list in one branch and the other in the
  next, and even Ackermann's function. Ori did this, with no annotations.
- **Measures written by the programmer.** Where no argument shrinks, the
  programmer names a quantity that does, and sometimes proves it. Lean
  writes `termination_by` and `decreasing_by`; Idris and Agda have their
  own forms.

Ori's history ran through most of these: recursion only through `fold`,
then plain SCT, then SCT fed by facts the compiler derived about results,
such as `mod(a, b) < b` where `b > 0`, so `gcd` was proved with nothing
written down. Faun dropped the check on 2026-09-29.

## What totality makes simple

### One meaning for pure code

When every pure call answers, and no operation can fail, the order in
which pure code runs cannot be observed: only the answer can. A pure
program then means one thing however it is evaluated, eagerly, lazily, in
parallel or reordered.

Without totality a hang is observable, so the language must say what runs.
Faun shows the cost in `&` and `|` on `Bool`. Code relies on the right side
being skipped where the left decides:

```ruby
even(n) -> n == 0 | odd(n - 1)
odd(n) -> n != 0 & even(n - 1)
```

At nought `0 - 1` is `0`, so working out the right side would go round
forever. The compiler finds `Bool.and` and `Bool.or` by name and lowers
them to a match on the left, a special case no other function has
([computation](computation.md)). In a total language `and` would be an
ordinary function, and skipping its right side an optimization nobody
could see. The same goes for `select` and `Order.or`.

### Work may move, not only be skipped

Faun keeps one freedom without totality: pure work nothing needs may be
left out. That is enough for dead code removal, fusion and pruning, which
only skip. It is not enough for what moves work earlier or does it on
spec:

- working out both branches of an `if` and picking one without a jump, as
  C compilers do with `cmov`
- hoisting a call out of a branch, or out of a loop that might not run
- working out independent pure calls in parallel
- folding any closed call at compile time

Each runs work on a path that would not have run it, so where that work
never comes back, it turns a program that finishes into one that hangs.
With totality every one of these is allowed without asking. Without it,
each needs the work proved to stop first, and constant folding gives up
past a step budget rather than risk hanging the compiler.

Ori's notes measured where LLVM stands: it deduces `willreturn` for
straight-line code and counted loops, and gives up at recursion, which is
exactly what SCT decides. Totality covers the case a conventional optimizer
cannot.

### A class of mistakes caught when compiling

Recursing on the list rather than its rest, or on `n` rather than `n - 1`,
was a refusal: "goes round on what it was handed, not on a part of it."
Without the check, the program hangs when run, and a test that reaches it
hangs instead of failing.

### Functions in the mathematical sense

A total pure function is a function: every input has one answer. Reasoning
by equations holds without exceptions, and an `expect` either holds or
does not. Haskell's pure functions carry an undefined value for each type,
which is where its equational reasoning picks up asterisks.

### Room for types that compute

A type checker that evaluates terms, as dependent types require, would run
user code while checking. In a total language that is safe; in Faun it
could hang the checker ([dependent types](dependent-types.md)). Indexed
types over a separate decidable theory, such as linear arithmetic on
lengths, never run user code, so they do not need totality.

## What totality makes hard

### Programs that stop for reasons a size analysis cannot see

When the check was revived as an experiment in October, on Faun's code as
written, and fixed until everything it could prove was proved, what was
left was not a shape the analysis missed. Each depends on the input, on an
invariant of the data, or on what callers pass:

| Definition                          | Why it stops                      |
| ----------------------------------- | --------------------------------- |
| `bfs`, `toposort`, `groups_from`    | a worklist that fills up, bounded |
| `leaving_order`, `components` walk  | by the set of nodes seen so far   |
| union-find `root`, `back`           | parents point to smaller nodes    |
| `Heap.drain`                        | callers add only finitely many    |
| the float formatter's `widen`       | callers never start it at nought  |
| `mine` (Advent of Code 2015, day 4) | an answer exists for that input   |

These fall into three kinds, and only the first looks within reach of an
analysis that needs nothing written:

- **Worklists.** A graph walk, Dijkstra's algorithm among them, stops
  because each round either visits a node not seen before or takes an item
  off the worklist, and a graph has finitely many nodes. The textbook proof
  is a pair compared in order: the number of nodes not yet seen, then the
  worklist's length. No argument's size shows it; a set's does. An
  analysis that knew a `seen` set only grows, never past the number of
  nodes, and grows where an absent key is put in it, could build the pair
  itself. Faun already recognizes facts of this kind about lists, such as
  what `put` and `append` do to a length. This is unexplored.
- **Invariants of the data.** Union-find's `root` stops because parents
  point to smaller nodes, which the code keeps true but no analysis of the
  definition can see. It needs a proof, or a type that keeps the
  invariant.
- **Searches.** `mine` stops because an answer exists for its input. No
  analysis can know that; a bound is the honest form.

Interpreters for a language that can loop, and servers, must not stop at
all; Ori's recourse was to put the loop in the runtime, outside the
language, with total handlers.

### Fuel, or a measure written by hand

Where no argument shrinks, the program has to say what does. There are two
ways, and both are text written for the checker's sake:

- **Fuel.** A step count handed down and taken one from each round. Faun
  had 71 lines of it in 20 files. The graph library handed every walk
  `stored_edges(graph) + 1`, a helper that existed for nothing else. Worse,
  a limit one too small turns a hang into a silently wrong answer: a drain
  one short returns a partial walk.
- **A measure.** The quantity that shrinks, written beside the definition:
  the number of nodes not yet visited, or `hi - lo`. Lean's
  `termination_by` is this, often with a proof under `decreasing_by` that
  the measure goes down at each call.

SCT spares the programmer for descent on the arguments themselves: which
argument shrinks, in which order, is found without being written. A
measure is needed exactly where the quantity is not an argument's size.

### Slower checking, and an analysis that keeps growing

The analysis was 2,315 lines and took 8–41% of `faun check` time on the
example programs; the termination proposal has the table. Each extension to
prove another shape reached into every match the analysis reads. One
experiment to prove a walk over a table of marks took 540 lines and slowed
unrelated programs by up to 1.8×. The October revival ended near 2,900
lines, adding 3–10 ms to a check. Ori's tiers were about 3,100.

The analysis is also trusted. A bug in it accepts a program that never
stops, and every optimization relying on totality inherits the bug. The
October work found three such bugs in the old checker.

### Verdicts that move

- **Optimization.** Termination was checked again after optimization, and
  at one point a program was accepted or refused depending on how much had
  been inlined.
- **How a condition is spelled.** A guard was read in one order of an `&`
  and not the other, or lost when a later clause took a parameter apart.
- **Generic code.** A generic definition is judged at each type it is used
  at. `countdown(n) -> countdown(n - 1) + 1` with a base case at nought is
  proved at `Nat`, whose subtraction stops at nought. It is refused at
  `Int`, where a negative argument never comes back, and at `U8`, where it
  does come back, by wrapping round, but no size shows it. A library author cannot see what their definition
  requires of its type, and one no program instantiates is never judged:
  about 5% of the standard library's signatures were never seen.

### Refusals that blame the program

"Nothing here shows `walk` stops" is said both of a program that loops and
of one that stops where the proof is out of reach. The message cannot tell
the user which. Ori kept the two verdicts distinct; the user still had to
change a program that was correct.

## What Faun does instead

- **Termination is not checked.** A needed call that never comes back hangs
  the program, after every effect written before it.
- **Unneeded pure work may be left out.** This keeps dead code removal,
  fusion and pruning sound with no proof. It never lets the optimizer
  conclude that anything stops, so nothing is derived from a loop that must
  have ended, unlike C++'s forward-progress rule.
- **Two connectives choose.** `&` and `|` on `Bool` work out their right
  side only where the left does not decide. Whether that is promised, and
  how it is described, is open ([computation](computation.md)).
- **Bounded compile-time work.** Constant folding runs within a budget.
- **Kept refusals.** Exhaustive matching stays, for its own reasons
  ([pattern matching](forms/pattern-matching.md)), and so does refusing a
  callback wrapped anew each round, which is about what can be compiled.

## Rationale

### Why did Faun drop it?

The guarantee caught a real but rare mistake, and the bill was visible in
every program that recursed on anything but a part of its input: fuel,
wrong answers where fuel ran short, refusals of correct programs, and a
large share of checking time. The optimizer turned out to need only that
unneeded work may be skipped. The cost Faun accepted is semantic: pure code
no longer means one thing under every evaluation order, and the language
has to say where that matters.

### Why not make recursion total by construction?

Ori tried a `fold` as the only recursion first. It fails on the programs
people write: a rose tree, whose children sit in a `List`, has no field of
its own type to fold over, and mutual families such as an AST's
expressions and statements fold from neither side. JSON is a rose tree and
a parser is a mutual family, so the first two real programs hit the wall.

### Why not require written measures, as Lean does?

It accepts everything an analysis accepts and more, and the checker stays
small, since checking a given measure is simpler than finding one. But
every definition whose descent is not on an argument carries a measure,
and often a proof, written for the checker. The worklist programs above
would each gain one. That is the same kind of text as fuel, without the
wrong answers, and it runs against Faun's aim of short programs that are
pleasant to write.

### Why not total by default, with a `partial` marker?

Idris, Lean and Agda do this. It keeps the checker's cost and its refusals
for every unmarked definition, and adds a word to the language. Totality
is also a property of the whole call graph: one `partial` definition makes
every caller partial, so a guarantee for a program is only as strong as its
least careful dependency.

### Why not track divergence as an effect?

Koka infers a `div` effect for any function it cannot show stops, and F\*
separates `Tot` from `Dv`. Nothing is refused, and the compiler knows
where totality holds. In Faun it would be inferred, like an effect a
function might have, and not written. It still needs the analysis, with
its cost and its bugs, since an optimization trusting the fact must never
be told wrong. And it adds a second kind of purity for a reader to track.
The termination proposal rejected the same idea as "keep the analysis as a
fact, not a refusal."

### Why not assume every call comes back, as C++ does?

It would give the optimizer everything totality gives it, with no checker.
C++ makes a side-effect-free loop that never ends undefined behaviour, and
LLVM's `mustprogress` lets the optimizer assume such loops end. From the
assumption it derives facts about the code after them, and a false
assumption makes anything possible: the termination proposal shows clang
falling out of an endless `main` into the next function.

Faun has no undefined behaviour anywhere: no operation fails, and every
one answers. Assuming termination would add the one exception, where a
looping bug could skip a check and run an effect it should not have.
Faun's rule is the safe half of the assumption: it permits leaving work
out, and never concluding that anything stops, so a looping bug is a hang,
never a miscompile.

### Why not use what obviously stops?

Most of what speculation wants is small: straight-line arithmetic with no
call that can come round again, and a `for` over a list, which stops since
the list is finite. Both stop with nothing to prove. A fact the compiler
reads off such code, as LLVM deduces `willreturn` for straight-line code
and counted loops, would let the optimizer work out both branches of a
cheap `if`, or hoist a call out of a branch, with no whole-program
analysis, no refusals and no cost to checking. It would not give pure code
one meaning, so it would not remove the special case in `&` and `|`. This
is unexplored.

### What would change the decision?

- **An analysis that needs nothing written for most real code, and is
  fast.** The October experiment left worklists, invariants of the data
  and searches. If a recognized measure for worklists proved the graph
  library in a few hundred lines and a few milliseconds, requiring totality
  would ask for a bound only where one is honest: searches, and invariants
  a type does not keep.
- **Optimizations that only totality allows.** If speculation, parallel
  evaluation or folding without a budget turn out to matter in Faun's
  benchmarks, the semantic case grows.
- **More blessed evaluation.** If more functions than `Bool`'s connectives
  need a promised evaluation order, the cost of not having one meaning for
  pure code is growing.
- **Types that compute.** Full dependent types would need it; Faun has
  ruled them out. Indexed types would not.
- **Running untrusted code.** Totality plus a resource limit is a
  guarantee that can be handed to someone. Faun has no such use today, and
  totality alone does not bound time.

## Related

- [Termination proposal](proposals/approved/termination.md): the decision,
  its measurements and its errata
- [Computation](computation.md): strict evaluation, the rule for unneeded
  work, and `&` and `|`
- [Dependent types](dependent-types.md): why types that compute are out
- [Pattern matching](forms/pattern-matching.md): exhaustiveness, kept for
  its own reasons
- [Functions](values/functions.md): the refusal that remains, a callback
  wrapped anew each round
