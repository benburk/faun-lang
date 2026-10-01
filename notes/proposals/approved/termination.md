# Proposal: Termination is not checked

- **Status:** Approved
- **Created:** 2026-09-29
- **Approved:** 2026-09-29
- **Affects:** what a pure definition may do, Barb validation and the
  termination analysis, which goes, the refused programs about stopping, the
  README's promise, every step limit written only to satisfy the checker

---

## Summary

Today a definition the compiler cannot prove stops is refused. After this
change nothing about stopping is checked: a pure definition may fail to
stop, and a program that needs its answer hangs, as in Rust, OCaml or
Haskell. One rule replaces the guarantee the optimizer relied on: a pure
computation whose result is never needed may be left out, so whether it
would have stopped is not observable. The termination analysis goes
entirely.

| Case                           | Today         | After             |
| ------------------------------ | ------------- | ----------------- |
| Not proved to stop             | refused       | accepted          |
| A needed call never comes back | cannot happen | the program hangs |
| Unneeded pure work never stops | cannot happen | may be left out   |
| Checking cost of the proof     | 8–41%         | none              |
| Termination analysis           | 2,315 lines   | none              |

## Motivation

The guarantee costs more than it gives. What people get from it is a
promise that a pure call comes back, which catches a class of bug that is
real but rare. Termination is not boundedness either: a loop counting to
2^64 is total. What people pay is visible in every program that recurses on
something other than a part of what it was handed.

**Step limits written for the checker.** 71 lines in 20 of the example and
standard files mention `fuel`. Some are honest bounds: Newton's method gives
up after `n` steps, a search over a finite space says when it is exhausted.
Others exist only so the checker accepts a loop that plainly stops. The
graph library's worklists are the clearest case: every walk hands
`stored_edges(graph) + 1` to its drain, a helper that exists for nothing
else, and each module carries a paragraph explaining why the fuel never runs
out.

**A limit turns a hang into a wrong answer.** When a step limit is too small,
the definition answers what it has so far. A drain whose bound is one short
returns a partial walk, silently. Without the limit, the same mistake is a
program that hangs, which is at least visible.

**Proving more is expensive and fragile.** An experiment extended the
checker so a walk over a table of `Bool` marks needs no limit. It took about
540 lines across `stops.rs` and `relations.rs`, slowed checking unrelated
programs by up to 1.8×, and at one point accepted or refused a program
depending on how much the optimizer had inlined, because termination is
checked again after optimization. Each extension reaches into every match
the analysis reads.

**It is a large share of checking time.** Built in release and timed best of
three, `faun check` with and without the termination pass:

| Program              |    With | Without | Saved |
| -------------------- | ------: | ------: | ----: |
| `libraries/template` | 35.3 ms | 20.8 ms |   41% |
| `aoc/201512`         | 33.6 ms | 21.7 ms |   35% |
| `libraries/json`     | 33.8 ms | 24.0 ms |   29% |
| `aoc/201515`         | 25.3 ms | 20.4 ms |   19% |
| `aoc/201519`         | 31.3 ms | 25.6 ms |   18% |
| `libraries/graph`    | 31.1 ms | 28.5 ms |    8% |

Checking a small program in under 10 ms is a goal; this pass is the largest
single piece of it that can simply go.

**Refusals report the checker's limits as the program's fault.** "Nothing
here shows `walk` stops" is said of programs that stop, where the proof is
out of the checker's reach. The same message cannot tell a user whether
their program loops or the compiler lost track of it.

**The optimizer needs less than totality.** Two passes rely on every call
coming back, and both only ever skip work nothing needs: fusion stops a
producer where its consumer stops (`barb/fuse.rs`), and pruning drops a loop
whose answer nothing reads (`ir/prune.rs`, "every loop comes back: each is a
total definition's tail call"). A rule that says unneeded pure work may be
left out keeps both sound, with no proof of anything.

## Design

### What a program means

A pure definition's call either answers or never comes back. Evaluation
stays eager and in order: every argument is evaluated before the call it is
handed to, and bindings in the order written. Recursion that exhausts the
stack remains what it is today, target resource exhaustion, outside the
value semantics.

**Unneeded pure work may be left out.** A value is needed where the
program's behaviour depends on it: it is handed to a host call, it is the
program's answer, or a match deciding either of those takes it apart. A
pure computation, one that reaches no host call, whose result is not needed
need not be evaluated. Leaving it out changes nothing a program can observe
except that a computation that would never have come back does not hang
the program. So:

- A needed call that never comes back hangs the program there, after every
  host effect written before it and before any written after.
- An unneeded one may hang the program, or may be left out. A program must
  not rely on either.

Host calls are never left out, reordered or repeated, as today.

**This is not C++'s forward-progress rule.** C++ makes a loop without side
effects that never ends undefined behaviour, and LLVM's `mustprogress` lets
the optimizer assume such a loop ends. From that assumption it derives
facts about what follows, and a false assumption makes anything possible.
With clang, this prints `hello`:

```c
int main() { while (1) ; }
void unreachable() { printf("hello\n"); }
```

The loop has no exit, so the code after it is unreachable, so the loop and
`main`'s return go, and execution falls into the next function. The rule
here licenses only leaving work out. It never lets the optimizer conclude
that anything stops, so nothing is derived from a loop that must have ended.

**`&` and `|` stay ordinary definitions.** Both are definitions in
`bool.fn`, `and(True, True) -> True` and `or(False, False) -> False`, with
no special evaluation rule. Where `a` is `True`, `a | b` does not need `b`,
so `b` may be left out: a `b` that never comes back may or may not hang the
program, and a program must not rely on either. No operator becomes control
flow in the grammar.

### The analysis goes

`validate` keeps its structural checks and no longer asks whether anything
stops, before optimization or after it. `barb/stops.rs` and
`barb/relations.rs` go, except the two things other passes read from
`stops.rs` that are not about stopping: `breakers`, which inlining uses to
choose loop breakers, and `callees_first`, which folding orders definitions
by. Both move to a module of their own.

The two passes that relied on totality need no change, and their comments
say what they rely on instead:

- **Fusion** skips what a producer would have made past where its consumer
  stops. Nothing needs those elements.
- **Pruning** drops a loop whose answer nothing reads. Nothing needs it.

Every other stage moves, copies, merges or evaluates pure work, which the
rule never touches. Constant folding already evaluates within a budget and
declines past it, so a computation that never comes back cannot hang the
compiler.

A later pass may leave out any unneeded pure computation, not only the
recognised arithmetic cleanup drops today. That is an optimization this
allows, not part of this change.

### What stays refused

Nothing about stopping. The refusals that are not about termination stay: a
recursive call that wraps the callback it was handed in a new lambda each
time round still cannot be specialized, since it would need a definition for
every round.

## Costs

- **The guarantee goes.** "Proven total and panic free" is the first thing
  the README says, and "a total pure core" is in its feature list. Ori, which
  Faun ports, is built on the premise: its README says purity and totality
  make unused pure work unobservable. Here the rule makes it unobservable
  directly, without totality.
- **A class of mistake moves from compile time to run time.** Recursing on
  the list instead of its rest is caught today with "goes round on what it
  was handed, not on a part of it"; afterwards the program hangs.
- **Optimization can change whether a buggy program hangs.** A program whose
  unneeded pure work never comes back may hang unoptimized and finish
  optimized. Only programs that are already wrong are affected.
- **No diagnostic remains** for definitions that may not stop. The analysis
  is in the history if one is ever wanted, as an opt-in report, never a
  gate.

## Alternatives considered

**Assume forward progress, as C++ does.** The optimizer gains the most
freedom, and a looping bug becomes a miscompile rather than a hang, as the
example above shows. LLVM itself moved away from assuming it everywhere:
before LLVM 12, Rust's `loop {}` was deleted (rust-lang/rust#28728), and the
fix made forward progress a function attribute, `mustprogress`, that a
frontend opts into.

**Keep the analysis as a fact, not a refusal.** Fusion and pruning would ask
whether the work they skip was proved to stop. That keeps 2,300 lines to
answer a question the rule above makes unnecessary, and a fact the optimizer
trusts must never be wrong, which is the kind of subtlety the experiment
kept tripping over.

**Make nontermination fully observable.** Fusion would fuse only consumers
that read every element, and pruning keep every loop a definition wrote.
Sound without any rule, but it gives up optimizations on programs that stop,
to preserve the behaviour of programs that do not.

**Keep totality, with an escape hatch.** A `partial` marker on a definition,
as Idris, Lean and Agda have, keeps the guarantee by default. It keeps the
checker's cost and its refusals for every unmarked definition, and adds a
word to the language.

**Keep things as they are.** The step limits are now concentrated in the
graph library's drains, so the visible cost there is one argument per call.
The checking time, the refusals of programs that stop, and the analysis's
growth remain.

## Implementation impact

1. **Remove the check.** `validate` stops calling `stops`. Move `breakers`
   and `callees_first` to a module of their own, then delete the rest of
   `barb/stops.rs` and all of `barb/relations.rs`.
2. **Remove the refused programs about stopping.** 14 cases in
   `crates/cli/tests/refused/`, from
   `a_definition_that_may_not_stop_is_refused_at_its_looping_call` to
   `multiplying_by_one_grows_nothing`, are now accepted programs. They go;
   `just bless` confirms nothing else changed.
3. **Rewrite the promises.** The README's opening example and feature list;
   the Barb README's rule that every function with a body must be total, its
   description of `stops.rs`, and a statement of the rule under what a
   program means; the standard library README's note that host loops are
   "each bounded by fuel so it is seen to stop", and its note that
   callbacks' calls are "seen to stop"; `optimize.rs`'s "Validation/totality
   must precede this"; the comments in `fuse.rs` and `prune.rs`, which cite
   the rule.
4. **Drop step limits written only for the checker**, a library at a time:
   the graph library's `drain_stack`, `drain_queue` and `stored_edges`
   first. Bounds that mean something to the program stay.

## Testing

- A program with a definition that never stops, which no refused case now
  describes, is accepted by `faun check`.
- A program that needs the answer of a call that never comes back hangs:
  run under a timeout and expected to reach it. A host effect written before
  the call happens; one written after does not.
- Every program the suite checks today still builds and answers as before,
  and the size and speed benchmarks do not move.
- `faun check` on the ported programs is faster by about the measurements
  above.

## Open questions

None. Faun diverges from Ori here for good: a program ported from Ori means
the same, since everything Ori accepts stops, but a Faun program need not run
under Ori's rules.

## Origin

Porting a graph library, whose worklists needed step limits the checker
could not do without, led to an experiment extending the checker to prove
them. It worked, but at a cost to the compiler out of proportion to the
limits it removed, and raised the question of what the check was for.
Following it through, the optimizer turned out to need only that unneeded
work may be skipped, not that every call comes back.

## Errata

**2026-09-29.** Two machine-tier passes needed more than a comment. Building
a program whose needed call never comes back showed both:

- **Pruning** dropped a loop that never breaks, because nothing read its
  answer, and left the function holding it with nothing after the loop and
  no terminator. Such a loop is not unneeded work: what follows is reached
  only because it does not come back. `ir/prune.rs` now keeps a loop that
  never breaks and an `if` with an arm that never comes back.
- **Lowering** turned a definition called from one place, and going round
  only by calling itself, into a loop in its caller, with the caller's
  instructions after it. Where every path goes round again the loop never
  leaves, and nothing may follow it; `once_round` in `ir/lower.rs` now leaves
  such a definition a function.

One limitation remains. Range analysis reads a term nothing ever answers as
able to hold anything, so a value that never exists, handed to a host call
that must be proven to fit a word, is refused: `host.exit!(spin(3))` with
`spin` never coming back. `host.println!(spin(3).to_str())` builds and hangs.
