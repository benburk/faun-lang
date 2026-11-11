# Computation

This note owns what running a Faun program means: strict evaluation in the
order written, purity, the rule that pure work nothing needs may be left
out, termination not being checked, and iteration as tail calls.

## Strict evaluation

Faun evaluates eagerly. Every argument is worked out before the call it is
handed to, and a block's bindings in the order written. Apart from work
nothing needs (below), only a choice skips work: `if` works out the branch
it takes, arms the arm that matches, and a definition the clause it
selects.

`Bool.select` is an ordinary definition, so both of its candidates are
worked out before it is called. `if` is the form that chooses:

```ruby
halve(n) -> if n == 0 then 0 else n / 2

expect True.select(1, 2) == 1
expect halve(10) == 5
```

Effects happen in the order their lines are written. An effect stands on a
line of its own, or is bound to a name there; one inside an argument is
refused with "effect `read_to_end!` must stand on its own". So the lines of
a body are the order of its effects:

```ruby
main!(host) -> (
  host.println!("one")
  host.println!("two")
  host.exit!(0)
)
```

## Purity

A definition whose name does not end in `!` is pure: it computes an answer
from its arguments and does nothing else. It cannot call an effect, which
is refused with "pure definitions cannot call effect `println!`". Effects
come only from the `Host` a program is handed
([effects](forms/effects.md)).

Nothing changes in place. `=` binds a name again, shadowing the binding
before it to the end of its block; it never changes a value, so `snapshot =
order` stays what it was when `order` is bound again, and a definition with
steps is as pure as one without.

## Unneeded work may be left out

A value is needed where the program's behaviour depends on it: it is handed
to a host call, it is the program's answer, or a match deciding either of
those takes it apart. A pure computation whose answer is not needed may be
left out. Here `spin` never comes back, and nothing reads `ignored`:

```ruby
spin : Nat -> Nat
spin(n) -> spin(n + 1)

main!(host) -> (
  ignored = spin(0)
  host.println!("finished")
  host.exit!(0)
)
```

The program may print `finished`, or may hang before it; a program must not
rely on either. Host calls are never left out, reordered or repeated.

The compiler leaves such work out where it can see it. A list read only for
its first element, from a definition joining what its own calls answer, is
built only as far as that: `models(formula).first()`, over a search
answering every model, stops at the first, the second branch searched only
where the first found none ([`head.rs`](../crates/core/src/barb/head.rs)).
So does a test of whether it is empty, a `filter` or a `map` read for its
first element, and a search over it that stops at what it accepts, as
`find`, `any` and `all` do: `!models(formula).is_empty()` and
`models(formula).filter(fits).first()` stop at the first model they need.

## Termination is not checked

A pure call either answers or never comes back. A needed call that never
comes back hangs the program there, after every host effect written before
it and before any written after. Replace `ignored` above with
`host.println!(spin(0).to_str())` and the program hangs. Recursion that
exhausts the stack is the target running out of room, outside what a
program means. On x86-64 Linux and on the 6502 the program says
`stack overflow` on standard error and exits with status 3; under wasmtime
the engine stops it with a trap. The 6502 holds 128 return addresses, so
there calls run out of room at most 128 deep.

Nothing about stopping is refused. Why, what it measured and what it cost
are in [totality](totality.md).

## Iteration is tail calls

Faun has no loops: a walk is a function calling itself, a fold, or a
library function ([iteration](iteration.md)).
A call whose answer is its caller's answer is a jump on every target, so a
step costs a jump and millions of steps run in constant stack:

```ruby
summed : (List(Nat), Nat) -> Nat
summed([], total) -> total
summed([x, *xs], total) if x > 100 -> summed(xs, total)
summed([x, *xs], total) -> summed(xs, total + x)
```

A walk that leaves early answers instead of calling itself again, or folds
with `fold_until`, whose step answers `Continue(state)` or `Stop(state)`.

## `&` and `|`

On `Bool`, `&` and `|` are the connectives that conditions are joined
with, and work out their right side only where the left has not decided.
A program may rely on that: this parity check stops only because `|`
skips `odd(n - 1)` at nought, since `0 - 1` is `0` for a `Nat`.

```ruby
even : Nat -> Bool
even(n) -> n == 0 | odd(n - 1)

odd : Nat -> Bool
odd(n) -> n != 0 & even(n - 1)
```

The connective is the operator, not the function. `a.or(b)` and
`Bool.or(a, b)` are ordinary calls of the definitions in `bool.fn`, and
work out both arguments first, as every call does. On any other type, `&`
and `|` are ordinary calls of the type's `and` and `or`.

The right side of a connective may be skipped, so `?`, an effect, and a
binding of the body's names are each refused there, and names a test on
the left binds are seen on the right only because it runs only where the
test held.

## Rationale

### Why strict rather than lazy?

Lazy evaluation, as in Haskell, works out a value only when it is first
needed. That needs a thunk for every suspended value, a cell to update
once it is forced, and a runtime that forces it. Strict evaluation needs
none of these: a value exists when it is matched.

The memory model depends on that. Reference counting and in-place reuse
([memory](machine/memory.md)) work on data that exists, and a value is
freed or reused at a point the compiler can see. A suspended computation
holds what it reads for as long as it waits.

Much of what laziness is used for is recovered by the compiler instead.
Fusion runs a walk that builds a list together with the walk that takes it
apart, so the list in between is never made, and stops the producer where
the consumer stops. Pruning drops a walk whose answer nothing reads.
Constant folding works out closed calls during compilation, within a
budget.

The cost is that work the optimizer misses is done: `select` works out
both candidates, and an unfused pipeline builds its intermediate lists.
There are no infinite lists and no memoized lazy values. The recourse is
`if` where a choice should skip work, and a walk carrying explicit state
where demand is part of the algorithm.

### Why pure?

Purity is what makes the rule above possible. A computation that reaches no
host call does nothing but produce its answer, so where nothing needs the
answer, dropping it changes nothing a program can see. If any call could
write to a file, every call would have to be kept.

It also keeps a program readable in pieces. A call cannot change what it
is handed, so only a line `order = …` changes `order`. Every effect is
marked with `!` where it is called, and needs the `Host` passed to it, so a
reader can see which calls touch the world.

The cost is that mutation is not a language feature. A step is written
whole, `order = order.append(node)`, and effects need `Host` threaded to
them. In-place update is the compiler's to find: a list nothing else holds
is written where it lies.

### Why may unneeded work be left out?

Because the optimizer needs it, and nothing more. Fusion skips what a
producer would have made past where its consumer stops, and pruning drops a
walk whose answer nothing reads. Both only skip work nothing needs, and the
rule makes that sound with no proof that the skipped work would have
stopped. The rule licenses only leaving work out: the optimizer never
concludes that anything stops, so a walk that never ends is a hang, never a
miscompile ([totality](totality.md) weighs this against C++'s
forward-progress assumption).

The alternative was to make a hang fully observable: fuse only consumers
that read every element, and keep every walk a definition wrote. That is
sound without any rule, but gives up optimizations on programs that stop to
keep the behaviour of programs that do not.

The cost is that optimization can change whether a buggy program hangs: one
whose unneeded pure work never comes back may hang unoptimized and finish
optimized. Only programs that are already wrong are affected. The recourse
is the rule itself: a program must not rely on either outcome.

### Why not check termination?

Faun checked it once, as Ori does, and stopped on 2026-09-29. The guarantee
caught a real but rare class of bug and cost much more: step limits written
only for the checker, limits that turned a hang into a silently wrong
answer, 8 to 41% of checking time, and refusals of programs that stop. The
optimizer needed only the rule above. What Faun gave up is mostly one
meaning for pure code: with every pure call known to come back, the order
it runs in could not be observed, the optimizer could move work as freely
as it skips it, and `&` and `|` would need no promised order. Exhaustive
matching stays, for its own reason: a pure function answers for every input
it can be given ([pattern matching](forms/pattern-matching.md)).
[Totality](totality.md) owns the decision, its measurements and the
alternatives weighed.

### Why are `&` and `|` on `Bool` a condition form, not calls?

Because a condition needs one. In `r is Ok(v) & v < 100` the right side
reads a `v` that exists only where the left held, so it can be worked out
only there, in any language, total or not. Once names flow along `&`, it
chooses what runs, as `if`, arms and leaving lines do. Promising the
choice where nothing is bound too, as in `even` above, costs nothing more.

Only the operator chooses. A method call works out its arguments before it
is made, with no exception, so the rule for a call stays one rule, and the
special case is visibly syntax. Making `&` strict instead would mean
giving up names flowing along it, and nesting an `if` for each test, or
making `&` strict only where its left binds nothing, which is a worse
special case. The [totality](totality.md) note weighs this against a
language where the question could not be observed.

## History

- **2026-09-29:** termination stopped being checked, and the rule that
  unneeded pure work may be left out replaced the guarantee fusion and
  pruning had relied on ([totality](totality.md)). Building a program whose
  needed call never comes back showed two machine-tier passes needed more
  than the rule: pruning dropped a loop that never breaks, leaving its
  function with no end, and lowering turned a definition going round only by
  calling itself into a loop in its caller with the caller's instructions
  after it. Both now keep code reached only because something never comes
  back: `ir/prune.rs` keeps a loop that never breaks and an `if` with an arm
  that never comes back, and `once_round` in `ir/lower.rs` leaves such a
  definition a function.
- **2026-10-04:** when `if` was built, `&` and `|` on `Bool` began working
  out their right side only where the left had not decided, though the
  termination decision still said a program must not rely on it.
- **2026-11-03:** the skip was promised and given to the operators. Until
  then the compiler found `and` and `or` by name, so every spelling skipped;
  since, `a.and(b)`, `a.or(b)` and `Bool.and(a, b)` are ordinary calls.

## Related

- [Totality](totality.md): what requiring every call to come back buys and
  costs, and why Faun stopped checking it
- [Iteration](iteration.md): walks as tail calls, and why there are no
  loops
- [Effects](forms/effects.md): `!`, `Host` and the order of effects
- [Operators](forms/operators.md): operators as methods, `&` and `|`
- [Memory](machine/memory.md): reference counting and in-place reuse
- [Dependent types](dependent-types.md): why types never run code
