# Computation

This note owns what running a Faun program means: strict evaluation in the
order written, purity, the rule that pure work nothing needs may be left
out, termination not being checked, and loops as tail calls.

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

Nothing changes in place. `=` binds a name again; it never changes a value,
so `snapshot = order` stays what it was when `order` is bound again. A
lambda assigns only its own names, and a loop is a function of the names it
carries, so a definition with steps and loops is as pure as one without.

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

## Termination is not checked

A pure call either answers or never comes back. A needed call that never
comes back hangs the program there, after every host effect written before
it and before any written after. Replace `ignored` above with
`host.println!(spin(0).to_str())` and the program hangs. Recursion that
exhausts the stack is the target running out of room, outside what a
program means.

Nothing about stopping is refused. The decision, its measurements and its
costs are in the [termination proposal](proposals/approved/termination.md).

## Loops are tail calls

A `for` or `while` loop is a recursive function of the names it carries,
calling itself for the next round in tail position, so a round costs a
jump and nine million rounds run in constant stack
([loops proposal](proposals/approved/loops.md)):

```ruby
summed(xs) -> (
  total = 0
  for x in xs do (
    if x > 100 continue
    total = total + x
  )
  total
)
```

## `&` and `|`

`&` and `|` on `Bool` are calls of ordinary definitions in `bool.fn`:

```ruby
and : (Bool, Bool) -> Bool
and(True, True) -> True
and(_, _) -> False
```

The grammar reads them as infix operators like any other. The checker
treats their right side as possibly not worked out: `?`, an effect, and a
binding of the body's names are each refused there.

Today the compiler works out the right side only where the left has not
decided. Programs rely on it: this parity check stops only because `|`
skips `odd(n - 1)` at nought, since `0 - 1` is `0` for a `Nat`.

```ruby
even : Nat -> Bool
even(n) -> n == 0 | odd(n - 1)

odd : Nat -> Bool
odd(n) -> n != 0 & even(n - 1)
```

The standard README promises this. The termination proposal says the
opposite: the right side may be left out where the left decides, a program
must not rely on it either way, and no operator becomes control flow. The
two are not yet reconciled.

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
the consumer stops. Pruning drops a loop whose answer nothing reads.
Constant folding works out closed calls during compilation, within a
budget.

The cost is that work the optimizer misses is done: `select` works out
both candidates, and an unfused pipeline builds its intermediate lists.
There are no infinite lists and no memoized lazy values. The recourse is
`if` where a choice should skip work, and a loop or explicit state where
demand is part of the algorithm.

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

### Why not check termination?

Faun checked it once, as Ori does, and stopped. The guarantee caught a real
but rare class of bug, and cost much more: step limits written only so the
checker would accept loops that plainly stop, limits that turned a hang
into a silently wrong answer, 8 to 41% of checking time, and refusals of
programs that stop, reported as the program's fault. The optimizer needed
only the rule that unneeded pure work may be left out. The
[termination proposal](proposals/approved/termination.md) has the
measurements.

### Why not assume forward progress, as C++ does?

C++ makes a loop without side effects that never ends undefined behaviour,
and LLVM's `mustprogress` lets the optimizer assume such a loop ends. From
that assumption it derives facts about the code after the loop, and when
the assumption is false, anything can happen: the proposal shows clang
falling out of an endless `main` into the next function. Before LLVM 12
the same assumption deleted Rust's `loop {}` (rust-lang/rust#28728).

Faun's rule licenses only leaving work out. The optimizer never concludes
that anything stops, so a loop that never ends is a hang, never a
miscompile. The cost is the optimizations that need that conclusion:
pruning must keep a loop that never breaks even when nothing reads its
answer, since the code after it is reached only if it ends.

### Why did Ori require totality, and what did Faun give up?

Ori admitted only programs it could prove stop. Its reason was the
optimizer: with every call known to come back, deleting, fusing, moving or
evaluating pure work at compile time needs no side condition. It made the
proof a gate rather than an annotation because totality spreads through
the call graph, so one partial function would quietly disable rewrites in
every caller. And "every program stops" was a guarantee a user could run
untrusted input under.

Faun found the optimizer needs less: only that unneeded work may be
skipped. What it gave up:

- **The guarantee.** A pure call may never come back.
- **A class of compile-time error.** Recursing on a list instead of its
  rest was refused; now the program hangs.
- **Freedom to move needed work.** A call that might not come back keeps
  its place between the host calls around it.
- **One kind of determinism.** Unoptimized and optimized builds of a buggy
  program may differ in whether it hangs.

What it gained: no step limits, `while` loops whose test is partway
through, as in `while True do ( … if done break … )`, and checking without
the analysis, whose 2,315 lines are gone. Exhaustive matching stays, for
its own reason: a pure function answers for every input it can be given
([pattern matching](forms/pattern-matching.md)).

### Why are `&` and `|` not control flow in the grammar?

They are methods, as every operator is: `&` is `and`, logical on `Bool`
and bitwise on the words, and a type gives it meaning by defining the
method ([operators](forms/operators.md)). Making them control flow in the
grammar would give two operators an evaluation rule no other call has. The
forms that choose what runs are `if`, arms and leaving lines.

Because `?`, effects and bindings are refused on the right side, that side
is pure and cannot leave. Whether it is worked out changes only how long
the program takes, and whether a call there that never comes back hangs
it. That makes short-circuiting an evaluation question rather than a
grammar one, which is where the two documents above disagree.

## Related

- [Termination proposal](proposals/approved/termination.md): the decision
- [Loops proposal](proposals/approved/loops.md): loops as tail calls
- [Effects](forms/effects.md): `!`, `Host` and the order of effects
- [Operators](forms/operators.md): operators as methods, `&` and `|`
- [Memory](machine/memory.md): reference counting and in-place reuse
- [Dependent types](dependent-types.md): why types never run code
