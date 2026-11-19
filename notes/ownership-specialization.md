# Specializing by ownership

A Faun program never says whether an argument is borrowed, owned or copied,
nor whether what a function answers is new. Those are facts about how a
value is held, and the compiler works them out. This note, written on
2026-11-19, is the design for working them out per call rather than per
definition: making a definition into code for each way its arguments and
its answer are held, as monomorphization makes one generic definition into
code for each type it is used at. Nothing here is built. What the compiler
does today is owned by [memory](machine/memory.md); this note says it again
only where the design starts from it.

## The idea

A definition is written once, and the compiler makes it into the code each
use needs, along three axes:

| Written once               | Made into                           |
| -------------------------- | ----------------------------------- |
| a generic definition       | a definition per concrete type      |
| a `Nat`                    | a word, where its range fits one    |
| a definition taking a list | code per way its arguments are held |

The first two are built. Types are specialized per call
([types](types.md#specialization)); a `Nat` is held as a word where range
analysis bounds it ([numbers](values/numbers.md#how-a-nat-runs),
[ranges](machine/ranges.md)). The third is this note.

An argument that holds a count can reach a function in one of three ways:

- **Borrowed:** the caller keeps it, and the function only reads it.
- **Owned and held once:** the caller hands over its claim, and nothing
  else holds the value, so the function may write it where it lies.
- **Owned and perhaps shared:** the caller hands over a claim, but
  something else may hold the value too, so a write must copy first.

An answer is either **new**, held by nothing but the caller it is handed
to, or **perhaps shared**, as an argument handed back unchanged may be.
Specializing by ownership makes a definition into a version for each of
these its callers need: the version handed a value held once writes in
place and asks nothing, the version handed a shared one copies or borrows
and asks nothing either, and a caller handed an answer known to be new
writes it in place in turn.

"Specialize" is the accurate word, not "generic". A generic definition has
a parameter the programmer writes, a type variable or a bound. Here the
programmer writes nothing: the source is the same whatever the ownership,
and the copies are the compiler's, made from what it knows at each call,
as range analysis makes a word of a `Nat` no one declared small.

## Today

The compiler decides ownership once per definition, not per call:

- **Borrowed or owned** is one fact per parameter of each function
  (`crates/core/src/ir/ownership.rs`). A parameter is owned where the
  function takes a claim to it anywhere, a write, a field of a new cell, a
  loop's state or an owned parameter of something it calls, and borrowed
  otherwise. It is settled to a fixed point, since handing a parameter on
  to an owned one consumes it. Every caller passes it the same way: moving
  its own claim where the call is the argument's last use, and retaining a
  new one otherwise.
- **Writing in place** is decided as the program runs. Legalization
  (`crates/core/src/ir/legalize.rs`) makes each write of a buffer read the
  buffer's count and compare it with one: held once, it is written where it
  lies; held more than once, it is copied first
  (`crates/core/src/ir/sequence.rs`). The test is a load, a comparison and a
  branch for elements holding no counts, and a call of the layout's routine
  for elements that do.
- **Known before the program runs**, within one function, that a buffer is
  held once, a replacement asks nothing (`crates/core/src/ir/uniqueness.rs`).
  That is known of a buffer answered by a replacement, a push or an append
  and handed on since only by being moved, and of a buffer a loop carries
  and rewrites every time round, which is made one held once on entry,
  copied there if it is shared. It covers only buffers whose elements hold
  no counts, and only replacing an element: adding to either end and
  joining ask every time.

So a parameter, owned or not, is never known to be held once, and neither
is anything a call answers: the analysis stops at a function's edges. A
function handed a buffer it rewrites asks the count at every write, however
every caller holds it, and a caller handed back a buffer the function just
built asks again before its own write.

Two things already specialize by ownership in effect. Barb inlines a small
definition into its caller, and the inlined body is then analysed with
everything the caller knows, ownership included; the gap is what is too
large or too recursive to inline. And the loop that makes its buffer one
held once on entry is a specialization in miniature: one copy, or none,
outside the loop, and a body that never asks.

Ranges, the second axis, are also one fact per definition: a definition
starts from what every call hands it, joined
([ranges](machine/ranges.md#what-a-term-says)). The precedent for copying
per call is Barb's specialization by known values
(`crates/core/src/barb/specialize.rs`): a recursive definition handed
different constants by its callers gets a copy for each, at most four, of
definitions no larger than a bound, and a copy is kept only where it
decides a match its original could not. Ownership copies would need the
same three limits.

## What it would add

Each call site would know, as it knows an argument's type, how it holds
each argument it passes: whether it is the argument's last use, and
whether the value is one held once there. Each function would then be made
into a version per combination its callers ask for, among the parameters
whose mode changes what the function does:

- **A version for arguments held once** writes them in place with no test,
  and has no copying branch, so its code is smaller and its control
  simpler for what follows.
- **A version for arguments the caller keeps** borrows them: the caller
  neither retains before the call nor releases after, and a write in the
  function copies without asking.
- **Where nothing is known**, the version is the one compiled today, with
  its test. So a call site the analysis cannot read loses nothing.

Answers come second. A function whose every path answers a buffer it built,
or wrote in place, answers one held once, and its callers' writes of that
answer need no test. That needs no copies: it is one fact per definition,
like borrowed or owned, and is the first thing to build. Copies are needed
only where the answer's ownership follows an argument's, as when a path
hands the argument back unchanged:

```ruby ignore
bump(counts, at) -> counts.put(at, counts.get(at).ok_or(0) + 1)
pad(xs, n) -> if xs.len() >= n then xs else pad(xs.append(0), n)
```

`bump` answers a buffer held once whatever it is handed, since a
replacement writes one or copies one. `pad` answers what it was handed
where that is already long enough, so its answer is new only in the
version handed one held once.

Recursion closes quickly. A version handed a buffer held once and writing
it hands on one held once, so it calls itself. A version handed a shared
buffer copies at its first write and from then on holds its own, so it
calls the version for buffers held once. Two versions of a self-recursive
function cover it, which is the loop's entry copy above, made for recursion
that is not a loop.

## What it would cost

- **Code size.** Each version is a copy of the function through the
  machine tier and the target. Images are measured, the 6502's most of
  all, and a version with no copying branch is smaller than the original,
  so whether a program grows is a measurement, not a given.
- **Compile time.** Each version is lowered, legalized and emitted again,
  and the machine tier is most of what a compile spends beyond the
  standard library ([compile time](compile-time.md)).
- **A cap.** Versions multiply with types and callbacks already
  specialized, and with each parameter whose mode matters. So, as Barb
  copies a definition for known values at most four times, and only where
  the copy decides something, a version would be made only for a parameter
  some write in the function reads, and kept only where it removes a test
  or a copy its caller runs.
- **Fields.** A list taken out of a record's field is held by the record
  too, unless the record dies there. Today nothing in the machine tier
  follows ownership through a cell: cells are not written in place, and a
  field read retains. So a list carried in a record, as state often is, is
  never known to be held once, and versions would not change that until
  fields are followed, or cells written in place, as
  [memory](machine/memory.md#writing-in-place) plans.
- **Elements that hold counts.** Writing over an element that holds a count
  gives that count up, which the layout's routine does; static uniqueness
  today covers only elements that hold none. A version for those buffers
  saves the test but not the call.
- **Reading the output.** `faun emit target` would show several versions of
  a function, which must be named so a reader can tell which call takes
  which.

## Measuring first

How much the tests and copies cost is not known, and the test is cheap:
a load, a comparison and a branch a processor predicts well when the same
buffer is held once every time. So the work starts with counting, in the
suite and the probes, before any version is made:

1. **Every count test executed,** by the write it guards, and what it
   found: held once or shared. The machine IR's evaluator
   (`crates/core/src/ir/evaluate.rs`) already counts the calls of each
   function and the bytes stored, as the cost oracle representation work
   is judged by, and runs a legalized program, so it could count tests by
   site too without touching a target.
2. **Every copy those tests made,** and its bytes: a copy made because a
   caller still holds the value is required, and no version removes it;
   one made because the analysis could not see the value was held once is
   what this design is for.
3. **Every retain and release at a call** to an owned parameter, where the
   caller keeps the argument.
4. **Where each sits:** in a loop, in a recursion, or in code run once, and
   what share of the program's instructions it is.
5. **Which of them one fact per definition removes,** an answer known to be
   new or a parameter known held once by every caller, and which need
   versions.

The baseline profile of n-body spent 8% of its time releasing and 36%
allocating ([memory](machine/memory.md#why-reference-counting-and-not-a-tracing-collector));
how much of that is tests at function edges is what step 1 would say. If
the tests that remain sit outside hot loops, or the per-definition facts
remove most of them, the versions are not worth their code, and only the
facts are built. A change built from this goes through the ratchet like
any other, and is accepted only where speed, memory, size and compile time
together say so.

## Related work

- **Lean 4.** Ullrich and de Moura, "Counting Immutable Beans: Reference
  Counting Optimized for Purely Functional Programming" (IFL 2019), infer
  for each function which parameters are borrowed and which owned, to a
  fixed point, as Faun does today. Lean reuses a cell and updates an array
  in place where a test as the program runs finds it unshared, and lets a
  programmer mark a parameter borrowed, `@&`. One convention per parameter
  per function, not per call.
- **Koka.** Perceus (Reinking, Xie, de Moura and Leijen, PLDI 2021) places
  counts precisely and reuses a cell a match takes apart for a constructor
  of the same size, where its count is one when the program runs. "Functional
  but in-place" names the style this allows; Lorenzen, Leijen and
  Swierstra's FP² (ICFP 2023) adds a `fip` mark the compiler checks, so
  that a function written so runs in place. Koka, as far as we know, also
  lets a programmer mark a parameter borrowed. Reuse there is decided by a
  test as the program runs, as Faun's writes are.
- **Roc.** Roc's compiler runs an alias analysis over the whole program,
  Morphic, to find values nothing else holds and update them in place
  without a test, and, as we understand its design, can make a function
  into versions by what that analysis finds. We have not checked how far
  the shipped compiler goes; it may be the nearest to this note.
- **Swift.** The optimizer's function signature specialization can turn an
  owned parameter into a guaranteed, that is borrowed, one, keeping the
  original as a thunk for callers it cannot see. Swift's collections are
  copied on write by a uniqueness test as the program runs, and since 5.9
  a programmer may write `borrowing` or `consuming` on a parameter.
- **Mojo.** Each parameter's convention, reading it, mutating it or owning
  it, is written by the programmer, with an explicit transfer of
  ownership; the names have changed between releases. The compiler checks
  them rather than choosing them.
- **Linear Haskell.** Bernardy and others (POPL 2018) put multiplicities in
  function types, `a %1 -> b`, polymorphic over them, `a %m -> b`. The
  programmer writes them, and they say what a function may do with an
  argument, not how it is passed; GHC does not, as far as we know, choose
  a calling convention from them.
- **Clean.** Uniqueness types say in the type that a value is held once,
  so that it may be written in place; the compiler infers them, with
  polymorphism over uniqueness, but they are part of a function's type,
  and a program relying on a write in place states it there.

What would be Faun's own is the combination: ownership treated as a
parameter no program writes and no type shows, inferred and specialized on
like a type parameter or a range, for answers as well as arguments. Lean,
Koka and Faun today infer one convention per function and test the rest as
the program runs; Mojo, Linear Haskell and Clean write ownership in the
source or the type; Swift specializes signatures under its optimizer, and
Roc specializes for uniqueness it proves, both nearer to this note than
the rest.

## Rationale

### Why specialize rather than let a program say how it holds a value?

Because a program cannot see the difference
([memory](machine/memory.md#why-is-writing-in-place-invisible-to-a-program)).
A value cannot change, so whether a write is in place shows only in time,
and a mode written in the source would be a promise about speed that the
types would then carry everywhere, as Mojo's conventions and Clean's
uniqueness do. The compiler already knows, at each call, whether the call
is an argument's last use; it is the one placing the counts. The cost
accepted is the one memory names: how a program performs rests on facts it
does not write, and `faun emit target` is how to see them.

### Why not one fact per definition, and stop there?

One fact per definition is where to start: an answer known to be new, and
a parameter known held once by every caller, remove tests with no copies.
It stops where callers differ. A function called both with a buffer held
once and with one its caller keeps must test, and with one version per
definition the many callers that could write in place pay for the few that
cannot. Monomorphization faced the same choice for types, a boxed uniform
representation or a copy per type, and chose copies; ranges have not yet,
and are joined over callers.

## Open questions

- Whether counting the tests finds enough in hot code to build versions at
  all, or only the per-definition facts.
- Whether a version should be keyed by each parameter's mode, or only by
  those a write in the function reads.
- Whether ranges should be specialized per call in the same pass, since
  both are facts a caller knows and a callee joins.
- How versions should be named in `faun emit` output.

## Related

- [Memory](machine/memory.md): counts, borrowed and owned parameters, and
  writing in place, as built
- [Types](types.md#specialization): monomorphization, and the programs it
  refuses
- [Ranges](machine/ranges.md): what a number can be, one fact per
  definition
- [Architecture](machine/architecture.md): the tiers, and why the whole
  program is compiled at once
- [Compile time](compile-time.md): where a compile's work goes
