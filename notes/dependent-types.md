# Dependent types

This note owns why Faun has no dependent types and no user-written proofs,
and keeps open the one restricted form that may still be worth having:
indexed types. The README says it in one line: "No dependent types or
user-written proofs."

A dependent type is a type that mentions a value: a list whose type says
its length, `Vec(3, Nat)`, or a function whose result type depends on its
argument. In a full dependent language any program term can stand in a
type, and the checker decides whether two types are equal by evaluating
those terms.

## What Faun has instead

Faun's types are Hindley–Milner with rows ([types](types.md)). A type never
mentions a value, and type checking never runs a program. The ground that
dependent types cover in other languages is covered by other means:

- **Inference.** What follows is checked with no signature written, so the
  checks cost nothing in a program's text ([types](types.md)).
- **Exhaustive matching.** Every match covers every value of its type, so
  there is no partial function to prove safe
  ([pattern matching](forms/pattern-matching.md)).
- **Operations defined for every input.** Where a dependent language would
  ask for a proof that an index is in range or a divisor is not zero, Faun
  answers something for every input:

  ```ruby
  expect [10, 20].get(5) == Err(OutOfBounds)
  expect [10, 20].get_or(5, 0) == 0
  expect [1, 2, 3].zip([4]) == [(1, 4)]
  expect 7 / 0 == 0
  expect U8.of_nat(300) == U8.of_nat(44)
  ```

- **Invariants kept by a module.** `Str` is UTF-8 bytes behind a private
  constructor, so only `Str`'s own module can build one, and
  `Str.from_utf8` checks the bytes once. The invariant is held by who may
  build the value, not by a proof carried with it.
- **Linear resources.** A `File` must be used up exactly once on every path,
  checked with nothing written ([effects](forms/effects.md)).
- **Failure rows in signatures.** A signature's row says exactly which
  failures a function can answer, and the checker holds the body to it
  ([tags](values/tags.md)).
- **Facts found by shape.** The compiler derives what it needs from what a
  definition computes rather than from a declared type: a numeral is checked
  against its type's range (`big : U8` with `big = 300` is refused), `len`
  is answered from the length a list holds, and range analysis finds which
  values fit a machine word.

## Rationale

### Why no dependent types?

Most code does not want them. Lean and other provers are making real
progress on proving mathematics, and that is where a proof is the product.
In ordinary software the product is the program, and a proof is a cost
paid next to it.

What people want from a type system in ordinary code is a short program
that says enough of its business rules and domain invariants to be checked.
Concise code is easier to review. A dependent signature is a second program
that a reviewer must also read, and it is often longer than the first.

Requirements also change constantly. A program whose types carry proofs
must be re-proved each time a rule changes, so every change costs two
edits, and the second is often the harder one. That slows iteration.

There is no visible demand. LLMs can now write proofs for general-purpose
languages, yet teams are not bringing proofs into their codebases or
treating them as a selling point. Even with proofs cheaper, nobody seems
to want them outside mathematics.

Leaving them out keeps the compiler fast and the code easy to read, and
holds to Faun's goal of being simple to understand, with very few concepts.

Concision, simplicity and speed of iteration are better goals for ordinary
software, and dependent types run against all three. The cost is that an
invariant a type cannot state is checked by a test, a `Result`, or a
module boundary instead.

Ori, and an earlier design before it, ruled out full dependent types from the
start, to keep checking decidable and inference complete. Ori kept indexed
types as the one extension under study. Faun inherits that line.

### Why not let an LLM write the proofs?

Cheap proofs remove only one of the costs above. The type a proof answers
to is still written, read and reviewed by people, and it is the type that
says what was proved. The proof still breaks when a requirement changes,
and the checker still has to evaluate it. If demand appears, the question
can be asked again with evidence.

### What would they cost the language?

An experiment built five small dependent cores with Faun's surface: a
predicative Martin-Löf type theory (MLTT), quantitative type theory (QTT),
and cores inspired by CDLE, BendTT and observational type theory
([benburk/toy-type-theory](https://github.com/benburk/toy-type-theory)).
Every one needed syntax Faun does not have: universes (`Type0`), dependent
binders, quantities, erasure markers. Even the identity function needs them.
In Faun:

```ruby
id(x) -> x
```

In the MLTT core:

```text
id : (A : Type0) -> (x : A) -> A
id(A, x) -> x
```

QTT writes `(0 A : Type0) -> (1 x : A) -> A`, BendTT `{A : Type0}`, and
CDLE `forall A.` with `gen(A) ->` in the body.

Every core also excludes general recursion, since a checker that normalizes
terms must know they stop. QTT's core cannot define addition; MLTT's
defines it through an eliminator and a separately declared motive. Faun's
`Nat.add` is two clauses (`standard/nat.fn`):

```ruby
add(0, y) -> y
add(Succ(n), y) -> Succ(n + y)
```

### What would they cost the checker?

To decide whether two dependent types are equal, the checker normalizes
the terms in them: it runs the program. The MLTT core accepts
`plus_one : Eq(Nat, plus(one, one), succ(one))` only by computing
`plus(one, one)` while checking.

That collides with two of Faun's decisions. Termination is not checked
([totality](totality.md)), so a term in a type may
never come back, and the checker would hang on it. The only defence is a
budget, and the toy QTT and BendTT checkers have exactly that: a node
budget on normalization, which their READMEs say can reject valid
programs. That is the step-limit problem dropping termination checking removed,
moved into the type checker. And checking a small program in under 10 ms
is a goal; a checker that runs user code has no bound on its own time.

### Why not refinement types?

Refinement types, as in Liquid Haskell, attach a predicate to a type,
`{r : Nat | r < b}`, and hand the obligations to an SMT solver, so no proof
is written. They are the cheapest dependent form, and the closest to
indexed types below.

They still put predicates in signatures, which Faun keeps optional, and
still need re-stating when a rule changes. A solver's time is hard to
predict, and its failure reads as a type error the user cannot argue with.
Faun covers the common cases, the ones refinements are usually shown on, by
defining the operation everywhere instead: division by zero is zero, a
lookup out of range is an `Err`.

The cost is that those cases give an answer rather than a compile error:
`7 / 0` is `0`, and a program that meant something else is wrong at run
time. The recourse is an `expect` test, or a `Result` the caller must
match.

### Why not optional or gradual proofs?

A proof is never only local. A function whose type says its argument is
non-empty passes that obligation to every caller, and a library that
adopts proofs pulls them into each program that uses it. Ori made the same
argument the other way about totality: one partial function demotes every
caller.

Optional proofs also do not make the language smaller. Every reader must
still know the proof syntax to read a library, and the checker must still
normalize terms wherever proofs appear. [Totality](totality.md) rejected
a `partial` marker for the same reason: it keeps the cost and adds a word
to the language.

## Open: indexed types

Indexed types are the restricted form that may still fit: a type carries a
value from a small decidable language, such as a length, and a decision
procedure checks it without running the program. Faun already has their
lowest tier, tags as phantom type parameters. Whether to go further is
open; [indexed types](indexed-types.md) owns the question.

## Related

- [Types](types.md): what the type system is, and why it stops at HM
- [Indexed types](indexed-types.md): the restricted form left open
- [Computation](computation.md): why termination is not checked
- [Totality](totality.md): what a total language would allow types to do,
  why termination stopped being checked, and the 10 ms goal
- [Pattern matching](forms/pattern-matching.md): exhaustive matching
- [Effects](forms/effects.md): linear resources
- [Numbers](values/numbers.md): division by zero, word ranges
