# Indexed types

An open question, not a decision. This note owns what indexed types are,
where they sit between Faun's types and full dependent types, what they
could buy Faun, what they would cost, and what would have to hold to adopt
them. Why full dependent types are out is
[dependent types](dependent-types.md)'s.

## What they are

An indexed type is a type with a value in it, drawn from a small language
of its own. The usual example is a list whose type says its length:

```text
Vec(3, Nat)                                  a list of exactly three
append : (Vec(m, a), Vec(n, a)) -> Vec(m + n, a)
zip : (Vec(n, a), Vec(n, b)) -> Vec(n, (a, b))
```

(None of this is Faun syntax.) The indices `m`, `n` and `m + n` are
variables and expressions, not only constants. What makes this cheaper
than full dependent types is two restrictions:

- **The index language is fixed, small and decidable,** and separate from
  the program's terms. Typically it is natural numbers under linear
  arithmetic: `m + n`, `2 * n` and `n - 1` are in, `m * n` is out, since
  multiplying two variables makes the theory undecidable. No index ever
  calls a definition the program wrote.
- **Type equality is decided by a solver, not by evaluation.** Checking
  that `Vec(m + n, a)` is `Vec(k, a)` asks a decision procedure for linear
  arithmetic whether `m + n = k`. A full dependent checker would normalize
  both types by running their terms.

So, to the question of whether indexed types are a subset of dependent
types that is easier to prove: yes, with one correction. They are
dependent, since a type mentions a value. What makes them easy is not that
indices are constants; it is that every proof obligation falls in a theory
a machine decides, so no one writes a proof and the checker never runs the
program.

## The spectrum

| Kind           | A type may mention   | Checked by           | Example   |
| -------------- | -------------------- | -------------------- | --------- |
| Simple         | other types          | unification          | ML        |
| Tag indices    | a type-level tag     | unification          | GADTs     |
| Size indices   | sizes, by equality   | unification          | Futhark   |
| Indexed        | linear arithmetic    | a decision procedure | DML, ATS  |
| Refinement     | predicates on values | an SMT solver        | Liquid H. |
| Full dependent | any term             | evaluation           | Agda      |

Each row admits more and costs more:

- **Tag indices** are already in Faun, as a phantom type parameter. A
  door's state can be part of its type, and walking through a door that
  was never opened is refused:

  ```ruby
  Closed : [Closed]
  Open : [Open]
  Door(state) : [Door(Nat)]

  shut : Nat -> Door(Closed)
  shut(n) -> Door(n)

  open : Door(Closed) -> Door(Open)
  open(Door(n)) -> Door(n)

  walk : Door(Open) -> Nat
  walk(Door(n)) -> n

  expect walk(open(shut(3))) == 3
  ```

  `walk(shut(3))` is a type mismatch. Nothing new is needed for this tier.
- **Size indices** let a type carry a size, compared only for equality.
  Futhark's array types, `[n]f64`, are this; Rust's const generics,
  `[T; N]`, are close. Unification already decides it: a size is one more
  kind of type variable, and `zip` of two `[n]` arrays checks without a
  solver. Arithmetic on sizes, as `append` needs, is the next row.
- **Indexed types** add arithmetic on indices. Dependent ML (Xi and
  Pfenning) used them to remove array bounds checks from ML programs, and
  ATS builds on it. Rust's arithmetic on const generics has stayed
  unstable for years, which says something about the cost.
- **Refinement types** attach a predicate, `{r : Nat | r < b}`, and hand
  the obligation to an SMT solver: Liquid Haskell, F\*, and contracts like
  SPARK's or Evergreen's `where` and `ensures`. They reach further, and
  their failures come from a solver whose time and verdicts are hard to
  predict.

## What they could buy Faun

- **Lookups that cannot miss.** A `get` whose index is shown to be below
  the length could answer the element rather than a `Result`, with no check
  when the program runs.
- **Lengths that must agree.** `zip` of two lists of one length, or the
  dimensions of matrices multiplied, refused where they are built rather
  than quietly cut short: today `[1, 2, 3].zip([4])` is `[(1, 4)]`.
- **Fixed-size data held flat.** n-body steps a list of exactly five bodies.
  The compiler already finds that length by shape and keeps it through
  `map` and `put`, so a step builds no list; an index would make the five
  part of the type, and a program could rely on it rather than hope the
  analysis found it.
- **Nothing at run time.** An index is erased: a `Vec(n, a)` would be a
  `List(a)` in memory.

Much of Ori's case was termination: a length index would let mergesort's
halving be seen to descend. Faun does not check termination, so that part
of the case is gone ([totality](totality.md)).

## What they would cost

- **Signatures.** Indices must be written somewhere. Dependent ML asked for
  them on every function whose indices it should check; inferring them in
  general is not decidable, and Hindley–Milner's guarantee of one most
  general type does not survive arithmetic. Faun's signatures are optional
  today, and that is the first thing at risk.
- **A solver in the checker.** Linear arithmetic is decidable but not cheap
  in the worst case, and its failures read as "could not show
  `m + n = k`" about a program that may be right. Haskell's type-level
  naturals show the experience: the base solver cannot see `n + 1 = 1 + n`,
  and real code leans on solver plugins.
- **A second language.** Index variables, their arithmetic and their rules
  are a sublanguage a reader must know to read a library, even if most
  programs never write one.
- **Interaction with the rest.** Rows, `where` bounds and monomorphization
  were designed without indices. Indices erase, so specialization would not
  multiply, but every rule that unifies types would have to know about
  them.

## What a step would look like

The tiers suggest an order, each worth having on its own:

1. **Tag indices**, which Faun has: typestate with phantom parameters and
   private constructors.
2. **Size indices with equality only.** A size variable unified like a
   type, inferred like one, and erased. It needs no solver, so checking
   time and error messages stay what they are. It covers `zip`, matrix
   dimensions and fixed-size data, but not `append`, whose size is a sum.
3. **Linear arithmetic on sizes,** only if step 2 leaves real programs
   wanting it.

Step 2 is the one worth an experiment: it may give most of the practical
benefit at little of the cost.

## What would have to hold

- Indices are inferred in ordinary code: a program that never writes one
  reads and checks as it does today, and signatures stay optional.
- Checking stays within its time goal on the example programs.
- Indices erase, so no program gets slower or larger.
- An error names the fact that failed in the program's own terms, never a
  solver's.
- Real programs get shorter or faster: fewer `Result`s from lookups, fewer
  checks when they run, or data held flat that is boxed today.

## Rationale

### Why not refinement types instead?

They are strictly more expressive, and they are the route systems
languages take toward proof: a contract such as `where n < usize::MAX`
beside a function, discharged by a solver, with an escape hatch for what
the host promises. That route earns its cost where the language would
otherwise allow a memory error, so every proof buys safety. Faun removes
those hazards by design instead: no pointers, no partial operations, a
lookup that can miss answers a `Result`. What is left for a predicate to
protect is ordinary correctness, which is where [dependent types](dependent-types.md) argues proofs cost more than they give.

### Isn't checked structure exactly what an LLM writing code wants?

It is the strongest argument for them: a tool that refuses a wrong program
tells an agent what to fix. Faun already gives that feedback cheaply and
with nothing written: exhaustive matching, closed tag rows, linear
resources and types inferred everywhere. An index earns a place only if it
catches mistakes these do not, in programs people would otherwise write.

### Why keep them open at all?

Because unlike full dependent types they need not run the program, need
not touch termination, and at the size-equality tier need no solver. The
cost could be small, and the benefit is concrete: lookups without a
`Result`, and lengths checked where data is built.

## Related

- [Dependent types](dependent-types.md): why full dependent types are out
- [Types](types.md): inference, rows and `where` bounds, which indices
  would have to fit
- [Totality](totality.md): termination, which no longer argues for them
- [Collections](values/collections.md): `get`, `zip` and the lists
  indices would describe
- [N-body](nbody-performance.md): a fixed-length list found by analysis
