# barb

A simple compiler backend language with value semantics and automatic representation selection.

The idea is that, by encoding very little information in the program, there are fewer concepts to learn, and the compiler can derive the facts easily and optimize them.

## Goals

- Competitive with LLVM with a fraction of the code
- Better code gen on tricky targets, e.g. 6502
- Easy to add new backends

## Input program requirements

value semantics. a bodyless call is a value the target computes

- functions with bodies must be total - able to be proven to terminate by totality checker
- bodyless functions
  - can be used for representing effects
  - must be bodyless, implemented by the target
  - modeled by threading world state through calls
- must not have
  - pointer equality, reference identity, identity hashing. since representation is selected for you.
  - sizeof, alignment, layout dependent serialization, casts between representations
  - weak refs, finalizers
- whole source available. ish. backend will be able to dynamically link libs eventually
- must be fully defunctionalized and monomorphized

## The IR

```
body ::= (x = expr)* expr         bindings, then the term that answers

expr ::= x                        a local, read back
       | Ctor(x*)                 a saturated construction
       | value                    known outright, held encoded
       | name(x*)                 a saturated call to a top-level name
       | match x { arm* }         an arm per constructor, in tag order

arm  ::= Ctor(x*) -> body         fields bound as the next locals

x    ::= a parameter, a binding, or a field an arm bound
```

## Code map

- `model.rs`: terms, declarations, IDs and their small intrinsic methods.
- `program.rs`: `Program`, pool ownership, queries, declarations and interning.
  Its body-construction entry point delegates to `builder.rs`.
- `builder.rs`: `Builder` and temporary state for scoped body construction.
  The machine IR uses the same model/program/builder split. Keep each type's
  core API with its definition; separate substantial named algorithms, not
  reads from writes. Keep fields and construction machinery private or narrowly
  visible within the tier, and re-export the public API from `mod.rs`.
- `validate.rs`, `stops.rs`: structural checks and termination. Frontend typing
  and well-formed arena references remain preconditions, not proofs supplied here.
- `arithmetic.rs`: recognize induction equations, without range analysis.
- `bounds.rs`: interval arithmetic and interprocedural range propagation.
  `Propagation` is the evolving state; `Ranges` is the conservative final result.
- `facts.rs`: `analyze` combines recognition and ranges for the final program.
  Run it after optimization; facts must be recomputed after rewriting.
- `normalize.rs`: capture-free structural rebuilding; `inline.rs`: expansion
  eligibility, copy costs and budgets. Structural-only normalization does not
  construct an inlining plan or compute its recursion/copy-cost tables.
- `constant.rs`, `evaluate.rs`: compact values and bounded evaluation.
- `laws.rs`, `fold.rs`, `cleanup.rs`: separate optimizing rewrites.
- `optimize.rs`: the fixed schedule below; `pretty.rs`: rendering.

## Optimization passes

`optimize(program, &OptimizeOptions)` runs a small fixed schedule after validation:

1. Structural normalization: substitute local aliases, without expanding calls.
2. Optional helper inlining: nonrecursive, non-arithmetic helpers only.
3. Arithmetic identities justified by structurally recognized `Operation` facts.
4. Constant folding with one shared evaluation budget for the entire pass.
5. Effect-safe cleanup: remove aliases and unused atoms, constants and constructors.

Each stage runs once and can be disabled programmatically. `read_with_options` exposes
these controls without bypassing validation or totality checking. Disabling helper
inlining may reduce range analysis precision and backend representability, not alter
Barb semantics. The compatibility `normalize` entry point still includes inlining.
`normalize_with_limits` does structural-only rebuilding when any inline limit is
zero, without planning expansions. Recognition still runs to protect arithmetic
definitions; this is not a claim that structural normalization performs no analysis.

`InlineLimits` bounds copied arena entries per callee, per caller and across the whole
program, plus expansion depth. Large callees are refused before copying; exhausted
budgets leave ordinary calls. Structural copying of the input itself is not charged
as expansion. Normalization reads existing slots and appends new ones without
cloning the program. Function roots change only after all bodies have been rebuilt,
so inlining always reads original callees and respects their original cost/depth
limits. Superseded slots remain until cleanup.

`FoldLimits` bounds aggregate work, encoded value size and evaluation depth. Work
includes expression visits, copied bytes and conservative bigint word-operation
estimates. Result-size and work checks precede native arithmetic and constructor
concatenation. Limits are optimization policy, never language integer limits; a
refused fold retains the original expression. Traversing/recognizing the input is
not covered by evaluator fuel.

Cleanup walks bindings backward, accounting for captures in nested match arms, then
renames retained locals. Dead constructor chains disappear in this single traversal;
there is no fixed-point loop. Every call and match is conservatively retained, even
when its result is unused. In particular, dropping a constructor does not drop the
eager calls that computed its fields. Folded, now-unused product constants no longer
demand runtime representations; live products still require backend support.

Cleanup is also the term-arena compaction point. It borrows the original program,
builds fresh expression/argument/binding/arm pools, then installs those pools and
updated function roots. Every defined function is retained, not only entry-reachable
ones. Recognized arithmetic equations are copied without semantic rewriting, with
expression sharing preserved; liveness rewriting remains occurrence-specific.
Names, declarations, type lists and constant storage are neither cloned nor moved.
Constant-pool garbage collection is not part of this pass.

Read-only walks borrow pool slices; mutating laws and folding traverse stable ranges
one entry at a time instead of copying binding/arm lists. Range propagation borrows
the current result table for each function, then publishes its answer; it does not
snapshot the whole table per function or delay answers until the next round.
Bounded constant queries decode directly into a checked `u64`, without allocating a
bigint; arbitrary-precision queries retain their separate unbounded decoder.

Compaction invalidates old expression IDs and term ranges, including saved bodies
and expression-indexed facts. Function, type, constructor, symbol and constant IDs
stay stable. Recompute `analyze` after optimization. Disabling cleanup leaves the
append-only arena history in place; memory reclamation is not required for semantics.

Identities preserve monus and zero-divisor semantics. In particular, `x / x` is not
rewritten to one. Argument bindings remain eager even when a law makes their values
irrelevant. Bodyless calls may have effects or fail to return: passes preserve their
order, multiplicity and selected path. A whole call or match is folded only if every
selected eager binding evaluates successfully.

## Why this over LLVM

- llvm makes you choose a representation before a target.
- barb doesn't have to prove expensive things like pointer aliasing, purity
- barb has no undefined behavior
