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
- an entry is optional. Every defined function is validated and must be total
  whether or not the entry reaches it. Optimization then keeps only what the
  entry reaches, so what is checked is everything written and what is kept is
  what runs; a program with no entry is checked, keeps every definition, and
  lowers to nothing
- must be fully defunctionalized and monomorphized
- a function with a body may be claimed to compute an IEEE 754 operation
  (`Program::claim`), where the frontend knows what no equation says. Its
  body must then compute that operation on the patterns its wrapped naturals
  hold, up to which NaN pattern a NaN is; validation checks only the claim's
  shape. A target with float instructions answers it with one; everything
  else, the evaluator excepted, walks the body.

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
- `program.rs`: `Program`, queries, declarations and coordination of owned pools.
  Its body-construction entry point delegates to `builder.rs`.
- `types.rs`: a private, borrowed view of declaration metadata, independent of
  function bodies, names and constant storage.
- `terms.rs`: owns expressions, argument lists, binding runs and match arms.
  Its append operations return IDs, ranges and bodies; buffer fields stay private.
  `Program` coordinates arena replacement with remapped function roots.
- `builder.rs`: `Builder` and temporary state for scoped body construction.
  The machine IR uses the same model/program/builder split. Keep each type's
  core API with its definition; separate substantial named algorithms, not
  reads from writes. Keep fields and construction machinery private or narrowly
  visible within the tier, and re-export the public API from `mod.rs`.
- `validate.rs`, `stops.rs`: structural checks and size-change termination.
  A round nothing else shows stops is asked again with a measure besides each
  parameter, `a ∸ b` for each ordered pair of natural parameters: smaller
  where the new pair lies within the old, one side moved, and a guard keeps
  them apart. Where even that fails, what calls answer is read as well: each
  definition's answer against its parameters, a greatest fixpoint, taken
  apart by its shape, and each field of a parameter of a sum holding no
  more of itself is a size of its own, so a parser going round on the rest
  it answers, in an `Ok` or handed to a helper that takes it apart, is seen
  to stop.
- `relations.rs`: what a guard says of the sizes it compared, followed from
  the comparisons recognized by their equations through the definitions
  answering from them, as the facts each constructor of the answer carries.
  A `Refusal` names what it refuses by Barb's own ids -- the function, and for
  a definition that may not stop, the call beginning a way round with no
  descent -- never by source; a frontend maps them back through what
  `Builder::call_site` told it, before anything rewrites the program.
  The termination pass keeps signed constructor-depth bounds for locals, so taking
  two fields and rebuilding one constructor still records a decrease. Structurally
  recognized natural arithmetic contributes its semantic result bounds: monus and
  division do not exceed the dividend, monus of a positive by a positive and
  division by at least two strictly reduce a positive dividend, and a remainder
  is below a positive divisor. This proves such definitions as factorial,
  Fibonacci, GCD, and popcount without trusting their source names.
  The pass then closes call matrices within each recursive component and requires
  every idempotent self-path to have a strict diagonal. Matrices are flat and
  endpoint-indexed, so closure considers only composable paths and stops at the
  first counterexample. Frontend typing and well-formed arena references remain
  preconditions, not proofs supplied here.
- `claim.rs`: what a claimed float is -- a natural in one-field wrappers,
  taken and answered at one type -- and answering a claimed call from its
  operands' patterns with the host's arithmetic (`crate::float`). A claimed
  definition is treated as a recognized one: kept, never inlined, and inert
  to cleanup. Range analysis gives its answer, and each wrapper it is built
  into, the whole format: a machine's NaN need not be the body's.
- `arithmetic.rs`: recognize induction equations, without range analysis. The
  same equations recognize a count of a sequence -- nought when empty, one more
  than the rest's for a step, never reading the element -- as a
  `SequenceOperation::Length`, a separate table from the binary `Operation`s.
  A recognized definition of either kind keeps its body: passes neither rewrite
  nor inline it, and cleanup treats its calls as inert.
  Bitwise `And`, `Or` and `Xor` and `Pow` are walks with more arguments than
  their operation: `f(a, b, place, built)` is `built + place * (a op b)`,
  halving both sides a step, and `f(base, e, built)` is `built * base ^ e`,
  squaring the base as the exponent halves. Halving is what makes each an
  induction, so the equations are checked symbolically, with a step's bit --
  which may read only `a % 2` and `b % 2`, or `e % 2` -- worked out for each
  way it can be. Only a two-argument definition calling a walk from its
  identity, a place of one and nothing built or one built, is the operation;
  the walk itself is not.
- `bounds.rs`: interval arithmetic and interprocedural range propagation.
  Each constructor field holds the join of every value built into it, by
  construction or in a constant; reading one back answers no more. Fields of
  values built out of sight -- entry parameters, bodyless results, spine
  constants -- hold anything but what an `Assumed` given to the analysis
  says of them. Barb itself assumes nothing: the tier lowering a program for a
  target supplies what it knows. A field of an enumeration type is also
  bounded by its tag count. A spine's rest is read as a step of its count and
  says nothing; a sequence's element holds what was built into it, a known
  byte string records the range of its bytes, and a known sequence of up to
  4096 other elements what each element's fields hold. A remainder by a
  natural known outright is below it even past what a `u64` bound says, so
  `n % 2^64` is a word. A recognized length
  answers what `Assumed` says a length can be; machine lowering says a word.
  Widening settles what recursion leaves growing; a few narrowing rounds then
  walk every definition afresh from the settled state, without widening, and
  take back what nothing reaches -- a remainder of a widened count is still
  below its divisor, and so is whatever it is handed to.
  A bitwise and is no more than either operand, an or or exclusive or is no
  wider than the wider, and a power is at most the greatest base to the
  greatest exponent where that fits a word.
  `Propagation` is the evolving state; `Ranges` is the conservative final result.
- `sequence.rs`: recognize a definition reversing one sequence onto
  another -- the other for the empty one, itself on the rest onto the element
  pushed for a step -- as `SequenceOperation::ReverseOnto`, and one that is a
  reversal onto nothing reversed again onto its second argument as
  `SequenceOperation::Prepend`. Both keep their bodies and are answered by
  machine lowering as one buffer operation: room made once, then a copy. A
  definition taking a count of elements off the front -- the sequence for
  nought, the empty one for an empty sequence, itself on the rest and the
  count less one otherwise, matching either first -- is
  `SequenceOperation::Drop`, answered as the same buffer holding fewer, and
  known bytes less some of their front as the same bytes further on. A
  definition rebuilding a sequence's front with the element a count reaches
  replaced by a value -- the empty sequence or itself for an empty one, the
  value pushed before the rest at nought, and the element pushed before
  itself on the rest and the count less one otherwise -- is
  `SequenceOperation::Replace`, answered as one element written over: where
  the buffer, and in place where nothing else holds it.
- `affine.rs`: derive small affine summaries from recognized natural addition and
  multiplication by constants, without adding an expression kind or expanding
  nonlinear products.
- `facts.rs`: the fact tables. `Program` owns them. Recognition is worked out
  the first time a pass asks and kept across rewrites, since rewriting a body
  keeps what it means; defining a body or a type forgets it. `Program::analyze`
  adds ranges and affine summaries, which any change to a body, declaration
  or the entry drops, so `Program::facts` answers only facts about the program
  as it stands. Lowering reads them there and refuses an unanalyzed program.
  Facts attach to functions, types and fields where possible, because those
  survive rewriting; expression-indexed facts do not.
- `normalize.rs`: capture-free structural rebuilding; `inline.rs`: expansion
  eligibility, copy costs and budgets. Structural-only normalization does not
  construct an inlining plan or compute its recursion/copy-cost tables. Every
  walk also takes the arm a match on a local written as a constructor or a
  known value selects, with its fields what built it, and replaces a match
  whose arms bind nothing and are term-for-term the same with that arm.
- `invariant.rs`: a parameter every call from outside hands the same known
  value, and every call from inside passes on as it came, is that value:
  the definition binds it first and reads it there, so what reads it inside
  a loop reads something known. The parameter stays, read by nothing.
- `specialize.rs`: where callers hand such a parameter different known
  values, a copy of the definition holding each, calling itself; kept, and
  given the calls handing its value, only where folding it decides a match
  between two or more arms.
- `descent.rs`: a definition taking two numbers of one natural type down
  together -- nought answers one base case, a step and nought another, two
  steps call it again on both predecessors with nothing else changed -- is
  those base cases applied to `a monus b` and `b monus a`, so it calls itself
  no more and may be inlined. The monus is the definition recognized as one
  over that type, or one declared in the shape recognition reads.
- `fuse.rs`: a producer walks a list, pushes one element onto an accumulator
  per step and answers it reversed; a consumer takes a list apart from the
  front, reading its rest only as the argument of tail calls to itself. A
  producer's call onto an empty accumulator read once, by a consumer's call
  later in the same body, becomes a call of a new definition doing both steps
  in one walk. Where the consumer is itself a producer, so is the fused one,
  so a chain fuses a link at a time. Only definitions reaching no bodyless
  call take part: fusing interleaves their work and cuts the producer short
  where the consumer stops. Nothing is recognized by name. The same walk
  turns a list reversed onto nothing and read once, by a reversal of it onto
  another, into one prepend in order: the recognized definition for that
  type, or one declared in the shape recognition reads.
- `sweep.rs`: dropping the definitions an entry does not reach, once
  validation has checked them and inlining and fusion have copied what they
  needed out of them.
- `copy.rs`: copying terms into a body under construction through a map of
  locals, with an optional redirect of one function's calls; what fusion and
  descent build new bodies with.
- `constant.rs`, `constant/view.rs`, `constant/checked.rs`: compact encoding,
  validated semantic views, and checked construction.
  Views read magnitudes and constructors without materializing trees.
  Evaluator field scans walk an encoding's extent within a budget.
- `constant/pool.rs`: owns constant entries, encoded bytes and checked insertion.
  `Program` keeps this pool paired with its own declarations; callers cannot
  substitute a different catalogue. The codec and views borrow only type metadata.
- `evaluate.rs`, `budget.rs`: evaluation and its shared work/size/depth policy.
- `laws.rs`, `fold.rs`, `normalize.rs`, `cleanup.rs`: separate optimizing rewrites.
- `optimize.rs`: the fixed schedule below; `pretty.rs`: rendering.

## Diagnostic rendering

`Program::render` uses indentation to delimit match arms and nested bodies,
without braces. Bodyless declarations keep `= <elsewhere>` on the signature
line. Types reserved with `declare_inline_type` carry their complete structural
spelling at each use and omit a redundant top-level declaration. The text is a
diagnostic view, not surface syntax or a serialization.
Frontend-created declarations retain their source names, including `!` on
platform calls such as `exit!` and `stdout!`, and those are the names machine
lowering carries through for linkage. A declaration may still name a different
provider symbol -- `answered_by` is how two declarations reach one routine at
two types -- so nothing infers a provider or an effect from the display name.

## Optimization passes

`optimize(program)` runs a small fixed schedule after validation:

1. Structural normalization: substitute local aliases, without expanding calls.
2. Descent: rewrite definitions taking two numbers down together as their
   base cases on the two differences, so they no longer recurse.
3. Helper inlining: non-arithmetic helpers other than loop breakers. In each
   recursive component, a definition calling itself is a breaker, and so are
   enough of the rest that no cycle is left among the others; each other one may
   be copied into its caller, so definitions calling each other become one
   calling itself, which machine lowering makes a loop where the call is a tail.
4. Fusion: a list built by one walk and read once by another is never built.
5. Arithmetic identities justified by structurally recognized `Operation` facts.
6. Constant folding, each definition after what it calls, so that a caller
   meets its callees' answers as constants; each definition draws at most a
   per-definition allowance from the pass's budget, so a costly answer
   declined in one leaves the rest something to fold with.
7. Specialization: a parameter a definition passes on to itself as it came,
   which callers hand different known values, gets a copy of the definition
   for each value, at most four, folded with that value bound. A copy is kept,
   and takes the calls handing its value, only where that decides a match
   between two or more arms, so a loop is not copied for values it only
   carries. Refolding one copy skips call-graph construction and ordering;
   refolding several definitions retains callee-first order and the same budgets.
8. Invariant arguments: a parameter every caller the entry reaches hands one
   known value is bound to that value in its definition. After folding, so
   what they hand is known, and before algebraic normalization, which reads a
   known sequence's length as a number. Each definition given a value is then
   folded again, with a budget of its own, so what it asks of that value is
   answered too.
9. Bounded algebraic normalization: combine constants across recognized associative
   operations and directional monus/division chains, then push power-of-two moduli
   through sums and products.
10. Sweep: where there is an entry, drop every definition it does not reach,
    renumbering function IDs in order. Types, constructors and constants stay.
11. Effect-safe cleanup: remove aliases, unused inert terms, and calls proved to be
    pure arithmetic or lengths; retain calls of unknown meaning and matches.

Every normalizing stage (1, 3 and 9) also decides what is already decided: a
match on a known constructor is its arm, the length of a known sequence is a
number, and a match whose arms agree is that
arm. A match that is the last binding of a body answering a match on it, and
read nothing else there, becomes one match: where each of its arms ends by
building a constructor, that arm goes on into the second's arm for it. Only
where no arm of the second is taken by two of the first, so nothing is copied
twice. Fusion, descent and specialization add definitions; a copy's name is its
original's and a number after a dot; a fused walk's name joins its two
halves' with `+`, and what they replace stays until nothing calls it.

Each stage runs once, always; there are no switches. Tests isolating one stage
call it directly within the crate. Inlining is also what gives range analysis
most of its precision, so lowering an uninlined program can need wider values.
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

`FoldLimits` bounds aggregate work, work per definition, encoded value size and
evaluation depth. Work
includes expression visits, copied bytes and conservative bigint word-operation
estimates. Result-size and work checks precede native arithmetic and constructor
concatenation. Limits are optimization policy, never language integer limits; a
refused fold retains the original expression. Algebraic normalization starts a
separate budget with the same limits; a refused constant combination is left
uncombined. Traversing/recognizing the input is not covered by evaluator
fuel.

Final-program analysis also records bounded affine forms of recognized natural
arithmetic. A form holds a `u64` constant and at most eight local terms with `u64`
coefficients. Addition combines forms; multiplication scales one only when the
other is constant. Overflow, a ninth term, a nonlinear product, monus, division,
modulus, comparison or control flow ends the summary. This is deliberately not a
polynomial normalizer: it scales affine forms by constants but never multiplies two
nonconstant forms or changes Barb's five expression kinds. Machine lowering
materializes summaries as arithmetic on their original leaf locals; dead source
operations then leave during machine-IR pruning. Source functions named like arithmetic remain ordinary calls unless their
equations are structurally recognized.

Cleanup walks bindings backward, accounting for captures in nested match arms, then
renames retained locals. Dead constructor chains disappear in this single traversal;
there is no fixed-point loop. Matches and calls of unknown meaning are conservatively
retained even when their results are unused. Calls structurally recognized as pure,
total arithmetic or lengths are inert and may go. In particular, dropping a constructor does
not drop opaque eager calls that computed its fields. Folded, now-unused product
constants no longer demand runtime representations; live products lower to
their fields' machine values and payload-carrying sums to machine cells.

Cleanup is also the term-arena compaction point. It borrows the original program,
builds a fresh `TermArena`, then hands it and all remapped function roots to
`Program::replace_terms`. Every definition the sweep kept is retained. Recognized arithmetic equations are copied without semantic rewriting, with
expression sharing preserved; liveness rewriting remains occurrence-specific.
Names, declarations, type lists and constant storage are neither cloned nor moved.
Constant-pool garbage collection is not part of this pass.

`TermArena` groups the same four contiguous buffers, without another heap layer.
Normalization appends to the existing arena and publishes roots after rebuilding;
cleanup moves replacement buffers into place without cloning them. The two passes
share storage operations, not traversal, liveness or inlining policy. Storage
construction still assumes valid references and lexical scopes; it neither brands
IDs nor makes panicking builders or iterators transactional.

Read-only walks borrow pool slices; mutating laws and folding traverse stable ranges
one entry at a time instead of copying binding/arm lists. Range propagation borrows
the current result table for each function, then publishes its answer; it does not
snapshot the whole table per function or delay answers until the next round.
Constants carry their types in the pool: `Expr::Static(ConstId)` and
`Builder::known(ConstId)` cannot independently attach a different type. Type
constructors are assigned once; a pending declaration is distinct from a defined
empty type. Recursive and mutually recursive declarations remain possible.

`type_shape(program, id)` classifies declarations structurally as uninhabited,
unit, wrapper, product, natural, sequence, wider spine, enumeration, or general
sum. A sequence is exactly an empty constructor plus a step with one payload and
one recursive field; its element may be any type. Names and constructor order do
not participate. Machine representation selection uses this exhaustive view
instead of rediscovering products, naturals, and byte spines independently.
Units are erased, wrappers remain transparent, naturals and enumerations are
scalar, products of at most eight leaves are held flat as their fields'
values, sequences are a buffer and a length, and everything else carrying
fields -- wider products and general sums -- becomes a managed cell. `Shape` is the constant codec's own
view of an encoding and answers a different question; representation selection
does not read it.

`Program::constant(id).view()` classifies a validated value as `Natural`, `Spine`,
or `Constructor`, with private, shape-specific handles. A natural is a zero-payload
spine; the `Spine` case has element payloads. Constant encoding is structural,
never based on source names. `NaturalView::try_u64()` can fail only with `TooWide`;
`to_biguint()` reads the magnitude without expanding the spine. `SpineView` supplies
its length and an explicit `ByteView` capability. Every constant has a total
`constructor()` query that inspects the header without allocating a bigint or
computing a predecessor. Tail decomposition does that work only when requested.
Ordinary constructor fields can be borrowed with a budget.

`Program::intern` checks constructor trees; `intern_number`, `intern_natural`, `intern_byte_spine`, and their builder entry
points return `Result`. Number insertion rejects undefined and non-natural shapes;
byte-spine insertion requires one recursive field and one element field that is
a natural or wraps one, since a wrapper encodes as what it wraps.
All checks run before bytes are written. Failed construction never changes the
pools. There is no way in from raw bytes, so every constant is canonically
encoded; the folder builds compound constants from fields it has checked. The byte format and
`known_bytes` remain unchanged; a tree decoder remains only as an independent test
oracle. IDs are still unbranded and must be used with their owning program; this
is not a full type checker for dynamic Barb expressions.

`ConstructionError` describes invalid input. `LimitExceeded`
distinguishes work, depth and value-size refusal. Evaluation separately reports
dynamic inputs, opaque calls and limits; only the folding driver decides to keep
an expression. Invalid construction in otherwise well-typed Barb is an invariant
violation, not a routine reason to decline folding. Field scans share evaluation's
depth and work budget, and construction still reserves encoded size before copying.
Pool construction checks fields once and assembles from borrowed inputs. Compound results
still use an owned staging buffer so pool reallocation cannot invalidate input
slices and resource refusal leaves storage unchanged. Former field-copy charges
remain conservative reservations: removing those temporary buffers does not alter
folding thresholds. Entries and bytes remain compact, contiguous and append-only,
without deduplication or per-value heap objects in the pool.
Leaf bigint conversions are total; evaluation size-checks arguments before using
them. Evaluation results remain owned byte buffers. Buffer sharing and arena
branding are separate decisions.

Compaction invalidates old expression IDs and term ranges, including saved bodies
and expression-indexed facts. Function, type, constructor, symbol and constant IDs
stay stable; expression-indexed facts are dropped with the old arena, so
analyze after optimizing. Until cleanup runs, the append-only arena history
stays in place; memory reclamation is not required for semantics.

Identities preserve monus and zero-divisor semantics. In particular, `x / x` is not
rewritten to one. Argument bindings remain eager even when a law makes their values
irrelevant. Bodyless calls may have effects or fail to return: passes preserve their
order, multiplicity and selected path. A whole call or match is folded only if every
selected eager binding evaluates successfully.

## Why this over LLVM

- llvm makes you choose a representation before a target.
- barb doesn't have to prove expensive things like pointer aliasing, purity
- barb has no undefined behavior
