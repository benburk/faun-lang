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
  whether or not the entry reaches it; machine lowering takes only what the
  entry reaches, so a program with no entry is checked and lowers to nothing
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
  A `Refusal` names what it refuses by Barb's own ids -- the function, and for
  a definition that may not stop, the call beginning a way round with no
  descent -- never by source; a frontend maps them back through what
  `Builder::call_site` told it, before anything rewrites the program.
  The termination pass keeps signed constructor-depth bounds for locals, so taking
  two fields and rebuilding one constructor still records a decrease. Structurally
  recognized natural arithmetic contributes its semantic result bounds: monus and
  division do not exceed the dividend, division by at least two strictly reduces a
  positive dividend, and a remainder is below a positive divisor. This proves such
  definitions as Fibonacci, GCD, and popcount without trusting their source names.
  The pass then closes call matrices within each recursive component and requires
  every idempotent self-path to have a strict diagonal. Matrices are flat and
  endpoint-indexed, so closure considers only composable paths and stops at the
  first counterexample. Frontend typing and well-formed arena references remain
  preconditions, not proofs supplied here.
- `arithmetic.rs`: recognize induction equations, without range analysis. The
  same equations recognize a count of a sequence -- nought when empty, one more
  than the rest's for a step, never reading the element -- as a
  `SequenceOperation::Length`, a separate table from the binary `Operation`s.
  A recognized definition of either kind keeps its body: passes neither rewrite
  nor inline it, and cleanup treats its calls as inert.
- `bounds.rs`: interval arithmetic and interprocedural range propagation.
  Each constructor field holds the join of every value built into it, by
  construction or in a constant; reading one back answers no more. Fields of
  values built out of sight -- entry parameters, bodyless results, spine
  constants -- hold anything but what an `Assumed` given to the analysis
  says of them. Barb itself assumes nothing: the tier lowering a program for a
  target supplies what it knows. A field of an enumeration type is also
  bounded by its tag count. A spine's rest is read as a step of its count and
  says nothing; a sequence's element holds what was built into it, and a
  known byte string records the range of its bytes. A recognized length
  answers what `Assumed` says a length can be; machine lowering says a word.
  Widening settles what recursion leaves growing; a few narrowing rounds then
  walk every definition afresh from the settled state, without widening, and
  take back what nothing reaches -- a remainder of a widened count is still
  below its divisor, and so is whatever it is handed to.
  `Propagation` is the evolving state; `Ranges` is the conservative final result.
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
  construct an inlining plan or compute its recursion/copy-cost tables.
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
2. Helper inlining: nonrecursive, non-arithmetic helpers only.
3. Arithmetic identities justified by structurally recognized `Operation` facts.
4. Constant folding with one shared evaluation budget for the entire pass.
5. Bounded algebraic normalization: combine constants across recognized associative
   operations and directional monus/division chains, then push power-of-two moduli
   through sums and products.
6. Effect-safe cleanup: remove aliases, unused inert terms, and calls proved to be
   pure arithmetic or lengths; retain calls of unknown meaning and matches.

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

`FoldLimits` bounds aggregate work, encoded value size and evaluation depth. Work
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
`Program::replace_terms`. Every defined function is retained, not only entry-reachable
ones. Recognized arithmetic equations are copied without semantic rewriting, with
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
byte-spine insertion requires one natural element field and one recursive field.
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
