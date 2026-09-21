# Machine IR contracts

## Inspection

`Program::render` prints diagnostic text with function signatures, SSA value
classes, data spans and explicit region edges. Function names are printed
without quotes, as in `fn f0 main!() -> (word) = r0`. Calls name the callee and
retain its declaration ID as an annotation, for example `call exit(v10)  # f1`.
Names need not be unique; the ID distinguishes declarations, including internal
functions named like external providers. It resolves operand/signature
runs rather than exposing pool offsets; regions appear once in storage order,
including retained detached regions. It neither validates nor mutates the
program and assumes well-formed references, like other queries. Pending
function definitions are distinct from externals, and `<no terminator>` records
absence rather than inventing an unreachable instruction. In validated IR that
absence means the region cannot fall through. The text is not a serialization
or a round-trippable source format.

Dumps with function declarations begin with a class legend: classes describe
individual values' representation requirements, not source types. `fixedN`
means `0 <= value < 2^N`, not wrapping arithmetic or an exact inferred interval.
A narrower sink requires a fit proof or an explicit conversion. The legend does
not add range analysis or change the classes printed on definitions and signatures.

The CLI's `inspect --emit ir` validates lowered IR without requiring target
acceptance; `--emit prepared-ir` prints the result of `Target::prepare` instead.
`--emit barb` uses `read_barb_with_options` with the default optimization options,
sharing the front-end pipeline with ordinary compilation. See the
[runnable inspection example](../README.md#inspecting-a-runtime-expression).

## Zero-width scalars

Bounds-based lowering selects `fixed0` for values proven to be zero: the range
`0 <= value < 2^0` has one inhabitant. Zero-valued parameters, results and joins
remain scalar values with their original arity; they are not erased like unit.
A known result does not permit dropping the effects or nonreturning calls that
compute it. Targets may still materialize zero in a register, slot or ABI word.
Constants already declared at wider classes remain valid, and the entry retains
its Word result contract.

Comparison lowering also gives each synthesized tag constant its own minimal
class: zero uses `fixed0`, one uses `fixed1`. Both emitted arms must fit their
shared join. If range analysis proves that only the zero tag can be returned,
that narrower result is established after the join; the other arm's tag is not
truncated merely because its branch is unreachable.

## Functions

`ir::Program::new` creates an entry, not an environment. It neither installs
builtins nor detects a host. The program has one function table and one `Call`
operation. A function's `Definition` is `Declared(RegionId)` while awaiting a
body, `Body(RegionId)` after construction, or `External`.
For an external function, `Function.name` is the provider symbol. A platform
routine has one name at every tier, `!` and all, so `exit!` is what the source
writes, what the declaration carries, and what a target is asked by. Where a
Barb declaration names a different provider -- two declarations reaching one
routine at two types -- lowering resolves that to the provider symbol; the
machine declaration stores no second source name. A function with a body has a
descriptive name, which does not select a host operation.

`Program::default()` is an empty construction state. Its first function must
be the entry: validation rejects a missing entry or one without a body, with
parameters, or without exactly one Word result. `Program::new(name)` uses that
empty state and declares the entry immediately; it still returns the program
and entry ID together.

Parameter classes and returning result classes occupy the signature pool.
A body's parameter values belong to its root region. External declarations
allocate neither parameter values nor dummy regions. `Returns::Never` is
distinct from `Returns::Values` with an empty class list: the latter returns
normally, while the former has no continuation. `declare_never` declares an
internal function with that same nonreturning contract.

```rust
use faun::ir::{Class, Program, Returns};

let (mut program, main) = Program::new("main");
let stop = program.external("exit!", &[Class::Word], Returns::Never);
program.define(main, |b, _| {
    let status = b.constant(Class::Word, 0);
    b.call(stop, &[status]);
});
```

An external function declaration describes its name and signature, not whether
a provider exists. Structural IR validation checks references and calls without
consulting a catalog. Target
acceptance checks called external declarations against the target's symbols,
parameter/result classes and returning behavior. Uncalled declarations do not
require a provider; all signatures still undergo structural and representation
checks.
A target-width `Fixed` class and `Word` describe the same scalar ABI; a narrower
result claim does not. The interpreter uses the declared contract and calls its
host by provider symbol, including when evaluating an external function directly.

Environment discovery still uses `platform::Routines` in frontend setup and
`Target::routines`. A `Routine` has one name, and `Routine::offered` says whether
a source program may write it. `Routine::declare` copies that name and contract into a program;
`Routines::declare` also performs the named lookup. The program retains no
catalog. Source lowering only declares demanded functions. Targets own external
call emission and internal function numbering; source IDs need not be dense
emitted-body indices.

## Passes

`ir::optimize(program, &OptimizeOptions)` runs a small fixed schedule after
validation, in this order, each stage at most once:

1. `simplify`: recognise what lowering had no way to avoid writing. A branch
   whose condition only asks which tag an earlier comparison answered becomes
   a branch on that comparison, with its arms in whichever order the tags say.
   A constant read at a `Fixed` width is written at that width instead of
   being converted to it.
2. `prune`: drop instructions nothing reads. A call may do something while
   answering and a store does nothing else, so neither is dropped, and an `if`
   holding either stays for what it holds rather than for what it answers.
   A loop stays either way: this does not decide whether one comes back.

Nothing here is a fixed point and nothing changes what a program means.
Validation must precede it: a pass reads a program as structurally sound.

A pass reads one program and writes another, because values, instructions and
regions live in arenas addressed by position: removing an instruction where it
stands would renumber every value after it. `ir::rewrite` owns the walk between
the two -- the descent past `If` and `Loop`, and the map from an old value to
whatever stands for it -- so a pass is only the decision it came to make. Data,
globals, names, function declarations and function IDs survive a pass; values,
instructions and regions do not, so nothing held across one names the same
thing afterwards.

`read` runs this schedule, so `--emit ir` shows the optimized program. The
corpus in `faun::programs` is written directly in machine IR and does not.

Source demand discovery, answer analysis, and emission share a lazy reachable-arm
walk. Tagged matches analyze each arm once when planning that match, then compute
suffix join widths backward; nested tests retain their narrower joins. Answer
analysis reuses a scoped local-presence stack, restoring it after each body and
arm, including nonreturning ones. These results belong to lexical occurrences,
not a global expression-ID cache. Demand discovery and emission remain separate.

## Typed entity storage

Functions, regions, values' classes, data spans and symbol entries live in
internal `Pool<Id, T>` collections. Insertion returns the inserted ID; indexing
and checked lookup take that ID type. ID conversion is checked before that
pool is extended, not after it. This does not make multi-pool builders transactional.
The same storage is used for Barb's individually addressed entities, including
its expression arena and the fresh arena built during cleanup.

Each pool is still one contiguous vector with compact IDs. Public slice views
remain available; byte, operand and signature runs still use ordinary vectors
and ranges. Instruction/result arrays still have coordinated construction.
Typed IDs distinguish entity kinds, not programs or generations: references
must still be remapped when a pool is rebuilt. There is no insertion in the
middle, removal, or mutable vector escape hatch on the pool itself.

`Program::function(FunctionId)` provides typed lookup outside the IR module;
`functions()` still exposes a slice for iteration. Like other indexing accessors,
`function` panics for an out-of-bounds ID. Validation and unchecked interpretation
keep checked lookups rather than assuming references are valid.

Ordinary slice appends use `append_range`, which checks the encoded start and
length before extending a vector and returns the appended run. Empty runs keep
their position. This preserves the existing two-field range contract: it does
not impose a new total-pool byte limit or promise rollback if element cloning
panics. Iterator-based construction and coordinated instruction/result writes
retain their own construction logic.

For a callee declared to return exactly one value, `Builder::call_one` returns
a `ValueId` directly, using the result class from the signature. It rejects
zero, multiple, and nonreturning result contracts before appending call operands
or values. General `call` remains available for all result contracts.
Both emit ordinary calls with the same ordering and effect semantics;
`call_one` avoids constructing a temporary result vector, not the operand or SSA
storage required by the call.

## Region completion

Builder callbacks record `ret`, `yield_`, `break_`, or `continue_` directly and
return `()`. A region stores an optional terminator: absence is valid only when
its instructions cannot fall through. There is no explicit IR `Unreachable`.

Validation derives continuation from call signatures and structured transfers:
a `Never` call cannot continue; an `If` continues only through a branch's yield;
a loop continues after itself only through a break from that loop. Nested loops
consume their own breaks. A break through an earlier branch still counts even
if the remaining path ends in a nonreturning call. Return and continue do not
create a local continuation. Both conditional branches are considered; this is
structural control-flow checking, not a proof about condition values or whether
a returning call actually terminates.

Validation rejects missing transfers on possible fallthrough paths, and rejects
instructions or terminators after terminal control flow. The builder also
rejects attempts to append after an explicit transfer. Unchecked interpretation
reports an invalid program if a missing terminator is reached. Wasm still uses
its native `unreachable` opcode where its stack typing needs a marker; that is
an encoding detail, not a second IR control-flow assertion.

## Fallible construction

`declare` reserves parameters and a root slot, allowing forward calls.
Validation rejects every unbuilt declaration, including unused ones.
`define` installs an infallibly built body;
`try_define` accepts a callback returning `Result<(), E>` and propagates
its error without a separate caller error slot or fabricated terminator.
Neither method may define an external declaration.

On an error, the existing root body is unchanged, or an unbuilt declaration
remains unbuilt. This is not transactional
rollback: appended values, data and nested regions remain in the arenas, while
the unfinished root's instructions are discarded. Retained entries still
undergo pool-wide validation and target checks. Retrying is supported, but
clients that need the prior pool state should discard the partial program
rather than assume rollback. Lowering does so by returning the error instead of exposing its partial
program.

## Representation rebuilding

Legalization copies preserved metadata and maps signature classes in place in
the new signature pool. Declaration and symbol IDs, signature ranges, data and
globals are preserved; bodies receive newly minted parameter values and rebuilt
regions. Old value IDs are not retained. See [runtime naturals](runtime-naturals.md)
for the distinction between the global SSA mapping and path-local ownership.
