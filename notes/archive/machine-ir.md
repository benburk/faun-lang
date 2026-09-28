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

The primary frontend's `faun build --emit machine` prints validated, optimized
machine IR before target preparation; `--emit barb` stops after the Barb
optimization schedule. Both write to stdout and use the selected target's host
contract. Ordinary `faun build` continues through `Target::prepare` and artifact
emission.

The archived simple frontend's `faun-simple inspect --emit ir` validates lowered
IR without requiring target acceptance; `--emit prepared-ir` prints the result
of `Target::prepare` instead. `--emit barb` uses
`faun_simple::read_barb`, sharing that frontend's pipeline with ordinary
compilation. See the
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
be the logical entry: validation rejects a missing entry, one without a body,
or one without exactly one Word result. The entry may have named parameters;
targets bind those from their process startup convention and reject names they
cannot supply. Ordinary calls cannot name the logical entry: only the target's
physical startup adapter enters it. `Program::new(name)` declares a parameterless entry, while
`Program::new_with_params` declares that logical startup signature. Both return
the program and entry ID together.

Parameter classes and returning result classes occupy the signature pool;
parameter names occupy parallel declaration metadata and survive rewriting and
legalization. A body's parameter values belong to its root region. External declarations
allocate neither parameter values nor dummy regions. `Returns::Never` is
distinct from `Returns::Values` with an empty class list: the latter returns
normally, while the former has no continuation. `declare_never` declares an
internal function with that same nonreturning contract.

```rust
use faun_core::ir::{Class, Program, Returns};

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

A routine's contract says what each argument it is handed becomes, not just
what class it is. `platform::Takes::StaticBytes` is one argument a program
writes and two machine values a routine reads: the address the bytes start at
and how many there are. Lowering places those bytes in machine data and hands
over both. Nothing about this names a routine, so a second routine taking a
byte string needs nothing added here; `write!(bytes)` is the one that does
today. A byte string worked out while the program runs is refused rather than
copied -- marshalling a managed sequence into a contiguous buffer belongs to
`legalize`, which owns layout, and does not exist yet.

`read_byte!` is an ordinary returning external with no machine operands: source
`Host` authority carries nothing and is erased before this tier. Its nine-bit
scalar answer is zero at EOF or one plus the byte read. The native targets map
read errors to EOF; there is no error channel or aggregate buffer in this
contract.

## Flat products

A source product -- one constructor, several fields -- has no machine value of
its own. Lowering holds it as its fields' values end to end: a nested product
contributes its own leaves, a unit contributes none, and a wrapper around a
product is that product. Construction and matching emit no instruction, so a
product costs no allocation, reference count or release walk. A parameter,
result, `if` join or cell field of product type is one machine value per leaf;
a flat entry parameter's leaves are named `name.0`, `name.1`, and so on.

Whether a product is flat is read off the type alone. A leaf is held at the
class Barb's range analysis gives that field of that constructor: every value
built into it anywhere in the program, so a number only ever built small is a
small fixed width, and one grown round a recursion is a `Natural`. A tag with
no better bound is a `Word`, and a sum or sequence is a `Cell`. Cell fields
take their classes the same way. Two kinds of product
remain cells: one with more than eight leaves, which is cheaper shared than
copied, and one reaching itself through products alone, which has no values.
Host routines read scalars and byte strings, so a product handed to one is
refused.

## Fitting boundaries

The IR lets a function take and answer any number of values and a region carry
any number across an edge; flat products rely on that. A target declares what
its convention carries with `Target::budget` -- the 6502 passes four parameters,
answers one result and carries two values across a region edge, and x86-64
passes six and answers one. `Target::prepare` runs `ir::fit` before
legalization: where more values cross a boundary than the budget allows, the
last place holds one cell carrying the rest, tag zero, and the other side reads
them back with `CellField`. The logical entry and external declarations keep
their signatures. Values that fit stay where they are, so `fit` changes nothing
on a program within its budget, and wasm, which carries multiple values
natively, declares no limit.

A pack is an ordinary cell, so ownership placement and release treat it like
any other: a packed natural or cell is retained when packed and released with
the pack. `Target::limits` still checks the prepared program against the same
numbers; raw emission of an unfitted program is refused as before.

## Managed cells

`Class::Cell` is the abstract one-word representation for payload-carrying
sums, products too wide to hold flat, and the packs `fit` introduces.
`Cell { tag, fields }` constructs a value, `CellTag` reads
its constructor tag, and `CellField` projects a zero-based represented field.
These operations expose neither pointers nor target layout. Unit fields are
omitted, wrappers are transparent, a flat product field is laid inline as its
leaves, and each projection has the class selected for that field. Cells may
cross internal calls, structured branches, loops, and returns. Host signatures
cannot contain cells.

The reference interpreter keeps abstract cell values in a private handle table.
Target preparation instead lowers every cell to an address in the same private
heap used by runtime naturals. A mortal object has a block size and reference
count followed by its tag, represented-field count, and pairs of field kind and
word value. Field kinds distinguish unmanaged scalars, naturals, and cells so
recursive release can release managed children before freeing the block.
Projection retains a managed field. Construction takes its fields' claims,
moving a field's own claim where the cell is that value's last use. Ownership
placement releases each claim right after its value's last use and transfers
returned, yielded, broken, and continued values; see
[runtime naturals](runtime-naturals.md) for the schedule. Heap exhaustion follows the natural runtime contract and exits
with status 2.

Cell payload sizes and offsets are checked before rebuilding. After preparation,
`Class::Cell` and all three abstract operations are gone; targets receive ordinary
word-sized addresses, loads, stores, and calls to generated allocation and
ownership helpers.

## Sequence buffers

A sequence -- a two-constructor sum whose step holds one element and the rest
of itself, such as `List(a)` and `Str` -- is not a chain of cells. Lowering
holds it flat as two values: a `Class::Buffer` and a `Word` length. The
sequence is the buffer's last `len` elements, so every sequence sharing a
buffer is a suffix of it. Taking one apart tests the length against nought,
reads the first element's leaves with `BufferField`, and binds the rest as the
same buffer with the length one less: no allocation and no retain. An element
is its leaves, one slot each, so a flat product is laid inline.

`BufferEmpty` makes a buffer holding nothing, and `BufferPush` answers the
buffer holding one more element in front of the last `len`. It takes claims to
the buffer and to each leaf, so ownership placement moves the buffer's own
claim where the push is its last use. Legalization lowers a push to a
per-layout `seq.reserve` routine and stores the leaves where it made room:

- a buffer whose count is one and which has room in front of the sequence is
  written in place, releasing whatever a longer sequence left in that slot;
- otherwise the sequence is copied to the end of a new buffer with as much
  room again in front, each copied managed leaf retained, and the old buffer
  released.

So pushes onto a buffer nothing else holds are amortized constant, including
building on the way out as `map` does, since each step pushes onto the buffer
the rest of the walk just answered. A buffer records its capacity, the lowest
element it holds claims for, its stride and one kind per leaf; `seq.release`
releases every held element when the last claim goes. A known sequence whose
elements are all numbers -- a string, or a table of words and small counts --
is `BufferKnown`: its leaves in the data, legalized into a static buffer in
the image that nothing writes or frees, and width splitting lays a wide leaf
out as its words. A natural leaf is laid out only below `2^15`, where it is
held in place on every target and holds no claim. Any other known sequence is
built by pushing its elements from the end. The reference interpreter keeps
each buffer as a list of elements and gives a push a fresh one, so its answers
do not depend on writing in place.

## Saturating subtraction

`Binary::Monus` answers `left - right`, or zero where `right` is the greater.
Barb's natural monus lowers to it directly rather than to a comparison guarding
`Sub`. Its operands follow the comparison rule -- numbers of one kind -- and its
result may be any numeric class, including one narrower than either operand,
since the answer never exceeds `left`. Only naturals' monus answers `Natural`,
and runtime-natural legalization maps it to the same helper as `Sub`. Targets
compute it at the operands' width, where the borrow is, and choose the answer
from that borrow: a conditional clear on x86-64, `select` on wasm32, and a carry
branch on the 6502. `Sub` keeps its fit requirement on fixed classes.

## Bitwise operations and powers

`Binary::And`, `Or` and `Xor` answer a bit wherever both, either or exactly
one operand has one. They follow `Add`'s rule for operands, except that an or
or exclusive or is worked out at a class with every bit below the wider
operand's top one, since it may set bits neither operand's greatest has. No
bit crosses between words, so width splitting answers each word from the same
words of its operands, and targets use their own instructions: `and`, `or`
and `xor` on x86-64 and wasm32, and `AND`, `ORA` and `EOR` a byte at a time on
the 6502. On `Natural` operands, runtime legalization calls `nat.and`,
`nat.or` or `nat.xor`, which answer two immediates from their numbers and
otherwise work a digit at a time.

Barb's `Pow` has no instruction of its own. Two to a power, at a class a
word holds, is `ShiftUp(1, k)`, and simplification makes a product or
quotient by one of those `ShiftUp` or `ShiftDown` by `k`: a shift by a
distance worked out while the program runs. x86-64 and wasm32 say they shift
by a register (`Target::shifts_by_register`); preparation writes every other
such shift as a loop of one-place shifts (`ir::expand_shifts`), as it does
one wider than the word, which splitting then carries across words, and one
down whose distance may reach the word, which an instruction would take
modulo the word. Acceptance refuses one a target cannot do. Any other power
is a loop squaring the base as the exponent halves, at the class range
analysis proved the answer fits.
Every intermediate fits there too: what has been multiplied in is the base to
the exponent's low bits, and the base is squared only while bits remain above.

## Passes

`ir::optimize(program)` runs a small fixed schedule after validation, in this
order, each stage once:

1. `simplify`: recognise what lowering had no way to avoid writing. A branch
   whose condition only asks which tag an earlier comparison answered becomes
   a branch on that comparison, with its arms in whichever order the tags say.
   A constant read at a `Fixed` width is written at that width instead of
   being converted to it. A run of additions of known numbers, all at one
   width, is one addition. Barb normalizes calls it recognizes as arithmetic;
   this lower-tier rule also covers constructor steps introduced by lowering
   and programs built directly in machine IR.
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
corpus in `faun_core::programs` is written directly in machine IR and does not.

`Program::operands(op)` iterates over immediate value operands without allocating,
in order and with repeated uses preserved. It does not descend into nested regions
or include their terminators. Pruning, ownership analysis, width splitting and the
6502 backend share this query; each owns its region traversal.

Source lowering may bypass a tree of recognized natural additions with Barb's
bounded affine summary. The summary remains a fact rather than a sixth Barb term:
lowering writes machine `Mul` and `Add` operations against the original leaf values,
and pruning removes bypassed intermediates. A coefficient of two remains an `Add`
so arbitrary-precision naturals do not acquire a multiplication helper merely for
doubling. Other constant products stay explicit for target selection; the 6502
currently strength-reduces a byte-sized product by three to one shift and one add.
An unrecognized source function named like multiplication is never involved.

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

Legalization maps signature classes in the new declaration pool, then uses
`ir::rewrite`'s shared skeleton construction to copy preserved metadata and mint
root parameters. Its ownership-aware body traversal remains separate. Declaration
and symbol IDs, signature ranges, data and globals are preserved; bodies receive
newly minted parameter values and rebuilt regions. Old value IDs are not retained.
See [runtime naturals](runtime-naturals.md) for the distinction between the global
SSA mapping and path-local ownership.
