# Machine IR contracts

`ir::Program::new` creates an entry, not an environment. It neither installs
builtins nor detects a host. The program has one function table and one `Call`
operation. A function's `Definition` is `Declared(RegionId)` while awaiting a
body, `Body(RegionId)` after construction, or `External`.
For an external function, `Function.name` is the provider symbol. Source aliases
are resolved by frontend lowering to function IDs; the machine declaration does
not store a second source name. A function with a body has a descriptive name,
which does not select a host operation.

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
let stop = program.external("exit", &[Class::Word], Returns::Never);
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
`Target::routines`. `Routine::declare` copies the provider name and contract into a program;
`Routines::declare` also performs the named lookup. The program retains no
catalog. Source lowering only declares demanded functions. Targets own external
call emission and internal function numbering; source IDs need not be dense
emitted-body indices.

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
