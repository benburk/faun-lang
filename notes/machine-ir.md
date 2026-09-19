# Machine IR contracts

`ir::Program::new` creates an entry, not an environment. It neither installs
builtins nor detects a host. The program has one function table and one `Call`
operation. A function's `Definition` is either `Body(RegionId)` or
`External { symbol }`; its local name need not match the provider symbol.

Parameter classes and returning result classes occupy the signature pool.
A body's parameter values belong to its root region. External declarations
allocate neither parameter values nor dummy regions. `Returns::Never` is
distinct from `Returns::Values` with an empty class list: the latter returns
normally, while the former must end its calling region with `Unreachable`.

```rust
use faun::ir::{Class, Program, Returns, Terminator};

let (mut program, main) = Program::new("main");
let stop = program.external("stop", "exit", &[Class::Word], Returns::Never);
program.define(main, |b, _| {
    let status = b.constant(Class::Word, 0);
    b.call(stop, &[status]);
    Terminator::UNREACHABLE
});
```

Declarations express requirements, not availability. Structural IR validation
checks their references and calls without consulting a catalog. Target
acceptance checks called external declarations against the target's symbols,
parameter/result classes and returning behavior. Uncalled declarations do not
require a provider; all signatures still undergo structural and representation
checks.
A target-width `Fixed` class and `Word` describe the same scalar ABI; a narrower
result claim does not. The interpreter uses the declared contract and calls its
host by provider symbol, including when evaluating an external function directly.

Environment discovery still uses `platform::Routines` in frontend setup and
`Target::routines`. `Routine::declare` copies a chosen contract into a program;
`Routines::declare` also performs the named lookup. The program retains no
catalog. Source lowering only declares demanded functions. Targets own external
call emission and internal function numbering; source IDs need not be dense
emitted-body indices.

## Fallible construction

`declare` reserves a body's parameters and an initially unreachable root region,
allowing forward calls. `define` installs an infallibly built body;
`try_define` accepts a callback returning `Result<Terminator, E>` and propagates
its error without a separate caller error slot or fabricated terminator.
Neither method may define an external declaration.

On an error, the existing root body is unchanged. This is not transactional
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
