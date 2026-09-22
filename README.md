# Faun

A work-in-progress compiled, statically typed, functional programming language,
targeting x86-64 Linux, wasm32 WASI, and MOS 6502 sim65.

The primary frontend is being replaced with an Ori-compatible language. The
`faun` command currently lexes and parses a strict subset:

```sh
cargo run -- check notes/examples/frontend.ori
cargo bench -p faun --bench frontend
```

The parser supports nominal constructor types, first-order signatures, clauses,
bindings, calls, methods, and operators. It does not lower programs yet. See the
[frontend status and benchmark contract](notes/frontend.md) for the exact
boundary.

The archived `faun-simple` command keeps the original `.fn` frontend and complete
compiler pipeline. It validates definitions, runs a bounded optimization
schedule, recognizes arithmetic structurally, derives ranges, and lowers to
validated machine IR. Targets then prepare representations, check their limits,
and emit. A reference machine-IR interpreter supports 16-, 32-, and 64-bit
configurations.

See [arithmetic and simple-frontend libraries](standard/README.md) for unbounded `Nat`,
monus and zero-divisor semantics, native arithmetic, and ordinary `U8`/`Int`
definitions. There is no automatic prelude or import syntax: prepend the needed
library files explicitly.

[Runtime naturals](notes/runtime-naturals.md) work on x86-64 and wasm32 using a
reusable private heap, 64 KiB by default; exhaustion exits with status 2 rather
than wrapping. Native 6502 runtime naturals remain disabled pending image/stack
capacity checks. Fixed-width values wider than a target word are still rejected.

`U8` and `Int` enforce their invariants structurally and support pure compile-time
uses after folding and dead-binding cleanup. Runtime product/sum packing and
signed lowering are not implemented.

Compiler clients should use `Target::compile`, or `Target::prepare` to inspect
the prepared IR; raw `emit` does not legalize naturals or establish its validation
and target-acceptance preconditions. See [machine IR contracts](notes/machine-ir.md)
for external declarations, function construction, and representation rebuilding.

## Inspecting a runtime expression

[`examples/expressions.fn`](examples/expressions.fn) computes `(argc + 2) + argc`
with a guard requiring `argc < 32`. Counts include the program name: no extra
arguments gives exit status 4, two gives 8, and rejected counts give 0. Constant
arithmetic folds normally; the argument-dependent additions remain.

Enter the development shell, then inspect optimized Barb and lowered machine IR:

```sh
nix develop
cargo run --bin faun-simple -- inspect --target mos6502-sim65 --emit barb examples/expressions.fn
cargo run --bin faun-simple -- inspect --target mos6502-sim65 --emit ir examples/expressions.fn
```

Dumps go to stdout, so they can be redirected to files. `barb` stops after the
normal optimization schedule; look at `main!` for the folded constants 2 and 32.
It preserves source names such as `exit!` -- which is also the name every tier
below reads -- uses indentation for matches, and prints bodyless declarations
inline as `= <elsewhere>`.
`ir` is structurally validated machine IR, after its own optimization schedule
and before target preparation, useful even when a target cannot represent it. Use `--emit prepared-ir` for the legalized,
target-accepted IR that emission consumes. All stages honor the selected target's
host contracts and retain source validation and totality checks.

Build and run the 6502 image, then disassemble its actual emitted bytes:

```sh
cargo run --bin faun-simple -- build --target mos6502-sim65 -o /tmp/faun-expressions examples/expressions.fn
sim65 /tmp/faun-expressions.bin a b
echo $? # 8 (the result is an exit status, not printed output)

# Remove the 12-byte sim65 header; the payload loads at $0200.
dd if=/tmp/faun-expressions.bin of=/tmp/faun-expressions.raw bs=1 skip=12 status=none
da65 --cpu 6502 --start-addr 0x0200 /tmp/faun-expressions.raw
```

`sim65` and `da65` come with the development shell. Assembly is currently obtained
by disassembly, not a compiler `--emit asm` mode. This example has no embedded
data; programs with data or literal pools need a da65 info file to distinguish
those bytes from instructions.
