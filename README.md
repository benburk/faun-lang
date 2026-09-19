# Faun

A work-in-progress compiled, statically typed, functional programming language,
targeting x86-64 Linux, wasm32 WASI, and MOS 6502 sim65.

The compiler validates source definitions, runs a bounded optimization schedule,
recognizes arithmetic structurally, derives ranges, and lowers to validated
machine IR. Targets then prepare representations, check their limits, and emit.
A reference machine-IR interpreter supports 16-, 32-, and 64-bit configurations.

See [arithmetic and source libraries](standard/README.md) for unbounded `Nat`,
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
