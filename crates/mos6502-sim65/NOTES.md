# MOS 6502 backend notes

## Potential optimizations

### Register-aware constant materialization

A dead register holding a known constant could materialize an adjacent constant with
`INX` or `DEX` instead of another immediate load. On the 6502, one step saves a byte
without adding cycles: `DEX` is one byte and two cycles, while `LDX #imm` is two bytes
and two cycles.

The startup sequence reading `argc` has one such opportunity. After setting the hardware
stack pointer, `X` holds `$FF`; two `DEX`/`STX` pairs could write `$FE` and `$FD` into
the sim65 argument-stack pointer. This would reduce each affected image by three
bytes.

Keep this as an instruction-selection rule rather than a startup special case. It
requires a dead source value, tracked N/Z flags, and a size/cycle comparison. Limit
the initial rule to a delta of one; longer increment or decrement sequences trade
cycles for size.
