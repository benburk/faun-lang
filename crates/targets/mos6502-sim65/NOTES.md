# MOS 6502 backend notes

## Potential optimizations

### Sharing a tail through a skipped load

Two paths that load different constants into `A` and then jump to the same place
can share one jump: the first load is followed by `$2C`, the opcode of `bit abs`,
which reads the second load's two bytes as an address and so skips it. That saves
a byte per shared tail, but the skipping path pays four cycles for the `bit`. It
also needs the skipped instruction to be exactly two bytes and `bit`'s flag changes
to be dead. Not worth it unless size is to be traded for cycles.
