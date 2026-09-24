# Runtime naturals

`Target::compile` prepares, validates, accepts and emits the same scalar machine
program. The CLI uses this interface. `Target::emit` is a raw backend interface:
its input must already be validated and accepted; it does not legalize naturals.
`Target::prepare` exposes the transformed program for inspection and evaluation.

`ir::legalize(&Program, ir::natural::Config)` rebuilds the arena-backed program,
keeping original function IDs (including externals) and existing data/globals
intact. Only
original Natural values become owned object addresses. Ordinary addresses are
not reference counted, and address/natural reinterpretation is rejected. Host
signatures containing Natural have no supported bigint ABI. Source host arguments
must have a fit proof; implicit effects are not requests for modulo conversion.

The shared runtime uses base-256 magnitudes and a reusable bounded private heap.
Its default budget is 64 KiB on x86-64 and wasm32. Allocation or reference-count
exhaustion exits with status 2; it never returns a wrapped integer or zero in
place of a failed allocation. Explicit `Convert` to scalar classes truncates.
Clients can select a different budget by legalizing explicitly before emission.
The serialized headers are **target sized**. Runtime generation records a
`Program::layout()` obligation containing `Config.word_bits`; every target is
little-endian. Legalization, target acceptance and interpretation reject a
mismatched word size before execution or emission. Cloning and
re-legalizing preserve this obligation; scalar-only legalization leaves portable
programs unbound.
This is a memory resource limit, not a numeric modulus.

Each local managed result owns one reference, and so do loop parameters and
owned function parameters. A parameter is owned when its function takes a
claim to it somewhere -- returns it, stores it in a cell, carries it into a
loop, converts it, or passes it to another owned parameter -- decided to a
fixed point across calls; every other parameter is borrowed. Function results,
branch results and loop state transfer owned references.

A claim is released right after its value's last use in the region holding
it. A use that takes a claim moves the value's own claim where that use is its
only and last reading, and retains a new one otherwise. A value whose last use
is an `if` hands its claim to both arms; each arm releases it at its own last
use, or on entry where it never reads it. A value read inside a loop body stays
with the enclosing region and is released after the loop. An exit moves out
claims the scopes it leaves hold, retains outgoing values it reads twice, and
releases everything else those scopes still hold; function returns unwind all
local scopes but not borrowed parameters. So a count of one means nothing else
can reach a value, which updating one in place relies on.

Validation establishes globally unique SSA definitions and lexical use. The
legalizer therefore keeps one monotonic old-to-new value map for the whole
program, shared by sequential branch builders; it does not snapshot that map
per function or branch. Ownership scopes remain path-local snapshots, so an
exit in one sibling cannot consume another sibling's claims. The runtime
itself declares the nonreturning external function `exit!(word)`; target
acceptance checks the provider contract, not a catalog retained in the IR.

## Deliberate limits

- `Fixed { bits }` wider than the target word is rejected, even where Natural
  objects could hold the value. Fixed arithmetic is a fit assertion; explicit
  conversion to wide Fixed would require a separate modulo legalization.
- The pure pass supports 16-, 32- and 64-bit interpreter configurations. The
  target wrapper currently rejects 16-bit runtime Natural programs: generated
  code needs audited 6502 image/frame limits before native support is safe.
  The exact software-frame gate in `Target::limits` does not establish complete
  image placement, frame separation, or hardware-stack safety.
  An 8 KiB heap is only a proposed 6502 default, not a proven image budget.
  Prelegalized scalar IR retains its layout obligation, so target acceptance
  rejects it too: manual legalization cannot bypass the guard. The custom-budget
  compilation recipe above is for x86/wasm, not a supported route to native 6502
  runtime execution. Raw emission still requires validated, accepted input.
- Heap capacity is configurable but cannot exceed the target address space.
  Runtime helper generation checks relative object/pool sizes, not complete
  target placement. Preexisting pools, all appended constants, code/image origin
  and reserved stack/frame areas must fit together; a valid runtime Config alone
  is not a proof of this aggregate layout.
  Existing target stack limits still apply. Calling-convention limits do not
  refuse a program: `Target::prepare` packs parameters and results past a
  target's budget into a cell before legalization, so a natural result beside
  another travels in one. Shared legalization and the interpreter also support
  multiple results directly.
  Runtime helpers use borrowed arguments and a single owned result, not a host
  bigint ABI.
