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
`Program::layout()` obligation containing `Config.word_bits` and
`Endian::Little`. Legalization, target acceptance and interpretation reject a
mismatched word size or byte order before execution or emission. Cloning and
re-legalizing preserve this obligation; scalar-only legalization leaves portable
programs unbound.
This is a memory resource limit, not a numeric modulus.

Each local natural result owns one reference. Function arguments are borrowed;
function results, branch results and loop state transfer owned references.
Outgoing aliases are retained individually before exited scopes are released.
Nested loop exits do not release ancestor captures; function returns unwind all
local scopes but not borrowed parameters. Dead locals remain live until their
region exits, so peak memory can be higher than with last-use placement. Loop
iteration cleanup reclaims dead allocations rather than accumulating history.

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
  Existing target calling-convention/stack limits still apply. Native x86-64
  compilation rejects functions with more than six arguments or one result;
  shared legalization and the interpreter also support multiple results.
  Runtime helpers use borrowed arguments and a single owned result, not a host
  bigint ABI.
