# Runtime naturals

`Target::compile` prepares, validates, accepts and emits the same scalar machine
program. The CLI uses this interface. `Target::emit` is a raw backend interface:
its input must already be validated and accepted; it does not legalize naturals.
`Target::prepare` exposes the transformed program for inspection and evaluation.

`ir::legalize(&Program, ir::natural::Config)` rebuilds the arena-backed program,
keeping original function/platform IDs and existing data/globals intact. Only
original Natural values become owned object addresses. Ordinary addresses are
not reference counted, and address/natural reinterpretation is rejected. Host
signatures containing Natural have no supported bigint ABI. Source host arguments
must have a fit proof; implicit effects are not requests for modulo conversion.

The shared runtime uses base-256 magnitudes and a reusable bounded private heap.
Its default budget is 64 KiB on x86-64 and wasm32. Allocation or reference-count
exhaustion exits with status 2; it never returns a wrapped integer or zero in
place of a failed allocation. Explicit `Convert` to scalar classes truncates.
Clients can select a different budget by legalizing explicitly before emission.
This is a memory resource limit, not a numeric modulus.

Each local natural result owns one reference. Function arguments are borrowed;
function results, branch results and loop state transfer owned references.
Outgoing aliases are retained individually before exited scopes are released.
Nested loop exits do not release ancestor captures; function returns unwind all
local scopes but not borrowed parameters. Dead locals remain live until their
region exits, so peak memory can be higher than with last-use placement. Loop
iteration cleanup reclaims dead allocations rather than accumulating history.

## Deliberate limits

- `Fixed { bits }` wider than the target word is rejected, even where Natural
  objects could hold the value. Fixed arithmetic is a fit assertion; explicit
  conversion to wide Fixed would require a separate modulo legalization.
- The pure pass supports 16-, 32- and 64-bit interpreter configurations. The
  target wrapper currently rejects 16-bit runtime Natural programs: generated
  code needs audited 6502 image/frame limits before native support is safe.
  An 8 KiB heap is only a proposed 6502 default, not a proven image budget.
  Manually legalized scalar IR no longer carries the Natural marker: feeding it
  to the 6502 backend bypasses this guard and remains the raw-emitter caller's
  responsibility. The custom-budget compilation recipe above is for x86/wasm,
  not a supported route to native 6502 runtime execution.
- Heap capacity is configurable but cannot exceed the target address space.
  Existing target calling-convention/stack limits still apply. Native x86-64
  compilation rejects functions with more than six arguments or one result;
  shared legalization and the interpreter also support multiple results.
  Runtime helpers use borrowed arguments and a single owned result, not a host
  bigint ABI.
