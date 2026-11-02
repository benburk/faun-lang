# Architecture

This note owns the shape of the compiler: the tiers a program passes
through, what each tier decides and leaves to the next, and the three
targets at the bottom. A Faun program is checked and made first-order in
the frontend, optimized as Barb, given a representation in machine IR, and
written out by a target for x86-64 Linux, wasm32 WASI, or the 6502 under
cc65's sim65 simulator. How values are counted and reused in memory is in
[memory](memory.md).

## The tiers

```text
source      → frontend   names, types, coverage, specialization, resources
            → Barb       first-order values; optimization and recognition
            → machine IR representation, ownership, structured control
            → target     registers, calling convention, encoding, image
```

**The frontend** (`crates/faun`) is a line of stages, each taking the
program as one tree:

1. Loading reads every module of the package and the packages it names.
2. Resolution names every global and local.
3. Checking infers types (Hindley–Milner, with rows and methods resolved
   by their receiver), writes the members a type asks for, and checks that
   patterns cover what they take apart.
4. Specialization makes each definition concrete at every type it is used
   at, which is monomorphization; functions are then checked to be second
   class.
5. Callback lowering makes a definition for each set of callbacks a
   function is handed, so no value is a function. Resources are then
   checked to be used up once.
6. Pattern compilation turns clauses into decisions, which Barb emission
   reads.

**Barb** (`crates/core/src/barb`) is a first-order language in A-normal
form (ANF), where every argument is a local and anything else is bound
first:

```text
body ::= (x = expr)* expr
expr ::= x | Ctor(x*) | value | name(x*) | match x { arm* }
arm  ::= Ctor(x*) -> body
```

A type is a name with constructors. `if` is a match on `Bool`, records and
tuples are one-constructor types, numbers are recursion over constructors.
A definition with no body is one the target computes, an effect among
them. Barb's [README](../../crates/core/src/barb/README.md) is its contract;
[barb](../barb.md) is the short form.

**Machine IR** (`crates/core/src/ir`) decides how each value is held: as a
word, a number known to fit some width, an arbitrary-precision natural, a
counted cell, or a sequence buffer. It places reference counts, lays out
data, and keeps control structured: regions take parameters, and a loop
stays the tail call it was written as. A short fixed schedule of passes
follows lowering.

**A target** (`crates/x86-64-linux`, `crates/wasm32-wasi`,
`crates/mos6502-sim65`) first fits the program to its word and its call
budget, then legalizes it: every count, allocation and buffer becomes
loads, stores and calls to routines generated in machine IR. Then it emits.
x86-64 allocates registers and writes a static ELF that makes system calls
itself; wasm32 writes a module importing WASI; the 6502 target holds a
16-bit word as two bytes and writes a sim65 image.

`faun emit barb FILE`, `faun emit machine FILE` and `faun emit target FILE`
print each stage. A definition counting a list, compiled for x86-64:

```text
count(v0: List<Str>) -> Nat = <length>
…
fn f0 main!(argc: 0..18446744073709551615) -> (word) = r0
```

Barb recognized `count` as a list's length, and the machine program reads
only how many arguments there are, so it makes no list of them at all.

## Rationale

### Why a first-order ANF core?

The fewer forms a core has, the less each pass has to handle. Barb has
five; every optimization, the evaluator and the validator read only those.
With no lambdas, every call names its callee, so inlining, recognition and
range analysis see the whole call graph. With ANF, every intermediate value
has a name to hang a fact on: its range, its length, whether it is the
answer of a recognized operation.

The cost is that the frontend must take apart everything higher-level
before Barb sees it: blocks, records, tags, callbacks and generic code.

### Why monomorphize and remove function values before Barb?

So representation can follow the concrete type. `List(U8)` is a buffer of
bytes and a `List` of five-field records a buffer of flat elements, which
only a tier that knows the element type can choose. Generic code then
needs no boxed uniform representation and no runtime dictionary of
methods.

Function values go the same way. A callback is passed straight into a call
and never held, so the frontend makes a definition for each set of
callbacks it is handed, and calling the parameter is a direct call. Barb
needs no closures, which would otherwise be allocated and called
indirectly.

The cost is code size and compile time, a copy for each type and each set
of callbacks. Two kinds of program would need unboundedly many copies and
are refused: a recursive call at a larger type, and a recursive call
wrapping its callback in a new lambda each time round.

### Why no LLVM or libc?

Barb's goals are to compete with LLVM in a fraction of the code, to make
better code on awkward targets such as the 6502, and to make a backend
easy to add. LLVM fits none of the three targets well:

- **The 6502** has three 8-bit registers, each with its own job. A general
  register allocator sees them as a hard coloring problem and fills the
  code with copies, as one LLVM-MOS contributor reports.
- **WebAssembly** wants structured control. LLVM's control flow graph has
  to be put back into structure by a Relooper; Faun's machine IR never
  flattens structure, and lowering it to jumps for x86 takes about fifteen
  lines.
- **Faun's semantics** let pure work be left out even where it would not
  have come back, and keep effects in order without a world value. Barb
  states those rules once and every pass keeps them; LLVM would need them
  expressed through its attributes.

Linux's system call interface is stable, so an x86-64 program needs
nothing else: no libc, no dynamic loader. WASI is the wasm32 target's
system interface and sim65's hooks the 6502's. The allocator, reference
counting, arbitrary-precision arithmetic and sequence buffers are routines
written in machine IR, so every target has the same ones.

The cost is everything LLVM would give for free: vectorization, a mature
register allocator, debug information, and more targets. Scalar C still
runs spectral norm 1.54 times as fast; the measurements are in
[spectral norm](../spectralnorm-performance.md) and
[n-body](../nbody-performance.md). macOS and Windows offer no
stable system call interface, so a target for either will need their
system libraries; how is part of the open FFI question in
[effects](../forms/effects.md).

### Why semantics that no backend changes?

A program means the same on a 64-bit machine, in a 32-bit wasm module and
on an 8-bit processor with 16-bit addresses. So the source and Barb name no
width, layout, address or target intrinsic: a value is what it holds, never
where, and Barb chooses each type's representation. Representation can
then differ by target, as a file descriptor is a `U32` on Linux and WASI and
a `U16` on sim65, without a program noticing. Much of the test suite runs
the same programs on all three targets.

The cost is that a program cannot ask for a layout, an instruction or a
calling convention. There is no inline assembly and no way to share a
struct with C, which FFI will have to answer.

### Why compile the whole program?

Specialization needs every call site to know which copies to make, and
callback lowering every callback a function is handed. A target supplies
only the routines the program reaches, and a host field nothing reads,
such as `args`, is never produced. Each is a fact about the program as a
whole that no separately compiled module could know.

The cost is that the standard library and every dependency are compiled
again with each program, from source. There are no binary libraries and
no separate compilation.

### Why recognize by shape and never by name?

`Nat` is two constructors and a file of functions, `List` the same, and the
standard library is ordinary Faun. Barb recognizes what a definition
computes from its equations: addition over `Nat`'s constructors, a count of
a list, a bitwise walk. So a program's own `count` above is answered from
the length a list holds, as the library's `len` is, and a type of one's own
with the same shape gets the same treatment. A recognition that misses
costs speed, never meaning: the definition runs as written.

The one exception is floats. `F32` and `F64` are IEEE 754 formats written
in Faun over `U32` and `U64` patterns, and no equation says that a
definition is IEEE 754's addition: recognizing correct rounding from a body
is beyond any recognizer. So lowering claims, by name, that `add`, `sub`,
`mul`, `div` and `sqrt` at each float's own type compute that operation
(`Program::claim`). Barb checks only the claim's shape. The definitions
stay and run wherever nothing faster does, on a target without float
instructions such as the 6502, and
`examples/floats/` is run both with and without the claims to check them.

## Related

- [Memory](memory.md): reference counting and reuse in the machine tier
- [Barb](../barb.md) and its
  [README](../../crates/core/src/barb/README.md): the core's contract
- [Types](../types.md): inference, rows and monomorphization in the frontend
- [Functions](../values/functions.md): second-class callbacks
- [Floats](../values/floats.md): the float contract the claims stand for
- [Effects](../forms/effects.md): bodyless definitions, and FFI left open
- [Machine IR, archived](../archive/machine-ir.md): the tier's contracts in
  detail, partly out of date
