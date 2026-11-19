# Compile time

Every compile reads the whole standard library again: about 4,900 lines,
embedded in the compiler as text, lexed, parsed, resolved and type-checked
beside the program in one shared `Context`. So even
`main!(host) -> host.exit!(0)` takes 170 million instructions. This note
says where a compile's work goes, and how much of it a standard library
checked once, when the compiler is built, would save.

## Where it goes (2026-11-18)

Millions of user-space instructions in each stage of an x86-64 build, the
stock backend favouring speed, with mimalloc and FxHash. The last row is
the processor time of the whole process, pinned to one CPU of a busy
machine. Each frontend stage is split by where a definition was written:
the standard library and host (std) or the program's own package (user).

| Stage              | empty | checksum | n-body | k-nuc. | adler | position |
| ------------------ | ----: | -------: | -----: | -----: | ----: | -------: |
| Lex, parse: std    |  17.2 |     17.2 |   17.1 |   17.2 |  17.2 |     17.2 |
| Lex, parse: user   |   0.0 |      0.1 |    0.6 |    0.2 |   0.1 |      0.1 |
| Load, other        |   6.0 |      6.0 |    6.1 |    6.0 |   6.0 |      6.0 |
| Resolve: std       |  13.8 |     13.8 |   13.8 |   13.8 |  13.8 |     13.8 |
| Resolve: user      |   0.1 |      0.1 |    0.5 |    0.2 |   0.1 |      0.2 |
| Resolve: scopes    |   4.4 |      4.4 |    4.5 |    4.4 |   4.4 |      4.4 |
| Desugar to derive  |   2.7 |      2.7 |    2.8 |    2.7 |   2.7 |      2.7 |
| Check: std bodies  |  84.3 |     83.3 |   84.2 |   85.2 |  83.1 |     83.7 |
| Check: user bodies |   0.0 |      0.3 |    2.3 |    0.9 |   0.2 |      0.4 |
| Check: tables      |  31.7 |     31.8 |   32.7 |   32.0 |  31.8 |     31.9 |
| Exhaustive: std    |   9.5 |      9.6 |    9.5 |    9.5 |   9.6 |      9.6 |
| Exhaustive: other  |   0.6 |      0.6 |    0.8 |    0.6 |   0.6 |      0.6 |
| Monomorphize       |   0.3 |      2.6 |    8.5 |   12.5 |   2.1 |      2.3 |
| Second class to PC |   0.3 |      3.8 |   16.5 |   24.3 |   3.2 |      3.4 |
| Barb lowering      |   0.2 |      2.2 |    7.9 |   11.3 |   1.9 |      2.1 |
| Frontend drop      |   2.9 |      2.9 |    3.0 |    2.9 |   2.9 |      2.9 |
| Barb optimize      |   0.3 |      8.9 |  423.5 |  449.1 |   6.2 |      9.8 |
| Machine IR         |   0.1 |     12.3 | 1122.0 | 1266.9 |  23.1 |     31.1 |
| Target             |   0.1 |     49.1 |  166.7 |  689.3 |  82.5 |     96.6 |
| Whole process      | 175.9 |    253.2 | 1925.3 | 2630.8 | 293.1 |    320.4 |
| Processor ms       |    19 |       25 |    105 |    152 |    27 |       29 |

- **Check: tables** is the checker's whole-program work outside a body:
  the environment built from every signature, the declared and effect
  checks, publishing every expression's resolved type and elaborating the
  typed program. It grows with the standard library, not the program.
- **Second class to PC** is second-class checking, callback lowering,
  linearity and pattern compilation.
- **Machine IR** is mostly range analysis, which is what makes the float
  programs and k-nucleotide slow to compile.
- `adler` and `position` are probes; checksum is a suite kernel.

A hook kept out of the tree read the thread's instruction counter around
each stage, and around each module, definition and checked component for
the split. The medians of five runs are shown; the stages account for all
but 1.5 to 2.3 million of what `perf stat` counts for the whole process,
which starts, reads its arguments and writes the image besides.

Before mimalloc and FxHash the six compiles took 235.7, 334.2, 2,214.8,
3,013.0, 380.5 and 411.4 million in all: hashing cost the resolver and the
checker most, and the allocator every stage.

## With the library checked once (2026-11-19)

The standard library is now checked when the compiler is built, and a
compile reads what that left back from a snapshot built into the compiler,
as [the snapshot's note](std-snapshot.md) says. Once the library was
checked alone, that was 155 million instructions of every compile; reading
it back is 18 million, so each compile runs 137 million fewer:

| Compiles                     |  Before |   After | Change |
| ---------------------------- | ------: | ------: | -----: |
| Empty program                |   171.6 |    34.6 |   -80% |
| Suite programs, median       |   450.4 |   313.9 |   -30% |
| Suite programs, all together |  11,206 |   9,021 |   -20% |
| Probes, median               |   305.5 |   169.4 |   -45% |
| k-nucleotide, the slowest    | 1,755.1 | 1,619.4 |    -8% |

Millions of user-space instructions, the median of five x86-64 builds
favouring speed with the stock backend, pinned to one CPU, the suite's
sixteen programs each built once. The empty program takes 7 processor
milliseconds where it took 26. What is left of it is mostly decoding the
whole typed program, which specialization could instead decode a
definition at a time as it reaches them; for the suite, the machine tier
is most of what is left, as the table above shows.

The table above, and the sections below, are from before the snapshot.

## What a checked standard library would save

The work that depends only on the standard library is the same 172 million
instructions in every compile: lexing, parsing and resolving it, checking
its bodies, the checker's tables and its coverage. That is:

| Compiles                     |  Today | Before the quick wins |
| ---------------------------- | -----: | --------------------: |
| Empty program                |    98% |                   98% |
| Suite programs, median       |    36% |                   39% |
| Suite programs, all together |    18% |                   21% |
| Kernels                      | 12-68% |                14-70% |
| Benchmarks game              |  6-49% |                 7-52% |
| Probes                       | 47-59% |                50-61% |

The suite counts both images of each program, built favouring speed and
size. What the program decides is the rest: its own few million in the
frontend, specializing what it uses of the library, and above all the
machine tier, the analysis and code generation of what it specialized. A
snapshot would leave its loading in place of the 172 million, perhaps ten
million to read back typed definitions, so the empty program would compile
about ten times faster, a kernel or a probe two to three times, and a float
program a tenth.

### Where the boundary falls

The standard package is loaded first and is a prefix of the module and
source numbers: the prelude imports every library module but
`float.format`, which the float modules import. The host module, and
`hosts/common.fn` it imports, follow it, then the program's package. The
library does not import the host, so it is the same on every target; the
host differs per target and is 400 lines, cheap to check each time.

Symbols and sites are not a prefix. Resolution numbers them module by
module, the library's first, but desugaring, deriving, elaboration and
specialization allocate more for the whole program after the program's own
modules are resolved. A snapshot needs the frontend to run in two steps:
the library through checking alone, then the host and the program
resolved and checked against what the first step left, numbering on from
it.

What the first step leaves, and a snapshot would hold:

- the sources' text, for diagnostics in library code, and the symbols;
- each module's public interface and scope, and the aliases resolution
  expands;
- the library's typed definitions, which specialization copies;
- the checker's environment: schemes, bounds, `where` constraints, the
  methods each type answers and the variable names signatures use;
- the declarations and derived members, and the prelude's identities.

None of these types is serializable today: the frontend has no serde, so
it is either derives across the AST, HIR, typed HIR and checker types or
an encoding of its own. The compiler could write the snapshot in a build
script that depends on `faun-frontend`, and embed it as the text is
embedded now; `FAUN_STD` would go on reading text.

### Smaller steps first

- **Skip the library's coverage check.** The library is checked as a
  package of its own by `just test-std`; a program's compile could check
  coverage only in its own package: 9.5 million, 5% of the empty program.
- **Check library bodies on demand.** A signed definition's scheme is its
  signature, so a library body is needed only when specialization reaches
  it. Checking the bodies a program reaches, as specialization asks for
  them, would save most of the 84 million in bodies and a share of the
  tables' 32, without serializing anything, though lexing, parsing and
  resolving the library would remain.
