# A checked standard library

[Compile time](compile-time.md) found that 172 million of the empty
program's 176 million instructions are the standard library's: lexing,
parsing, resolving and checking the same 4,900 lines in every compile. This
note is the design for checking it once, when the compiler is built, and
loading what checking it leaves instead: a snapshot. Checking library bodies
lazily, only those a program reaches, was the other way weighed; it is not
taken, since it would leave lexing, parsing and resolving in place and make
the checker's order depend on the program.

The work goes in steps, each a pull request reviewed before the next:

1. **This note**, and **the separation**: the frontend checks the standard
   package alone, then the host and the program against what that left,
   numbering on from it. Nothing is serialized, so every compile still runs
   both steps, and every image and refusal is what it was but where symbol
   numbering shows, below.
2. **The snapshot**: what the first step leaves, written when the compiler
   is built and read back in place of the first step.

## The boundary

The standard package is everything the prelude, `standard.fn`, reaches:
every library module, `float.format` through the float modules. It never
imports `std.host`, so it is the same on every target. The host, with
`hosts/common.fn`, and the program's own package come after it, and are
checked per compile.

**Step one** loads the standard package alone and takes it through every
stage of [`checked()`](../crates/frontend/src/lib.rs): resolution, record
builders, grouping, deriving, inference, elaboration and coverage. What it
leaves is a `Library`.

**Step two** goes on loading from where the library's loader stopped,
reading the host and the entry's package, and resolves, desugars, groups,
derives, infers, elaborates and covers only those modules, against the
library's state, which it extends: sources, modules, symbols and sites are
numbered on from the library's. The two typed programs are then one, the
library's definitions first, and specialization reads it as before.

An entry inside the standard package, as `just test-std` checks the
library's own expectations, is checked in one step, as before the
separation: its package is the library, so there is nothing to check it
against.

Every stage after checking, from specialization to Barb, still sees one
program and one `Context`.

### As built

[`library.rs`](../crates/frontend/src/library.rs) holds the two steps. The
loader stops after the standard package and goes on from where it stopped;
resolution, the record builders, grouping, deriving, the checker and the
coverage check each take the modules after those already checked, with what
checking those left: an `Earlier` holding the number of modules checked,
the next site, the prelude's identities, resolution's values and aliases,
the builders' pairings, the checker's `Environment` and the typed program.
Checking the whole program in one step is the same code with an empty
`Earlier`, which is how an entry inside the standard package, and the
frontend's own tests, are checked.

Once the library is checked its modules' syntax is dropped, so nothing after
can read it: a snapshot will not have it.

## What crosses it

Everything step two reads of step one, which is what a snapshot holds:

- **Sources**: each library module's name and text. A diagnostic may point
  into the library, at a signature a call does not fit, so the text must be
  there; for the built-in library it is the text already embedded, so a
  snapshot need hold only the names.
- **Symbols**: every spelling interned so far, in order, since a symbol is
  its index. Resolution interns as it goes, and deriving and elaboration
  intern more.
- **Sites**: the next number, and which sites are splices' `to_str` calls.
- **The loader's state**: each library module's path, source, namespace,
  scope and public interface, the paths already loaded, the prelude's
  exports every later module sees, the standard root, and how many packages
  have been given a root. The modules' syntax does not cross: nothing after
  step one reads it.
- **Resolution's state**: which globals are values, written `name = value`,
  and every alias and constraint alias, as written and as expanded, since a
  program's signature may name the library's aliases.
- **The record builders' pairings**: the library functions whose signature
  asks for record builders, which a program's call may use.
- **The prelude's identities**, `PreludeIds`: the types and members literals
  and patterns are made of.
- **The checker's environment**: each definition's scheme and `where`
  bounds, the names its signature gives its type variables, the signatures
  that write `_`, where each definition is introduced, each constructor's
  scheme, each record field's owners, and the methods each spelling names,
  signed and unsigned. Inference's own state need not cross: once the
  library is checked, every scheme can be written out resolved, so a
  snapshot holds them closed, and inference starts its variables after the
  largest one they use.
- **The library's typed program**: every definition as typed HIR, its
  scheme, its declared types, and the members each type has by spelling.
  This is the largest part.

What step one leaves today, for the built-in library: 22 modules from 162
KB of text, 1,428 symbols, 745 typed definitions holding 9,096 expressions,
21 declared types and 449 members by spelling, 745 schemes with 177 method
spellings and 36 constructors in the checker's environment, and two
functions asking for record builders. Printed with `Debug`, the typed program
is 2.3 MB and the modules' interfaces 78 KB; a binary encoding would be a
tenth of that or less.

### How specialization reads library bodies

Specialization starts from `main!` and the program's own definitions, and
copies each library definition it reaches, at the types it is reached at,
from the typed program. It reads nothing else of the library: no syntax, no
inference state. A program reaches a small part of the library, so a format
that can read one definition without the others would let a compile decode
only what it reaches; the first snapshot decodes the whole typed program,
and measures whether that matters.

### The host

The host is checked per compile, against the library, as the program is. It
is 420 lines of the 4,900, mostly signatures, and differs per target, so a
snapshot per target would multiply build time for little. If it shows in a
profile once the library is a snapshot, each target's host could be a
second, smaller snapshot taken on top of the library's.

## `FAUN_STD`

`FAUN_STD` names a directory to read the library's text from, to work on it
without rebuilding. Where it is set, step one runs from that text, as it
does today, and no snapshot is read: the snapshot is the built-in text's.
`just test-std` sets it, and checks the library in one step.

## The format

None of these types serializes today. The candidates:

- **serde, with bincode or postcard.** Derives across the typed HIR, the
  checker's environment and the interfaces, and a compact binary encoding.
  Decoding builds the ordinary owned types, so nothing downstream changes.
  It costs a dependency the frontend does not have, a derive on a hundred
  or so types, and wrappers where a type has no serde support: the
  `FxHashMap`s need the `serde` feature of `rustc-hash` or a conversion,
  `BigUint` its `serde` feature, and the checker's `Rc` types are resolved
  into owned ones before writing anyway. Decoding allocates every node, as
  checking does now, but does none of checking's work.
- **rkyv, read in place.** The snapshot is mapped and read without decoding,
  so a compile pays only for the definitions it touches. But every stage
  reads the ordinary types, so either they become generic over archived
  forms or what is reached is decoded anyway, at which point rkyv is a
  decoder like the others. Safe access validates the whole archive on each
  load, which costs a share of what decoding would; skipping that check
  needs `unsafe`, which the workspace forbids. It is also the most
  intrusive to maintain: archived types are a parallel set of types.
- **An encoding of its own.** A hand-written writer and reader per type.
  No dependency, and the format can index the typed program by definition,
  so specialization decodes a library definition only when it reaches it.
  It is the most code to keep in step with the types, though a round-trip
  test catches a field forgotten.

The plan is serde with postcard: the least code, an encoding as compact as
the hand-written one would be, and the decoding cost is measured before
anything cleverer is built. If decoding the whole typed program shows, the
typed program alone can move to a table of separately encoded definitions,
decoded as specialization reaches them, without changing the rest.

## The build step

The frontend cannot embed a snapshot of itself: its build script would have
to depend on the crate it builds. So the command's crate does it.
`crates/cli/build.rs` takes `faun-frontend` as a build dependency, runs step
one on the built-in library, writes the snapshot to `OUT_DIR`, and the
command embeds it with `include_bytes!` and hands it to the frontend, which
reads it in place of step one where `FAUN_STD` is not set. A build of the
frontend without a snapshot, its own tests among them, runs step one from
the text, as now.

Building the frontend for the build script compiles it a second time, for
the host and without the release profile's optimization; checking the
library unoptimized takes perhaps a second. Cargo's `build-override` can
raise the build script's optimization if that shows.

## What the separation changed

The empty program compiles in 171 million instructions where it took 174,
and the others in about 1% to 2% fewer; of the 171, step one is 155 million,
which is what a snapshot would replace with reading it back:

| Compile  | Before |  After | Step one | Its share |
| -------- | -----: | -----: | -------: | --------: |
| empty    |  174.1 |  171.1 |    154.8 |       90% |
| checksum |  250.6 |  247.3 |    154.8 |       63% |
| n-body   | 1169.2 | 1165.1 |    154.8 |       13% |
| k-nuc.   | 1987.9 | 1983.5 |    154.8 |        8% |
| adler    |  287.4 |  284.4 |    154.8 |       54% |
| position |  312.7 |  307.7 |    154.8 |       50% |

Millions of user-space instructions, the median of five x86-64 builds
favouring speed, pinned to one CPU, with the process's start, 1.3 million,
taken from step one. The rest of the empty program's compile is the host's
loading and checking, specialization, the tiers below, and dropping it all.

Every image is byte for byte what it was, on every target with both
backends, built favouring speed and size, but seven programs': n-body of the
suite, its untyped twin among the examples, two Advent of Code solutions,
the rock-paper-scissors arena and the JSON and LRU libraries' examples. In
each, a record's fields are laid out in another order, and so are the
values built and read with it, and nothing else differs. One refusal says
`{y: Nat, x: Nat}` where it said `{x: Nat, y: Nat}`.

The cause is that a record's fields, and a tag row's tags, are kept in the
order of their names' symbols, which is the order the names were first
interned. Before, the program's declarations were loaded before the
library's bodies were resolved, so a field name the program declared came
before a name only the library's bodies use; now the library is resolved
and checked first, so its names come first. `Vec3 : {x: F64, y: F64, z: F64}`
in n-body is laid out `y, x, z`, since a library body binds a `y` and none
binds an `x`. No numbering that checks the library first can keep the old
order, since it put names the program declares between the library's. A
snapshot has the same order as this separation, so the images it makes will
be these.

## Equivalence

The separation is tested by the evaluator and the test suite, comparing
every image of the suite, the probes and their twins, and the examples, on
every target with both backends, built favouring speed and size, with the
trunk's, and every refused program's message; and by a test that checking a
program after the library leaves the library's typed program as it was.

The snapshot will be tested by:

- a round trip: the state step one leaves, written and read back, is the
  state written;
- the same compile both ways: the frontend tests run step one from the text,
  and a test compiles the examples from the snapshot and from the text and
  compares their Barb;
- the evaluator, as for any change: every image the same.

## Open questions

- Whether a record's fields and a row's tags should be ordered by their
  spelling rather than by when their names were interned. A layout would
  then not move when the library's bodies start or stop using a name, and a
  refusal would show `{x: Nat, y: Nat}` however the names were met. It
  would move many images once, and is a change of its own.

- Whether specialization should decode the library's definitions as it
  reaches them, or the whole typed program once.
- Whether the host should have a snapshot of its own per target.
- How the snapshot is invalidated: today it is built with the compiler from
  the text built into the same compiler, so it cannot be stale; a snapshot
  read from disk, for `FAUN_STD`, would need the text's hash.
