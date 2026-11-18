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
   both steps, and every image and refusal is what it was.
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

## Equivalence

The separation is tested by the evaluator and the test suite: every image
of the suite, the probes and their twins, and the examples, on every target
with both backends, built favouring speed and size, byte for byte the same
as before, and every refused program's message the same.

The snapshot will be tested by:

- a round trip: the state step one leaves, written and read back, is the
  state written;
- the same compile both ways: the frontend tests run step one from the text,
  and a test compiles the examples from the snapshot and from the text and
  compares their Barb;
- the evaluator, as for any change: every image the same.

## Open questions

- Whether specialization should decode the library's definitions as it
  reaches them, or the whole typed program once.
- Whether the host should have a snapshot of its own per target.
- How the snapshot is invalidated: today it is built with the compiler from
  the text built into the same compiler, so it cannot be stale; a snapshot
  read from disk, for `FAUN_STD`, would need the text's hash.
