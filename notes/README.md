# Notes

These notes explain what Faun programs mean, why the language is shaped the
way it is, and how the compiler turns meaning into machine work. Each topic
has one owning note, which states what is true today and answers the
questions a newcomer would ask: why this, and why not the alternatives.

The organizing idea is in the [README](../README.md): see how far a small
set of mechanisms goes toward C-like speed, Python-like concision and
Rust-like safety. Most rationale here is an argument that some mechanism is
not needed.

## Reading map

### The model

- [Computation](computation.md): strict, pure evaluation; unneeded work may
  be left out; termination is not checked
- [Types](types.md): inference, rows, `where` bounds, aliases and
  monomorphization
- [Dependent types](dependent-types.md): why Faun leaves them out, and what
  indexed types might still offer
- [Anti-features](anti-features.md): everything left out, each linked to its
  owner

### `values/`: what exists

- [Numbers](values/numbers.md): contextual numerals, arbitrary-precision
  `Nat`, wrapping words, division by zero
- [Floats](values/floats.md): the `F32` and `F64` contract
- [Strings](values/strings.md): UTF-8 bytes, splices and escapes
- [Tags](values/tags.md): nominal and structural variants, and rows
- [Records](values/records.md): structural records, update, builders
- [Tuples](values/tuples.md): positional products
- [Collections](values/collections.md): lists, maps, sets and hashing
- [Functions](values/functions.md): clauses, values, lambdas, second-class
  callbacks

### `forms/`: how programs are written

- [Syntax](syntax.md): goals of the grammar, and commas
- [Pattern matching](forms/pattern-matching.md): clauses, `is`, arms,
  leaving lines and coverage
- [Methods](forms/methods.md): type blocks, derived members and visibility
- [Operators](forms/operators.md): operators as methods, one `cmp`, and
  precedence
- [Modules](forms/modules.md): imports, exports, packages and `expect`
- [Effects](forms/effects.md): `!` calls, `Host`, capabilities and linear
  resources

### `machine/`: how meaning becomes work

- [Architecture](machine/architecture.md): the frontend, Barb, the machine
  IR and the three targets
- [Barb](barb.md): the first-order core's shape
- [Memory](machine/memory.md): reference counting and in-place reuse

### Decisions and explorations

- [Proposals](proposals/README.md): every change to the language, by status.
  An approved proposal records why a decision was made when it was made.
  The concept note above owns what holds now.
- [Pattern matching, the domain](pattern-matching.md): the exploration
  behind `is`, arms, leaving lines and loops
- [Host effects](host-effects.md), the
  [effects brainstorm](effects/README.md) and its
  [roadmap](effects/roadmap.md): host APIs to come
- [Lints](lints.md): what a linter should flag and the compiler leaves alone
- [Grammar audit](grammar-audit.md): whether the grammar stays LL(1) and
  free of ambiguity
- [N-body](nbody-performance.md) and
  [spectral norm](spectralnorm-performance.md): performance investigations
- [Faun and AI](ai-future.md)
- `archive/`: notes kept for reference that no longer describe the compiler

## Maintenance

- **One owner.** Semantics, rationale, costs and answers to "why" go in the
  note that owns the topic. Another note may say it in a sentence and link
  there.
- **True today.** A concept note describes the language as built on `main`.
  Something planned is marked planned and names the proposal that plans it.
- **Proposals are history; notes are the present.** When a proposal is
  approved and built, its lasting contract and rationale move to the owning
  note. The proposal stays as the record, with its errata.
- **Rationale answers questions.** Each concept note ends with a
  `## Rationale` of `### Why …?` and `### Why not …?` questions. Each answer
  gives the reason, the cost accepted and, where there is one, the recourse.
- **The source is authoritative for mechanics.** The
  [standard library README](../crates/faun/standard/README.md), the
  [grammar](../crates/faun/src/grammar.ebnf) and the refused programs in
  `crates/cli/tests/refused/` say exactly what is accepted. Where a note and
  the compiler disagree, the note is wrong.
