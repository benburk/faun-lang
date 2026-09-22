# Frontends

Faun has two source frontends while the Ori-compatible one is built out.

## Ori-compatible frontend

`faun check PATH` loads, parses, links, resolves, and performs polymorphic type
inference on `.fn` source. The primary `faun` crate supplies its standard package,
so commands need no environment setup:

```sh
cargo run -- check crates/faun/examples/literals.fn
cargo run -- check crates/faun/examples/utilities.fn
```

The accepted language remains a subset of Ori, but now includes:

- package roots with `lib {}`, imports, exports, and `Type.*` interfaces;
- nominal sum and wrapper types, type parameters, and method blocks;
- signatures, function types, closed record types, structural variant types, and `where` constraints;
- clauses, guards, constructor/list/record/range/numeral patterns, and local bindings;
- names, arbitrary-size integer and character literals, strings and interpolation;
- records, field projection, lists, lambdas in call arguments, calls, static members, methods, and operators.

The grammar follows Ori's source language, while Faun source and package files
use the `.fn` extension. `crates/faun/standard/` supplies a bootstrap
prelude with
`Bool`, `Nat`, `Int`, `U8`, `List`, `Result`, and `Str`. It includes concrete
arithmetic, Boolean, collection, and result utilities that avoid hashing,
tuples, record rows and updates, and postfix propagation. Concrete equality implementations
replace bodyless derivation where no method constraint is needed. The complete
Ori standard package still contains forms outside this slice.

### Module and name model

A parsed module owns one `SourceId`; its spans remain two `u32` byte offsets.
Raw ASTs are never concatenated. The loader gives every module a unique
namespace, builds public interfaces, and leaves private declarations private.
Standard namespaces derive from their package-relative paths, so loading order
does not change their identities.

Resolution produces a separate HIR. Global names become four-byte interned
symbols and locals become clause-local integer IDs. This avoids allocating names
in the parser or repeatedly rewriting the surface tree as modules are merged.

The loader currently supports package-relative disk modules in either
`path.fn` or `path/name.fn` form. For applications it also mounts one
compiler-selected source module at the virtual path `std.host`. Dependency maps
in package headers remain to be added.

### Blessed literals

Literal spellings survive parsing losslessly. Numerals are decoded to
arbitrary-precision magnitudes only when resolution or checking reaches them.
String text remains source spans until that boundary, where escapes are decoded
to UTF-8 bytes.

A loaded prelude is inspected once to produce `PreludeIds`. The compiler-known
contract is deliberately narrow:

- an unconstrained nonnegative numeral defaults to `Nat`;
- a numeral expected as `Int` becomes `Int.of_nat(<Nat literal>)`;
- a directly negative `Int` additionally calls `Int.neg`;
- a negative `Nat` is rejected rather than losing its sign;
- a plain string builds the private `Str`, `List`, and `U8` cells directly from
  its UTF-8 bytes.

These expansions lower through ordinary Barb constants, constructors, and
calls. `Nat` arithmetic and the constructors of `Int` are not compiler
intrinsics.

### Type inference and methods

Signatures quantify their lowercase type variables and instantiate them at each
use. Unsigned definitions use Hindley–Milner inference: call-graph components
are checked monomorphically for recursion and generalized when each component
closes. Local bindings are generalized as well. Constructors participate with
schemes derived from their data declaration.

Dotted calls and operators resolve against the nominal head of their inferred
receiver type. Resolution may wait for argument, result, or literal constraints;
an otherwise unconstrained numeral defaults to `Nat` (or `Int` when negative)
before the final method choice. The checked result records each expression and
clause type together with canonical method targets and principal global schemes;
calls that remain ambiguous are rejected.

Method constraints are not implemented: a signature containing `where` is
rejected during checking. Bodyless signatures do not derive implementations;
the bootstrap prelude writes concrete `Bool`, `Nat`, and `Int` equality and
omits generic equality requiring bounds.

### Application and host contract

An application imports its compiler-selected interface explicitly and defines
one entry with the exact canonical signature:

```faun
import std.host {Host exit!}

main! : Host -> []
main!(host) -> exit!(host host.argc)
```

Each target-owned host module declares `Host : {argc: Nat}` and
`exit! : Host Nat -> []`. The empty structural variant type has no values, so
these computations cannot return. The record field is immutable startup data; the
explicit `Host` argument is authority to perform the effect. Pure definitions
cannot call names ending in `!`, and an effect call must stand alone as a local
binding or clause result.

`faun build --emit barb --target TARGET PATH` discovers `main!`, follows
reachable calls, specializes polymorphic globals and nominal data, then
optimizes and prints the resulting Barb program. `--emit machine` continues
through representation selection and machine-IR optimization, stopping before
target preparation. Ordinary `faun build` continues through preparation and
artifact emission. Barb keeps `main!(host: Host)` as its entry and preserves
`Host` construction and record projection. Machine lowering represents the current
one-field host transparently, and each target constructs the named `host` entry
value from its physical startup convention. Source calls to `exit!` erase
the authority argument before machine IR checks the provider signature.

Global functions, constructor functions, and lambdas with captures all use the
same first-order representation. Clause matrices become exhaustive Barb
matches; direct calls, methods, records, field projection, list syntax,
wrappers, and elaborated literals become ordinary Barb constructors, matches,
calls, and constants. Reachable bodyless signatures remain external Barb
declarations.

Lowering currently rejects ranges, interpolated strings, local destructuring
bindings, nonempty structural variants, polymorphic non-application entries, record
updates and rows, and local bindings whose generalized value itself requires
multiple specializations. Tuples, constraints, and postfix propagation remain
earlier frontend gaps.

### Performance

Run the frontend throughput benchmark in an optimized build:

```sh
cargo bench -p faun --bench frontend
```

It measures lexing and complete single-file parsing over three 100,000-line
inputs: small clauses, a mix of declarations and expressions, and nested
constructor results. It reports the best of seven runs and prints the 500,000
lines/s goal. The benchmark uses mimalloc, as both compiler binaries do. Module
I/O, linking, resolution, typing, and lowering are deliberately not included.

Literal validation does not walk ordinary numeric programs. The parser performs
the extra syntax walk only when lexer tokens show that character or string
escapes need validation.

### Grammar cost

The grammar dispatches module items and term declarations by their leading
tokens. Expression precedence uses `precedence!`; postfix calls, member access,
and infix operators begin with distinct tokens.

A body is less obvious because `Succ(Succ(x))` can be either a binding pattern
or its final expression. A non-allocating delimiter scan checks for a following
`=` before invoking the pattern rule. This prevents nested constructor results
from being parsed and allocated twice.

A result-only signature can still retry its type after the parameter-and-arrow
alternative fails. Shared `|`, `-`, and `*` glyphs may retry one token while
adjacency distinguishes infix syntax from lambdas, negation, and list rests.
These retries are bounded and do not nest another ambiguous declaration choice.
Add PEG caching only after a benchmark demonstrates repeated expensive work at
one input position.

## Simple frontend

`faun-simple` preserves the old `.fn` language and complete compiler pipeline.
Use it for backend development and the existing examples:

```sh
cargo run --bin faun-simple -- run crates/simple/examples/exit.fn
cargo run --bin faun-simple -- inspect --emit barb crates/simple/examples/expressions.fn
```

The library crate is `faun-simple`; it owns this syntax, its pipeline entry
points, and `crates/simple/standard/`. The primary syntax and
`crates/faun/standard/` belong to the `faun` crate. Both frontends depend on
the shared `faun-core` compiler core; the separate `faun-driver` crate composes
the primary frontend with whichever targets an executable registers.
