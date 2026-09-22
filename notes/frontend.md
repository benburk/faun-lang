# Frontends

Faun has two source frontends while the Ori-compatible one is built out.

## Ori-compatible frontend

`faun check PATH` loads, parses, links, resolves, and performs the currently
available signature-directed checks on `.ori` source. Set `ORI_STD` to a
standard-library root when the program needs an implicit prelude:

```sh
ORI_STD=standard/ori/standard.ori cargo run -- check notes/examples/literals.ori
```

The accepted language remains a subset of Ori, but now includes:

- package roots with `lib {}`, imports, exports, and `Type.*` interfaces;
- nominal sum and wrapper types, type parameters, and method blocks;
- signatures, function types, structural variant types, and `where` constraints;
- clauses, guards, constructor/list/range/numeral patterns, and local bindings;
- names, arbitrary-size integer and character literals, strings and interpolation;
- lists, lambdas in call arguments, calls, static members, methods, and operators.

The parser can read Ori's current `standard.ori`, `nat.ori`, `int.ori`, and
`str.ori` files individually. `standard/ori/` supplies a bootstrap prelude with
the same `Nat`, `Int`, `U8`, `List`, and `Str` representations and the methods
needed by literal elaboration. The complete Ori standard package still contains
forms outside this slice, including records and tuples.

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
`path.ori` or `path/name.ori` form. Dependency maps in package headers and
compiler-provided host modules remain to be added.

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
intrinsics. Contextual checking currently covers explicitly signed first-order
functions; full polymorphic inference, method resolution, interpolation calls,
and complete HIR-to-Barb lowering remain.

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
cargo run --bin faun-simple -- run examples/exit.fn
cargo run --bin faun-simple -- inspect --emit barb examples/expressions.fn
```

The library module is `faun::simple`. Existing `faun::read*` functions still
run this frontend until the Ori-compatible frontend can lower complete programs.
