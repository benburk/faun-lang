# Frontends

Faun has two source frontends while the Ori-compatible one is built out.

## Ori-compatible frontend

`faun check PATH` lexes and parses `.ori` source. The current grammar is a
strict subset of Ori and accepts:

- nominal constructor types, including type parameters;
- first-order signatures;
- function clauses with names, wildcards, constructors, and integer patterns;
- local bindings;
- names, integer literals, calls, method calls, unary operators, and binary
  operators.

It does not lower to Barb yet. Imports, exports, method blocks, records, tuples,
lists, strings, guards, lambdas, constraints, and type inference remain to be
ported. These forms fail during parsing rather than entering an incomplete AST.

The lexer follows Ori's layout rules. Tokens retain byte ranges plus
`space_before` and `newline_before`, so the PEG grammar can distinguish `f(x)`
from `f (x)` without retaining whitespace. AST names are byte ranges into the
input instead of allocated strings. Call `Name::text` with the original source
to read one.

Run the frontend throughput benchmark in an optimized build:

```sh
cargo bench -p faun --bench frontend
```

It measures lexing and full parsing separately over three 100,000-line inputs:
small clauses, a mix of declarations and expressions, and nested constructor
results. It reports the best of seven runs and prints the 500,000 lines/s goal.
The benchmark uses mimalloc, as both compiler binaries do. This is still a
parser benchmark, not a claim about name resolution, type inference, lowering,
or end-to-end compilation.

### Grammar cost

The grammar dispatches a term declaration once, then chooses a signature on `:`
or a clause on an adjacent `(`. Expression precedence uses `precedence!`, and
postfix calls, method calls, and infix operators begin with distinct tokens.
These paths do not retry whole declarations or expressions.

A body is less obvious because `Succ(Succ(x))` can be either a binding pattern
or its final expression. A plain `binding()* result:expr()` parses and allocates
the complete constructor tree as a pattern, fails to find `=`, discards it, and
then parses it again as an expression. The body rule now performs a
non-allocating delimiter scan for a following `=` before invoking the pattern
rule. The pattern rule still validates the syntax. This keeps nested constructor
results from taking that full retry.

Two bounded retries remain. A result-only signature first tries the
parameter-and-arrow form, then reads its type again when no arrow follows. The
shared `|`, `-`, and `*` glyphs may retry one token while adjacency decides
between infix and prefix/splice syntax. Neither retry nests another ambiguous
choice, so the current grammar has no known exponential backtracking path.
Keep future alternatives token-dispatched where possible; add PEG rule caching
only after a benchmark shows the same complex rule being retried at one input
position.

## Simple frontend

`faun-simple` preserves the old `.fn` language and complete compiler pipeline.
Use it for backend development and the existing examples:

```sh
cargo run --bin faun-simple -- run examples/exit.fn
cargo run --bin faun-simple -- inspect --emit barb examples/expressions.fn
```

The library module is `faun::simple`. Existing `faun::read*` functions still
run this frontend so backend clients do not change while the replacement cannot
lower programs.
