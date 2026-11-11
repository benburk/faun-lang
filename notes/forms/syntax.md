# Syntax

## Goals

- No symbol table required to parse it
- Fast to parse
- Layout- and indentation-agnostic
- small deterministic parser, limited lookahead, no explosive search through alternative interpretations
- LL(1) grammar for simpler parsing, incremental parsing, error recovery, better error messages
- few keywords

## Commas

Peers are parted by commas in every sequence written between delimiters:
arguments and clause-head patterns, lambda parameters, tuples, lists,
records and their patterns, type arguments, function, tuple and record
types, tag rows, and the names of `import`, `export` and `package`.

```ruby
export {Area, merge}

Area = {left: Nat, top: Nat, right: Nat, bottom: Nat}

merge : (List(Nat), List(Nat)) -> List(Nat)
merge([], ys) -> ys
merge(xs, []) -> xs
merge([x, *xt], [y, *yt]) if x <= y -> [x, *merge(xt, [y, *yt])]
merge([x, *xt], [y, *yt]) -> [y, *merge([x, *xt], yt)]
```

- A sequence may end with a comma, a rest's included: `[h, *t,]`. A
  `where` list is the exception: its last constraint takes none.
- A function type's parameters are parenthesized, as a clause head's are:
  `add : (Nat, Nat) -> Nat`. One parameter may go bare, `fib : Nat -> Nat`,
  and a tuple-typed parameter keeps its own parentheses,
  `((Nat, Nat)) -> Nat`.
- A tuple has at least two members: `(a)` groups, and `(a,)` is an error.
- A call's `(` touches what it calls: `f (x)` is an error.
- Method blocks `.( … )`, bindings, method chains, operators and string
  splices take no commas.

Space never chooses between two readings. A prefix `-` or `!` and a rest's
`*` touch what they take, and an infix `-` or `*` is spaced or touching on
both sides alike, so `[a -b]`, `x -3` and `a *b` are refused rather than
read one way. The [grammar](../../crates/faun/src/grammar.ebnf) states the
exact rules.

## Rationale

### Why commas?

They are what every reader expects, so the syntax spends none of its
strangeness on separators. Whitespace-separated arguments are the first
thing a reader notices, and every discussion of the language would begin
there instead of with totality, effects or in-place reuse. Roc moved from
whitespace application to `f(a, b)` for much the same reason.

The concrete gains:

- **Compound arguments.** Without commas the reader has to know precedence
  to count arguments. About 2–3% of lines have such an argument, and they
  are the lines that are hard to read:

  ```ruby
  lower(r * 10 s mp * 10 mm * 10 k - 1 closed fuel digits)
  lower(r * 10, s, mp * 10, mm * 10, k - 1, closed, fuel, digits)
  ```

- **Records.** `{x: n y: n.add(n)}` scans as `x: (n y): …` until the eye
  finds the colons.
- **Editors.** Argument text objects (targets.vim, mini.ai) and `f,`
  jumping split on commas, and work before any tree-sitter grammar exists.
- **Diagnostics.** A dropped operator used to be another call: `f(a + b)`
  without its `+` was `f(a b)`, two arguments, and the mistake surfaced as
  an arity or type error. Now it fails at the gap with "expected `,`", and
  a comma is a place to resume after an error in a long list.
- **Pasted and generated code.** Readers of C, Rust, Python and JSON see
  `f(a b)` as a missing comma, and so do language models trained on them.

The cost is under [What do commas cost?](#what-do-commas-cost).

### What do commas cost?

Length, mostly in the long lines. A heuristic tokenizer counted peer
boundaries over the Ori corpus (151 files, 7,698 code lines) and Faun's
`.fn` files (41 files, 2,731 code lines) as they were in September 2026,
±5%. Mean line length rose about 3%, and 4.5% on clause lines, but a third
more Ori lines crossed 80 columns and twice as many Faun lines crossed 100:

|                        | Ori before | Ori after | Faun before | Faun after |
| ---------------------- | ---------: | --------: | ----------: | ---------: |
| Mean line length       |       40.1 |      41.3 |        39.1 |       40.6 |
| Lines changed          |          — |       53% |           — |        58% |
| Lines over 80 columns  |        315 |       417 |         145 |        183 |
| Lines over 100 columns |         57 |        78 |          18 |         37 |

Where the commas fall:

| Context              |    Ori |  Faun |
| -------------------- | -----: | ----: |
| Clause-head patterns |  3,017 | 1,686 |
| Call arguments       |  2,388 |   846 |
| Lists                |  1,361 |   295 |
| Signature parameters |  1,271 |   702 |
| Type arguments       |    523 |   151 |
| Tuples               |    401 |    82 |
| Records              |    369 |    62 |
| Imports and exports  |    229 |    98 |
| Tuple types          |    220 |    37 |
| Tag rows             |    191 |    81 |
| Record types         |    102 |    13 |
| Total                | 10,072 | 4,053 |

Clause heads and signatures take 43% of them in Ori and 59% in Faun, so
pattern-matching code pays the most, and a clause group loses the look of
a table:

```ruby
merge([x *xt] [y *yt]) if x <= y -> [x *merge(xt [y *yt])]
merge([x, *xt], [y, *yt]) if x <= y -> [x, *merge(xt, [y, *yt])]

step(digit _ _ _ _ _ _ True False) -> [digit]
step(digit, _, _, _, _, _, _, True, False) -> [digit]
```

Short, plain elements (names, `_`, literals, small patterns) read better
without commas; anything with an operator, a colon or a nested call reads
better with them. One separator rule for all of them was judged worth the
loss in the first kind.

### Why can spacing not change meaning?

With whitespace as the separator, spacing had to settle what `-`, `*` and
`|` were: `a - b` subtracted and `[a -b]` was an error, `[h *t]` spread and
`h * t` multiplied, `f(a |x| x)` opened a lambda and `a | b` was an or, and
`a- b` was refused as lopsided. Those rules existed for about one line in
200 (Faun had 11 lambdas after another argument and 9 negated elements),
yet a respacing formatter or generator could change what a program meant.

With commas the token before an operator says what it is: after an operand
it is infix, after `,` or an opening bracket it is a prefix, a rest or a
lambda. The lexer lost its spacing tests on `-`, `*` and `|`, and a
tree-sitter grammar needs no spacing-sensitive tokens. Spacing is still
checked where it would mislead, `x -3` or `a *b`, but only to refuse, never
to choose a reading.

### Why may every sequence end with a comma?

So a list written one element per line changes one line when an element is
added or moved, as it did without commas. The policies considered:
forbidding it (Haskell, JSON) costs two-line diffs and drives programmers
to leading commas; requiring it on multi-line sequences (Go) is there for
semicolon insertion, which Faun lacks; letting a newline stand for a comma
(F#) puts layout back in the grammar and makes `f(a\n- b)` ambiguous again.
Allowing it everywhere is one rule, and costs the grammar one LL(1) check:
after `,`, stop if the next token closes the bracket. A formatter writes
one exactly when the closing bracket is on its own line.

The cost is spellings nobody writes, such as `|a, b,|`, and two spellings
of every one-line sequence until a formatter picks one. A `where` list's
last constraint takes none.

### Why does a signature parenthesize its parameters?

`add : (Nat, Nat) -> Nat` reads as the clause head `add(a, b)` below it,
as the function types of Rust and TypeScript do, and means the same in a
signature as in a parameter. The other spelling, `add : Nat, Nat -> Nat`,
makes a function-typed parameter `(a, b -> c)`, which looks like a tuple of
`a` and `b -> c`. Closing the parameter list also lets a `where` bound take
comma-separated constraints without ambiguity.

The cost is two characters in a multi-parameter signature, and doubled
parentheses for a tuple-typed parameter, `((Nat, Nat)) -> Nat`, as in Rust.

### Why is `(a,)` an error?

In Python `(a,)` is a tuple and `(a)` is not, a well-known trap. Faun's
tuples have two or more members, so a one-member tuple has no use, and
`(a,)` is refused rather than read as either a tuple or a grouping.

### Why must a call's `(` touch what it calls?

With commas two operands are never side by side, so `f (x)` could be a
call, as in Rust or Python. Keeping calls tight costs one check, keeps
`f(x)` recognisable at a glance, and stops a list element split across
lines, `[f\n(x)]`, from being read as a call.

### Why not optional commas?

Clojure treats commas as whitespace, which would let clause tables stay
bare. But wherever a comma is left out every spacing rule above still
applies, so the lexer would keep all of them, and a formatter must choose a
house style anyway. The parsing and tooling gains depend on commas being
required.

### Why not whitespace with parenthesized compound elements?

Peers could stay space-separated, with an element containing an infix
operator parenthesized in a sequence of two or more: `gcd(b (a % b))`. This
is Haskell's rule for application carried into argument lists. It changes
only 3–5% of lines (mean 40.2 columns in Ori, 324 lines over 80) and fixes
compound arguments. But records still read as `x: (n y): …`, and spacing
matters more, not less: `f(a (b + 1))` and `f(a(b + 1))` are two arguments
against one nested call, told apart by a space. The lexer keeps every rule
it had and gains a diagnostic, and the syntax is as unusual as whitespace
plus a rule to learn.

### Why not Haskell's split?

Haskell uses juxtaposition where the form is application (calls, clause
patterns, type application) and commas where it is data (tuples, lists,
records, imports), and pays with parentheses around compound arguments and
`$` to avoid them. A Faun shaped that way, commas in data and parenthesized
compound elements in calls and clause heads, changed 17% of Ori lines and
kept heads and signatures bare, where commas cost most. It was rejected for
its two separator rules: `f(a b)` beside `(a, b)`. Elm follows Haskell;
OCaml and F# use juxtaposition, `,` for tuples and `;` for lists; Nix's
`[ f x ]` is two elements, the closest analogue to whitespace Faun's
`[a - 1 b]`. Rust, Swift, Kotlin, Gleam, Roc, Python and JavaScript use
commas throughout.

## History

- **Before 2026-09-26:** Faun began as a port of Ori and took its
  whitespace-separated syntax, `f(a b)`, `[h *t]`, `{x: 1 y: 2}` and
  `add : Nat Nat -> Nat`, with spacing deciding `-`, `*` and `|`.
- **2026-09-26:** commas were proposed, measured on both corpora, approved
  and built the same day: every sequence takes them and a trailing one, a
  signature parenthesizes its parameters, and spacing stopped deciding what
  `-`, `*` and `|` are. Ori examples no longer parse as Faun; a converter
  built from the old lexer, inserting a comma wherever an element begins
  after another, was recommended and not built.
- **2026-10-09:** a prefix `-` or `!`, and then a rest's `*`, must touch
  what they take, and an infix operator is spaced alike on both sides, so
  `x -3`, `[a, * rest]` and `a *b` are refused instead of read one way.
  A pattern's `==` followed on 2026-10-11.

## Related

- [Tuples](../values/tuples.md): two members or more
- [Types](../types.md): signatures and `where` bounds
- [Pattern matching](pattern-matching.md): clause heads
