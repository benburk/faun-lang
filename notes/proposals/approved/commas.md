# Proposal: Commas Between Elements

- **Status:** Approved
- **Author:** cullback
- **Created:** 2026-09-26
- **Approved:** 2026-09-26
- **Affects:** the lexer, `grammar.ebnf`, the parser, diagnostics, `to_str`,
  the tree-sitter grammar, every program

---

## Summary

Separate peers with commas, as most languages do, instead of with
whitespace, as Ori does. Every sequence between delimiters takes them, and
may end with one. A signature parenthesizes its parameters. Spacing no
longer decides what `-`, `*` or `|` is.

| Form                          | Before             | After                |
| ----------------------------- | ------------------ | -------------------- |
| Call, constructor arguments   | `f(a b)`           | `f(a, b)`            |
| Clause-head patterns          | `f([x *xt] ys) ->` | `f([x, *xt], ys) ->` |
| Lambda parameters             | `\|acc x\|`        | `\|acc, x\|`         |
| Tuples, tuple patterns        | `(a b)`            | `(a, b)`             |
| Lists, list patterns          | `[a b *rest]`      | `[a, b, *rest]`      |
| Records, record patterns      | `{x: 1 y: 2}`      | `{x: 1, y: 2}`       |
| Record punning                | `{left top}`       | `{left, top}`        |
| Type arguments                | `Result(Nat Str)`  | `Result(Nat, Str)`   |
| Signature parameters          | `Nat Nat -> Nat`   | `(Nat, Nat) -> Nat`  |
| Function types                | `(a b -> c)`       | `((a, b) -> c)`      |
| Tuple types                   | `(Nat Nat)`        | `(Nat, Nat)`         |
| Record types                  | `{x: Nat y: Nat}`  | `{x: Nat, y: Nat}`   |
| Tag rows                      | `[Missing Bad]`    | `[Missing, Bad]`     |
| Alias constraints             | `where Name(a b)`  | `where Name(a, b)`   |
| `import`, `export`, `package` | `{List Str.*}`     | `{List, Str.*}`      |

Unaffected: method blocks `.( … )` (one item per line), bindings, method
chains, operators, and string splices.

The measurements and examples below describe the whitespace syntax Faun had
when this was written, and Ori still has.

## Motivation

- **Weirdness budget.** Whitespace-separated arguments are the first thing a
  reader notices, and the easiest thing to argue about. Every discussion of
  Faun would begin there instead of with totality, effects, or in-place
  reuse. Commas are the choice nobody argues about. Roc recently moved from
  whitespace application to `f(a, b)` calls for much the same reason.
- **Compound arguments become readable.** This is the largest real
  readability gain. Without commas, the reader has to know precedence just to
  count arguments:

  ```ruby
  lower(r * 10 s mp * 10 mm * 10 k - 1 closed fuel digits)
  lower(r * 10, s, mp * 10, mm * 10, k - 1, closed, fuel, digits)
  ```

  About 2–3% of lines have such an argument (`crates/faun/standard/float/format.fn`
  is dense with them), but they are exactly the lines that are hard to read.
- **Records read as records.** `{x: n y: n.add(n)}` scans as `x: (n y): …` until
  the eye finds the colons. So does `{left: Nat top: Nat right: Nat bottom: Nat}`
  in `aoc/201506.ori`.
- **Editor motions work out of the box.** targets.vim's `cia`/`daa` and mini.ai's
  argument text object split on commas, and they work in any language before
  a tree-sitter grammar exists. Without commas, `ciw` works for simple arguments
  but not for `mp * 10`, and `ciW` swallows `f(`. Tree-sitter's
  `@parameter.inner` works either way, but only once Faun has a grammar and
  queries. `f,` and `;` jumping between arguments also comes for free.
- **Spacing stops mattering.** `f(a, -b)`, `f(a, *rest)` and `f(a, |x| x)` read
  the same however they are spaced. The `Lopsided` and `NegatedElement` errors
  disappear. Formatters and generated code can't change meaning by respacing.
- **Hand-written and pasted code.** Readers trained on C, Rust, Python and JSON
  see `f(a b)` as a missing comma. JSON and Python pasted into a test fails
  today with `invalid token ','`. LLMs trained on comma languages will keep
  inserting commas. `notes/ai-future.md` puts humans first, and this helps
  both.

Whitespace separation also shapes the lexer (`crates/faun/src/lex.rs`).
Because a space is the separator, spacing has to settle what several glyphs
mean:

- `f(x)` is a call and `f (x)` is two peers (`CallParen`, `Adjacent`).
- `a - b` subtracts and `[a -b]` is an error (`Negate`, `Minus`, `NegatedElement`).
- `a- b` is an error (`Lopsided`).
- `[h *t]` spreads and `h * t` multiplies (`Rest`, `Star`).
- `f(a |x| x)` opens a lambda and `a | b` is an or (`LambdaBar`, `Bar`).

With commas, the token after `,` or an opening bracket always begins an
element, so `-`, `*` and `|` can be read without looking at spacing, and a
formatter can respace freely. Only the call adjacency is worth keeping.

These are the hardest lines to read today, and commas help each:

```ruby
# crates/faun/standard/float/format.fn — compound arguments
raise(r s * 10 mp mm k + 1 closed fuel digits)
reaches(rest + mp * 10 s closed)

# ori examples/records.ori, aoc/201506.ori — records and record types
p = {x: n y: n.add(n)}
inside : Nat Nat {left: Nat top: Nat right: Nat bottom: Nat} -> Bool

# aoc/201507.ori — a lambda after another argument
wiring.len().times(Map.empty() |signals| sweep(wiring signals))

# a signature with nested types
read : Reads(a) (Input -> Result(Read(b) ParserError)) -> Result(Reads((a b)) ParserError)

# the standard README's bound: where do the constraints split?
sum : List(a) -> a where a.zero : a a.add : a a -> a
```

## Design

Commas are required in every sequence the grammar writes between
delimiters. The change forced five decisions.

### Trailing commas

Every comma-separated sequence has to say whether `[a, b,]` is allowed. Four
policies are common:

- **Forbidden** (Haskell, JSON, SQL): one spelling, but adding an element to a
  vertical list edits two lines, and reordering lines breaks the last one.
  Haskell programmers answer with leading commas, `, b`, to get the diffs back.
- **Allowed** (Rust, Python, JavaScript, Swift): both spellings parse; a
  formatter picks one.
- **Required on multi-line sequences** (Go): Go enforces it in the grammar
  because semicolon insertion would otherwise end the line.
- **Newline as a separator** inside brackets (F# lists and records): keeps
  clean vertical lists, but puts layout back in the grammar, and `f(a\n- b)`
  becomes ambiguous again.

Decided: a trailing comma is allowed in every sequence, the same rule
everywhere, and a formatter writes one exactly when the closing bracket is on
its own line. Then a vertical list changes one line per element, as it did
without commas, and a one-line list has none. The grammar cost is one check:
after `,`, stop if the next token closes the bracket. That is still LL(1).

The edge cases:

- **One-element tuples.** In Python, `(a,)` is a tuple and `(a)` is not, a
  well-known trap. Faun's tuples have two or more members, so `(a,)` is an
  error ("a tuple has at least two members"), not a tuple or a grouping.
- **Empty sequences.** `f()`, `[]` and `{}` stay as they are; `f(,)` is an
  error.
- **After a rest.** Rust forbids a comma after `..` in struct patterns. Faun
  allows `[h, *t,]` for uniformity. A rest still has to come last.
- **Lambda parameters.** `|a, b,|` is legal under the uniform rule and never
  written by a formatter.

Vertical declarations are where this shows. Ori's `Json` row becomes:

```ruby
Json : [
  Null,
  Bool(Bool),
  Number(Int),
  String(Str),
  Array(List(Json)),
  Object(List((Str, Json))),
].(
```

About 360 separators in the Ori corpus fall across lines like this. Each
multi-line sequence also gains a trailing comma.

### Signature syntax

`add : Nat Nat -> Nat` has two natural comma spellings:

- **`add : Nat, Nat -> Nat`** keeps the old shape. But a parameter of function
  type reads as `(a, b -> c)`, which looks like a tuple of `a` and `b -> c`.
- **`add : (Nat, Nat) -> Nat`** mirrors the clause head `add(a, b)` and the
  function types of Rust and TypeScript. A one-parameter signature may drop
  the parentheses, `fib : Nat -> Nat`. The cost is a tuple-typed parameter,
  which needs its own parentheses, `((Nat, Nat)) -> Nat`, as in Rust, and two
  more characters in multi-parameter signatures.

Decided: the parenthesized form. It means the same thing in a signature and
in a parameter, it lines up with the clause heads below it, and it closes the
parameter list, so a `where` bound could later take comma-separated
constraints on one line (`where a.zero : a, a.add : (a, a) -> a`) without
ambiguity. Each member constraint is on its own line for now, which works
either way. A signature is a type: `(A, B) -> R`, `A -> R`, or the result
alone for a nullary definition. A function-typed parameter is written bare
in the list, `(List(a), a -> b) -> List(b)`.

### Required or optional commas

Clojure's rule, commas as whitespace, would let clause tables stay bare. But
wherever a comma is left out, every spacing rule above still applies, so the
lexer would keep all of them, and a formatter must choose a house style
anyway. Decided: required. The parsing and tooling gains depend on it.

### `f (x)`

With commas, two operands are never legitimately side by side, so `f (x)`
could be read as a call, as in Rust or Python. Decided: calls stay tight, and
`f (x)` is an error. It costs one check, keeps `f(x)` recognisable at a
glance, and avoids a list element split across lines being read as a call
(`[f\n(x)]`).

### Ori compatibility

Faun runs Ori examples through `faun test` to choose what to build next. Ori
keeps whitespace, so its examples no longer parse as Faun. Recommended, and
not built: a one-off converter built from the old lexer, which already finds
every element boundary. It would insert a comma wherever an element begins
after another (the rule the measurements used), so porting an Ori example
stays mechanical.

## Costs

- **Length.** About 3% on average and 4.5% on clause lines, concentrated in
  the wide lines: over-80 lines +32% (Ori), over-100 lines ×2 (Faun).
- **Pattern clause groups lose their look.** A group like
  `merge([x *xt] [y *yt]) if x <= y -> …` reads like a table, close to the
  notation on paper. Commas add noise exactly where the patterns are richest,
  and a column of wildcards becomes `_, _, _, _,`.
- **Signatures needed a decision**, above, and a tuple-typed parameter now
  needs doubled parentheses.
- **Trailing commas needed a policy**, above. Whitespace got one-line diffs
  for free, with one separator rule.
- **Churn.** Every file changes, along with the grammar, the lexer, the
  diagnostics, the formatter, and the port from Ori, which keeps its syntax.
  Ori examples no longer run through `faun test` without being converted.

### Measurements

A heuristic tokenizer ran over `../ori-lang` `examples/`, `demos/`,
`benchmarks/` and `standard/` (151 files, 7,698 code lines), and over Faun's
`crates/faun` `.fn` files (41 files, 2,731 code lines). It counts peer
boundaries per line. Each comma adds one column (`a b` becomes `a, b`), and
each parenthesized element under option C adds two. It isn't a parser, so
treat the numbers as ±5%.

Where the separators fall:

| Context              |        Ori |      Faun |
| -------------------- | ---------: | --------: |
| Clause-head patterns |      3,017 |     1,686 |
| Call arguments       |      2,388 |       846 |
| Lists                |      1,361 |       295 |
| Signature parameters |      1,271 |       702 |
| Type arguments       |        523 |       151 |
| Tuples               |        401 |        82 |
| Records              |        369 |        62 |
| Imports and exports  |        229 |        98 |
| Tuple types          |        220 |        37 |
| Tag rows             |        191 |        81 |
| Record types         |        102 |        13 |
| **Total**            | **10,072** | **4,053** |

Clause heads and signatures take 43% of the commas in Ori and 59% in Faun,
whose corpus is mostly the standard library. Pattern-matching code pays the
most.

What each option costs in line length (A is whitespace, B commas, C atomic
elements; see [Alternatives considered](#alternatives-considered)):

|                        | Ori A | Ori B | Ori C | Faun A | Faun B | Faun C |
| ---------------------- | ----: | ----: | ----: | -----: | -----: | -----: |
| Mean line length       |  40.1 |  41.3 |  40.2 |   39.1 |   40.6 |   39.2 |
| Lines changed          |     — |   53% |    3% |      — |    58% |     5% |
| Lines over 80 columns  |   315 |   417 |   324 |    145 |    183 |    149 |
| Lines over 100 columns |    57 |    78 |    59 |     18 |     37 |     22 |

By kind of line, with commas:

| Kind (Ori)         | Lines | Mean length |  Added by B |
| ------------------ | ----: | ----------: | ----------: |
| Clause (`f(…) ->`) | 2,931 |        45.2 | +1.6 (3.5%) |
| Signature          | 1,771 |        35.6 |        +1.2 |
| `expect`           |   751 |        47.8 |        +0.9 |
| Other              | 2,245 |        34.4 |        +1.0 |

In Faun, clause lines gain 1.9 columns on a 42.3 mean (4.5%).

The average line doesn't feel it. The long tail does: a third more lines
cross 80 columns, and in Faun twice as many cross 100. The worst cases are
argument-heavy lines, which gain 8 to 20 columns:

```ruby
step(digit _ _ _ _ _ _ False True) -> [digit + 1]
step(digit, _, _, _, _, _, _, False, True) -> [digit + 1]

expect [5 3 9 1 5 6 2 8 7 4 0].sort() == [0 1 2 3 4 5 5 6 7 8 9]
expect [5, 3, 9, 1, 5, 6, 2, 8, 7, 4, 0].sort() == [0, 1, 2, 3, 4, 5, 5, 6, 7, 8, 9]
```

The spacing-sensitive forms are rare. Ori has 34 lambdas written after another
argument and 9 negated elements such as `f(a -1)`; Faun has 11 and 9. Most of
the lexer's spacing rules exist for about one line in 200.

These were the cleanest lines, and commas hurt each:

```ruby
# patterns.ori — clause heads of plain names and small patterns
merge([x *xt] [y *yt]) if x <= y -> [x *merge(xt [y *yt])]
merge([x, *xt], [y, *yt]) if x <= y -> [x, *merge(xt, [y, *yt])]

# format.fn — wildcard rows
step(digit _ _ _ _ _ _ True False) -> [digit]
step(digit, _, _, _, _, _, _, True, False) -> [digit]

# aoc/201506.ori — string-and-name list patterns
instruction(["turn" "on" start "through" end]) -> parse_range(TurnOn start end)
instruction(["turn", "on", start, "through", end]) -> parse_range(TurnOn, start, end)

# list.fn — nested data in expects
expect [(2 1) (1 1) (2 0) (1 0)].sort_on(|(key _)| key) == [(1 1) (1 0) (2 1) (2 0)]
expect [(2, 1), (1, 1), (2, 0), (1, 0)].sort_on(|(key, _)| key) == [(1, 1), (1, 0), (2, 1), (2, 0)]
```

Short, plain elements (names, `_`, literals, small patterns) read better
without commas. Anything with an operator, a colon, or a nested call reads
better with them. Much of the Ori corpus is the first kind. Much of the
standard library's numeric code is the second.

## Alternatives considered

- **A. Whitespace**, as Faun had and Ori has: `f(a b)`, `[a b]`,
  `{x: 1 y: 2}`. Densest, with one separator rule everywhere, and clause
  groups read as tables. But compound arguments and records ask the reader to
  parse precedence to count elements, and spacing decides meaning:
  `lower(1 2 3 4 -1 0)` depends on `-1` being tight, while `4 - 1` would
  silently mean one argument.
- **C. Whitespace, with atomic elements:** peers stay space-separated, but in
  a sequence of two or more, an element containing an infix operator must be
  parenthesized: `gcd(b (a % b))`, not `gcd(b a % b)`. Only 3–5% of lines
  change, and the compound-argument problem is fixed. This is Haskell's rule
  for application, carried into delimited argument lists. Rejected: records
  still read as `x: (n y): …` and would need a rule of their own; spacing
  matters more, not less (`f(a (b + 1))` against `f(a(b + 1))` is two
  arguments against one nested call, told apart by a single space); the lexer
  keeps every rule it has and gains a diagnostic; and C is as unusual as A,
  plus a paren rule to learn.
- **Haskell's split:** juxtaposition where the form is application (`f a b`,
  clause patterns, type application, constructor fields), commas where it is
  data (tuples, lists, records, imports, contexts). Haskell pays with
  parentheses around any compound argument, `f (x + 1) (g y)`, and has `$`
  and `.` to avoid them. Faun's call parentheses already delimit arguments,
  and it allows infix operators inside them, which Haskell does not. A
  Haskell-shaped Faun would put commas in data and use C's parentheses in
  calls and clause heads. Measured on Ori, it changes 17% of lines and
  averages 40.4 columns (over-80 lines 315 → 346), and keeps clause heads and
  signatures bare, where commas cost the most. Rejected for its two separator
  rules: calls and data would look different, `f(a b)` next to `(a, b)`.
- **Optional commas**, as Clojure treats them as whitespace: `[1, 2, 3]` and
  `[1 2 3]` the same. Rejected under [Required or optional commas](#required-or-optional-commas).

Other precedents: Elm follows Haskell's split. OCaml and F# use juxtaposition
for application, `,` for tuples, and `;` for lists and records; F# lets
newlines stand for `;`. Nix separates list elements by space and applies
functions by juxtaposition, so `[ f x ]` is two elements, a well-known trap
and the closest analogue to A's `[a - 1 b]`. Rust, Swift, Kotlin, Gleam,
Roc, Python and JavaScript use commas throughout.

### The three options side by side

One program assembled from the excerpts above (`patterns.ori`, `format.fn`,
`aoc/201506.ori`, `aoc/201507.ori`, `list.fn`).

A, whitespace:

```ruby
export {Area merge lower}

Area = {left: Nat top: Nat right: Nat bottom: Nat}

merge : List(Nat) List(Nat) -> List(Nat)
merge([] ys) -> ys
merge(xs []) -> xs
merge([x *xt] [y *yt]) if x <= y -> [x *merge(xt [y *yt])]
merge([x *xt] [y *yt]) -> [y *merge([x *xt] yt)]

step : Nat Nat Nat Bool Bool -> List(Nat)
step(digit rest s False False) -> [digit *generate(rest s)]
step(digit _ _ False True) -> [digit + 1]
step(digit _ _ True False) -> [digit]
step(digit rest s True True) -> (rest * 2 < s).select([digit] [digit + 1])

lower : Nat Nat Nat Nat Int Nat -> (List(Nat) Int)
lower(r s mp mm k Succ(fuel)) if reaches((r + mp) * 10 s).not() ->
  lower(r * 10 s mp * 10 mm * 10 k - 1 fuel)
lower(r s mp mm k _) -> (generate(r s) k)

inside : Nat Nat Area -> Bool
inside(x y area) -> area.left <= x & x <= area.right

lit : List(Instruction) Bool -> Bool
lit(instructions start) -> instructions.fold(start |light Instruction(action _)| apply(light action))

expect [(2 1) (1 1)].sort_on(|(key _)| key) == [(1 1) (2 1)]
expect merge([1 4] [2 3]) == [1 2 3 4]
expect lower(1 2 3 4 -1 0) == ([] -1)
```

B, commas, as decided:

```ruby
export {Area, merge, lower}

Area = {left: Nat, top: Nat, right: Nat, bottom: Nat}

merge : (List(Nat), List(Nat)) -> List(Nat)
merge([], ys) -> ys
merge(xs, []) -> xs
merge([x, *xt], [y, *yt]) if x <= y -> [x, *merge(xt, [y, *yt])]
merge([x, *xt], [y, *yt]) -> [y, *merge([x, *xt], yt)]

step : (Nat, Nat, Nat, Bool, Bool) -> List(Nat)
step(digit, rest, s, False, False) -> [digit, *generate(rest, s)]
step(digit, _, _, False, True) -> [digit + 1]
step(digit, _, _, True, False) -> [digit]
step(digit, rest, s, True, True) -> (rest * 2 < s).select([digit], [digit + 1])

lower : (Nat, Nat, Nat, Nat, Int, Nat) -> (List(Nat), Int)
lower(r, s, mp, mm, k, Succ(fuel)) if reaches((r + mp) * 10, s).not() ->
  lower(r * 10, s, mp * 10, mm * 10, k - 1, fuel)
lower(r, s, mp, mm, k, _) -> (generate(r, s), k)

inside : (Nat, Nat, Area) -> Bool
inside(x, y, area) -> area.left <= x & x <= area.right

lit : (List(Instruction), Bool) -> Bool
lit(instructions, start) -> instructions.fold(start, |light, Instruction(action, _)| apply(light, action))

expect [(2, 1), (1, 1)].sort_on(|(key, _)| key) == [(1, 1), (2, 1)]
expect merge([1, 4], [2, 3]) == [1, 2, 3, 4]
expect lower(1, 2, 3, 4, -1, 0) == ([], -1)
```

Familiar at a glance: `lower`, `Area` and `lit` become the easiest lines to
read, and `merge` and `step` the hardest. `-1`, `*xt` and `|light …|` mean
the same however they are spaced.

C, atomic elements, differs from A only in the two `lower` lines, which is
the point:

```ruby
lower(r s mp mm k Succ(fuel)) if reaches(((r + mp) * 10) s).not() ->
  lower((r * 10) s (mp * 10) (mm * 10) (k - 1) fuel)
```

## Implementation impact

Commas change little in the parser and more in the lexer and other tools.

- **The parser barely changes.** The grammar is LL(1) either way, and it never
  sees spacing: the lexer classifies tokens first. Each sequence rule gains
  `","` and an optional trailing comma, which makes the grammar a few symbols
  longer, not shorter.
- **The lexer gets simpler.** Before, `classify` read the space on both sides
  of an operator to decide what it is. With commas, the token before it is
  enough, as in any C-style expression parser: after an operand, `-`
  subtracts, `*` multiplies and `|` is an or; after `,` or an opening bracket
  they negate, spread and open a lambda. That removes the spacing tests on
  `-`, `*` and `|`, and `closes_next`, which looked past space for a closing
  bracket to read `[_ *]`; the token kinds `Lopsided` and `NegatedElement`,
  which existed only to be reported; and `Adjacent`, since two operands side
  by side are an ordinary "expected `,`" error. What stays is the newline
  logic, the rule that `.`, `..` and `?` sit against what they join, and call
  adjacency.
- **Diagnostics improve.** Before, a dropped operator was often not a syntax
  error: `f(a + b)` without its `+` is `f(a b)`, two arguments, and the
  mistake surfaced later as an arity or type error. With commas, `f(a b)`
  fails in the parser, at the gap, with "expected `,`". A comma is also a
  place to resume after an error inside a long list.
- **Tools gain the most.** A tree-sitter grammar for whitespace syntax needs
  spacing-sensitive tokens to tell `f(a -b)` from `f(a - b)`. With commas, an
  ordinary whitespace-insensitive grammar with precedences is enough, and a
  formatter can respace freely.

What changed:

- The lexer reads `,` and no longer decides `-`, `*` or `|` by spacing: the
  grammar tells a prefix from an infix by where it stands. `Negate`, `Rest`,
  `LambdaBar`, `Lopsided`, `NegatedElement` and `Adjacent` are gone, and
  tokens no longer carry their spacing. Only call adjacency (`f(x)`) and the
  joins `.`, `..`, `.*` and `?` still look at space.
- Every sequence takes an optional trailing comma. A rest comes last, and may
  be followed by one.
- A signature is a type, as under [Signature syntax](#signature-syntax).
- `(a,)` is refused: a tuple has at least two members.
- `to_str` writes lists and tags with commas, `[1, 2, 3]` and `P(1, 2)`, and
  diagnostics print types and patterns the same way.
- Ori examples no longer parse as Faun without their commas.

## Testing

- `the_grammar_reads_and_refuses_commas_as_the_parser_does`
  (`crates/faun/src/ebnf.rs`) holds `grammar.ebnf` to the parser on trailing
  commas, a rest's place, `(,)`, and signatures with and without their
  parentheses.
- Every program in the repository is read by both, and by the tree-sitter
  grammar, in `just test`.

## Origin

Faun began as a port of Ori and took its whitespace-separated syntax. This
asked whether that should stay, measured what a change would cost on both
corpora, and compared the three options above.
