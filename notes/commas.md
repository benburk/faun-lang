# Commas

**Status: adopted.** Faun now separates with commas (option B), with the
decisions under [Decisions commas would bring](#decisions-commas-would-bring).
The measurements and examples below describe the whitespace syntax Faun had
when this was written, and Ori still has.

Should Faun separate peers with commas, as most languages do, instead of with
whitespace, as Ori does? This note lists the syntax a change would touch, measures
what it would cost on the Ori and Faun corpora, and compares three options:

- **A. Whitespace (today):** `f(a b)`, `[a b]`, `{x: 1 y: 2}`.
- **B. Commas:** `f(a, b)`, `[a, b]`, `{x: 1, y: 2}`.
- **C. Whitespace, with atomic elements:** peers stay space-separated, but in a
  sequence of two or more, an element containing an infix operator must be
  parenthesized: `gcd(b (a % b))`, not `gcd(b a % b)`.

## Verdict

B costs about one character per line on average. It removes the most unusual
thing a newcomer notices, fixes the hardest-to-read code in the corpus, and lets
the lexer drop most of its spacing rules. What it gives up is the terse,
table-like look of pattern-heavy clause groups. I'd adopt B unless that look is
something Faun is meant to be known for. C is cheap too, but it keeps the
unusual syntax and makes spacing matter even more.

## What syntax is affected

Every sequence the grammar writes as `{ x }` between delimiters
(`crates/faun/src/grammar.ebnf`):

| Form                           | Today              | With commas          |
| ------------------------------ | ------------------ | -------------------- |
| Call, constructor arguments    | `f(a b)`           | `f(a, b)`            |
| Clause-head patterns           | `f([x *xt] ys) ->` | `f([x, *xt], ys) ->` |
| Lambda parameters              | `\|acc x\|`        | `\|acc, x\|`         |
| Tuples, tuple patterns         | `(a b)`            | `(a, b)`             |
| Lists, list patterns           | `[a b *rest]`      | `[a, b, *rest]`      |
| Records, record patterns       | `{x: 1 y: 2}`      | `{x: 1, y: 2}`       |
| Record punning                 | `{left top}`       | `{left, top}`        |
| Type arguments                 | `Result(Nat Str)`  | `Result(Nat, Str)`   |
| Signature parameters           | `Nat Nat -> Nat`   | `(Nat, Nat) -> Nat`  |
| Function types                 | `(a b -> c)`       | `((a, b) -> c)`      |
| Tuple types                    | `(Nat Nat)`        | `(Nat, Nat)`         |
| Record types                   | `{x: Nat y: Nat}`  | `{x: Nat, y: Nat}`   |
| Tag rows                       | `[Missing Bad]`    | `[Missing, Bad]`     |
| Alias constraints              | `where Name(a b)`  | `where Name(a, b)`   |
| `import`, `exports`, `package` | `{List Str.*}`     | `{List, Str.*}`      |

Unaffected: method blocks `.( … )` (one item per line), bindings, method chains,
operators, and string splices.

Whitespace separation also shapes the lexer (`crates/faun/src/lex.rs`). Because
a space is the separator, spacing has to settle what several glyphs mean:

- `f(x)` is a call and `f (x)` is two peers (`CallParen`, `Adjacent`).
- `a - b` subtracts and `[a -b]` is an error (`Negate`, `Minus`, `NegatedElement`).
- `a- b` is an error (`Lopsided`).
- `[h *t]` spreads and `h * t` multiplies (`Rest`, `Star`).
- `f(a |x| x)` opens a lambda and `a | b` is an or (`LambdaBar`, `Bar`).

With commas, the token after `,` or an opening bracket always begins an element,
so `-`, `*` and `|` could be read without looking at spacing, and a formatter
could respace freely. Only the call adjacency is worth keeping.

## Measurements

I ran a heuristic tokenizer over `../ori-lang` `examples/`, `demos/`, `benchmarks/`
and `standard/` (151 files, 7,698 code lines), and over Faun's `crates/faun`
`.fn` files (41 files, 2,731 code lines). It counts peer boundaries per line.
Each comma adds one column (`a b` becomes `a, b`), and each parenthesized
element under C adds two. It isn't a parser, so treat the numbers as ±5%.

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

Clause heads and signatures take 43% of the commas in Ori and 59% in Faun, whose
corpus is mostly the standard library. So the hunch is right: pattern-matching
code pays the most.

What each option costs in line length:

|                        | Ori A | Ori B | Ori C | Faun A | Faun B | Faun C |
| ---------------------- | ----: | ----: | ----: | -----: | -----: | -----: |
| Mean line length       |  40.1 |  41.3 |  40.2 |   39.1 |   40.6 |   39.2 |
| Lines changed          |     — |   53% |    3% |      — |    58% |     5% |
| Lines over 80 columns  |   315 |   417 |   324 |    145 |    183 |    149 |
| Lines over 100 columns |    57 |    78 |    59 |     18 |     37 |     22 |

By kind of line, under B:

| Kind (Ori)         | Lines | Mean length |  Added by B |
| ------------------ | ----: | ----------: | ----------: |
| Clause (`f(…) ->`) | 2,931 |        45.2 | +1.6 (3.5%) |
| Signature          | 1,771 |        35.6 |        +1.2 |
| `expect`           |   751 |        47.8 |        +0.9 |
| Other              | 2,245 |        34.4 |        +1.0 |

In Faun, clause lines gain 1.9 columns on a 42.3 mean (4.5%).

So B makes the average line about 3% longer, and clause lines up to 4.5%
longer. The average line doesn't feel it. The long tail does: a third more
lines cross 80 columns, and in Faun twice as many cross 100. The worst cases
are argument-heavy lines, which gain 8 to 20 columns:

```ruby
step(digit _ _ _ _ _ _ False True) -> [digit + 1]
step(digit, _, _, _, _, _, _, False, True) -> [digit + 1]

expect [5 3 9 1 5 6 2 8 7 4 0].sort() == [0 1 2 3 4 5 5 6 7 8 9]
expect [5, 3, 9, 1, 5, 6, 2, 8, 7, 4, 0].sort() == [0, 1, 2, 3, 4, 5, 5, 6, 7, 8, 9]
```

The spacing-sensitive forms are rare. Ori has 34 lambdas written after another
argument and 9 negated elements such as `f(a -1)`; Faun has 11 and 9. Most of
the lexer's spacing rules exist for about one line in 200.

## Pros and cons of commas

For commas:

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

Against commas:

- **Length.** About 3% on average and 4.5% on clause lines, concentrated in the
  wide lines: over-80 lines +32% (Ori), over-100 lines ×2 (Faun).
- **Pattern clause groups lose their look.** A group like
  `merge([x *xt] [y *yt]) if x <= y -> …` reads like a table, close to the
  notation on paper. Commas add noise exactly where the patterns are richest,
  and a column of wildcards becomes `_, _, _, _,`.
- **Signatures need a decision.** `Nat Nat -> Nat` reads well without commas.
  `Nat, Nat -> Nat` is unusual, and `(Nat, Nat) -> Nat` makes a tuple-typed
  parameter need doubled parentheses (see
  [Signature syntax](#signature-syntax)).
- **Trailing commas.** Multi-line lists, rows, and records need a trailing-comma
  policy so a new element changes one line in a diff. Whitespace gets this for
  free, and the separator rule stays one rule.
- **Churn.** Every file changes, along with the grammar, the lexer, the
  diagnostics, the formatter, and the port from Ori, which keeps its syntax. Ori
  examples would no longer run through `faun test` without being rewritten.

## Parsing

Commas change little in the parser and more in the lexer and in other tools.

**The parser barely changes.** The grammar is LL(1) either way, and it never
sees spacing: the lexer classifies tokens first. Each sequence rule gains
`","` and an optional trailing comma (`{ x "," } [ x ]`), which makes the
grammar a few symbols longer, not shorter.

**The lexer gets simpler.** Today `classify` (`crates/faun/src/lex.rs`) reads
the space on both sides of an operator to decide what it is. With commas, the
token before it is enough, as in any C-style expression parser: after an
operand, `-` subtracts, `*` multiplies and `|` is an or; after `,` or an
opening bracket they negate, spread and open a lambda. That removes:

- the spacing tests on `-`, `*` and `|`, and `closes_next`, which looks past
  space for a closing bracket to read `[_ *]`;
- two token kinds that exist only to be reported, `Lopsided` and
  `NegatedElement`, and their messages in `grammar.rs`;
- `Adjacent` as a separate idea: two operands side by side become an ordinary
  "expected `,`" error.

What stays is the newline logic (a line ends outside brackets, and a leading
`.` continues a chain), the rule that `.`, `..` and `?` sit against what they
join, and, if it is kept, call adjacency (`f(x)` against `f (x)`). Nothing
outside the lexer reads `space_before` today, which is why the parser proper
is unaffected. The saving is about a dozen lines of `classify` and two error
kinds. What matters more is that spacing stops changing meaning.

**Diagnostics improve.** Today a dropped operator is often not a syntax
error: `f(a + b)` without its `+` is `f(a b)`, two arguments, and the mistake
surfaces later as an arity or type error. With commas, `f(a b)` fails in the
parser, at the gap, with "expected `,`". A comma is also a place to resume
after an error inside a long list.

**Tools gain the most.** A tree-sitter grammar for today's syntax needs
spacing-sensitive tokens (`token.immediate`, or an external scanner) to tell
`f(a -b)` from `f(a - b)` and `f(x)` from `f (x)`, and a formatter must
preserve spacing it doesn't understand. With commas, an ordinary
whitespace-insensitive grammar with precedences is enough, and a formatter can
respace freely.

## Examples, helped and hurt

Helped by commas (currently the hardest lines to read):

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

Hurt by commas (currently the cleanest lines):

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

## The three options side by side

One program assembled from the excerpts above (`patterns.ori`, `format.fn`,
`aoc/201506.ori`, `aoc/201507.ori`, `list.fn`).

### A. Whitespace (today)

```ruby
exports {Area merge lower}

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

- Densest and most uniform: one separator rule everywhere.
- Clause groups read as tables.
- `lower(r * 10 s mp * 10 …)` and the `Area` record ask the reader to parse
  precedence to count fields.
- `lower(1 2 3 4 -1 0)` depends on `-1` being tight, while `4 - 1` would silently
  mean one argument.

### B. Commas

```ruby
exports {Area, merge, lower}

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

- Familiar at a glance, and nothing in it would make a reader stop to ask.
- `lower`, `Area` and `lit` are now the easiest lines to read; `merge` and
  `step` are the hardest.
- `-1`, `*xt` and `|light …|` mean the same however they are spaced.
- Signatures use the parenthesized form recommended under
  [Signature syntax](#signature-syntax). They are two characters longer than
  `Nat, Nat -> Nat`, but they line up with the clause heads.

### C. Whitespace, atomic elements

```ruby
exports {Area merge lower}

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
lower(r s mp mm k Succ(fuel)) if reaches(((r + mp) * 10) s).not() ->
  lower((r * 10) s (mp * 10) (mm * 10) (k - 1) fuel)
lower(r s mp mm k _) -> (generate(r s) k)

inside : Nat Nat Area -> Bool
inside(x y area) -> area.left <= x & x <= area.right

lit : List(Instruction) Bool -> Bool
lit(instructions start) -> instructions.fold(start |light Instruction(action _)| apply(light action))

expect [(2 1) (1 1)].sort_on(|(key _)| key) == [(1 1) (2 1)]
expect merge([1 4] [2 3]) == [1 2 3 4]
expect lower(1 2 3 4 -1 0) == ([] -1)
```

- Identical to A except for the two `lower` lines, which is the point: only 3–5%
  of lines change, and the compound-argument problem is fixed.
- This is Haskell's rule for application (`f b (a`mod`b)`), carried into
  delimited argument lists.
- Records still read as `x: (n y): …`, so C would need a rule for them too:
  either `{x: (n + 1) y: 2}` or commas in records only.
- It makes spacing matter more, not less. `f(a (b + 1))` against `f(a(b + 1))`
  is two arguments against one nested call, told apart by a single space. A
  has the same trap only with tuples, which are rarer. Once elements must be
  atomic, `f(a - 1)` would read as `f(a -1)` unless it is made an error, so the
  lexer keeps every rule it has and gains a diagnostic.
- It spends none of the weirdness budget back: C is as unusual as A, plus a
  paren rule to learn.

## How Haskell and others compare

Haskell separates by juxtaposition where the form is _application_, and by
commas where the form is _data_:

- No separator: application `f a b`, clause patterns `f (x:xs) ys`, type
  application `Map String Int`, constructor fields `data T = T Int Int`.
- `->`, curried: signatures `Int -> Int -> Int`.
- `,`: tuples, lists, records `P { x = 1, y = 2 }`, import and export lists,
  `deriving (Eq, Show)`, contexts `(Eq a, Ord a) =>`, guards and comprehensions
  `| x > 0, y > 0`.

In Haskell, commas are never needed where juxtaposition means application,
and always needed inside a data literal. The price is parentheses around any
compound argument, `f (x + 1) (g y)`, and `$` and `.` exist to avoid them.

Faun differs in two ways. Its call parentheses already delimit the arguments,
so a nested call needs no extra parentheses (`f(g(x) y)`, not `f (g x) y`). And
it allows infix operators inside argument lists, which Haskell does not. So
today's Faun is more permissive than Haskell for arguments (`gcd(b a % b)`), and
less conventional than Haskell for data (`[1 2 3]`, `{x: 1 y: 2}`).

A Haskell-shaped Faun would put commas in tuples, lists, records, tag rows, and
imports, and use option C's parentheses in calls and clause heads. Measured on
Ori, it changes 17% of lines and averages 40.4 columns (over-80 lines 315 → 346).
It keeps clause heads and signatures bare, where the commas cost the most. But it
has two separator rules, and calls and data would look different: `f(a b)`
next to `(a, b)`.

Other precedents:

- **Elm** follows Haskell's split.
- **OCaml and F#** use juxtaposition for application, `,` for tuples, and `;`
  for lists and records. F# lets newlines stand for `;`.
- **Nix** separates list elements by space and applies functions by
  juxtaposition, so `[ f x ]` is two elements. It is a well-known trap and the
  closest analogue to A's `[a - 1 b]`.
- **Clojure** treats commas as whitespace: `[1, 2, 3]` and `[1 2 3]` are the
  same. Faun could do the same, allowing commas where they help (`lower(r * 10,
  s, …)`) and omitting them in clause tables. The cost is two styles, a
  formatter that has to pick one, and spacing rules that still bind wherever a
  comma is left out.
- **Rust, Swift, Kotlin, Gleam, Roc, Python and JavaScript** use commas throughout.

## Decisions commas would bring

If Faun adopts commas, these need settling. Each has a recommendation.

### Trailing commas

Every comma-separated sequence has to say whether `[a, b,]` is allowed. Four
policies are common:

- **Forbidden** (Haskell, JSON, SQL): one spelling, but adding an element to a
  vertical list edits two lines, and reordering lines breaks the last one.
  Haskell programmers answer with leading commas, `, b`, to get the diffs back.
- **Allowed** (Rust, Python, JavaScript, Swift): both spellings
  parse; a formatter picks one.
- **Required on multi-line sequences** (Go): Go enforces it in the grammar
  because semicolon insertion would otherwise end the line.
- **Newline as a separator** inside brackets (F# lists and records):
  keeps today's clean vertical lists, but puts layout back in the grammar, and
  `f(a\n- b)` becomes ambiguous again.

Recommendation: allow a trailing comma in every sequence, the same rule
everywhere, and have the formatter write one exactly when the closing bracket
is on its own line. Then a vertical list changes one line per element, as it
does today without commas, and a one-line list has none. The grammar cost is
one check: after `,`, stop if the next token closes the bracket. That is still
LL(1).

The edge cases:

- **One-element tuples.** In Python, `(a,)` is a tuple and `(a)` is not, a
  well-known trap. Faun's tuples have two or more elements, so `(a,)` should be
  an error ("a tuple has at least two elements"), not a tuple or a grouping.
- **Empty sequences.** `f()`, `[]` and `{}` stay as they are; `f(,)` is an
  error.
- **After a rest.** Rust forbids a comma after `..` in struct patterns. Faun
  should allow `[h, *t,]` for uniformity. A rest still has to come last.
- **Lambda parameters.** `|a, b,|` is legal under a uniform rule and never
  written by the formatter.

Vertical declarations are where this shows. Ori's `Json` row would be:

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

- **`add : Nat, Nat -> Nat`** keeps today's shape. But a parameter of
  function type reads as `(a, b -> c)`, which looks like a tuple of `a` and
  `b -> c`.
- **`add : (Nat, Nat) -> Nat`** mirrors the clause head `add(a, b)` and the
  function types of Rust and TypeScript. A one-parameter signature may drop
  the parentheses, `fib : Nat -> Nat`. The cost is a tuple-typed parameter,
  which needs its own parentheses, `((Nat, Nat)) -> Nat`, as in Rust, and two
  more characters in multi-parameter signatures. A function-typed parameter
  keeps its parentheses, as today: `map : (Tree(a), (a -> b)) -> Tree(b)`.

Recommendation: the parenthesized form. It means the same thing in a
signature and in a parameter, it lines up with the clause heads below it, and
it closes the parameter list, so a `where` bound could later take
comma-separated constraints on one line
(`where a.zero : a, a.add : (a, a) -> a`) without ambiguity. Today each member
constraint is on its own line, which works under either spelling.

### Required or optional commas

Clojure's rule, commas as whitespace, lets clause tables stay bare. But
wherever a comma is left out, every spacing rule above still applies, so the
lexer keeps all of them, and the formatter must choose a house style anyway.
Recommendation: required. The parsing and tooling gains depend on it.

### `f (x)`

With commas, two operands are never legitimately side by side, so `f (x)`
could be read as a call, as in Rust or Python. Recommendation: keep calls
tight and report `f (x)` as an error. It costs one check, keeps `f(x)`
recognisable at a glance, and avoids a list element split across lines being
read as a call (`[f\n(x)]`).

### Ori compatibility

Faun runs Ori examples through `faun test` to choose what to build next. Ori
keeps whitespace, so after the change those examples no longer parse.
Recommendation: a one-off converter built from today's lexer, which already
finds every element boundary. It inserts a comma wherever an element begins
after another (the rule the measurement above used), so porting an Ori
example stays mechanical.

## What changed

- The lexer reads `,` and no longer decides `-`, `*` or `|` by spacing: the
  grammar tells a prefix from an infix by where it stands. `Negate`, `Rest`,
  `LambdaBar`, `Lopsided`, `NegatedElement` and `Adjacent` are gone, and
  tokens no longer carry their spacing. Only call adjacency (`f(x)`) and the
  joins `.`, `..`, `.*` and `?` still look at space.
- Every sequence takes an optional trailing comma. A rest comes last, and may
  be followed by one.
- A signature is a type: `(A, B) -> R`, `A -> R`, or the result alone for a
  nullary definition. A tuple-typed parameter is `((A, B)) -> R`, and a
  function-typed one is written bare in a list, `(List(a), a -> b) -> List(b)`.
- `(a,)` is refused: a tuple has at least two members.
- `to_str` writes lists and tags with commas, `[1, 2, 3]` and `P(1, 2)`, and
  diagnostics print types and patterns the same way.
- Ori examples no longer parse as Faun without their commas.
