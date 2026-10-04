# Pattern matching: the domain

An exploration, not a proposal (2026-10-04). What taking values apart has to
do, what Faun does today, how other languages spell each part, and a few
whole designs compared on the same programs. The proposals that come out of
it are [conditions](proposals/drafts/conditions.md),
[branching](proposals/drafts/branching.md) and
[loops](proposals/drafts/loops.md).

## What we want

**Kinds of match**

- **Clauses:** pattern, optional guard, `->` body. Kept as they are.
- **Ternary:** `if c then a else b`. Built.
- **Infallible destructure:** `(a, b) = pair`. A pattern that can fail is
  refused, with advice.
- **Fallible destructure:** pattern and optional conditions, else leave by
  `return`, `continue` or `break`. A default is a ternary: `n = if r is
  Ok(v) then v else 0`, or `r.ok_or(0)`.
- **Many-way on a computed value:** arms of pattern, optional guard, body;
  exhaustive.
- **Plain test:** is it this shape, as a `Bool`.
- **Loops:** `for` takes an infallible pattern; `while x is P` binds.
- **Lambda parameters:** infallible patterns, as today.

**Pattern vocabulary**

- Today's forms: constructors, literals, ranges, strings, lists with a
  rest, records open or closed, tuples, a repeated name as equality.
- Or-patterns everywhere, not only in a clause's parameters.
- The whole and its parts, `@` or `as`. Missing.
- Against a name in scope: guard, pin, or refused shadowing. Missing, and
  a trap.

**Rules**

- Names are seen where success is known: along the `&` chain, in the
  success branch or body, and below a guard line.
- A guard may bind, `r is Ok(v) & v > 0`, on one line.
- Exits are explicit: `return`, `continue`, `break`, `?`. No `return`
  expression.
- `&` and `|` short-circuit on `Bool`. Built.
- Effects stand one to a line. Built.
- `?` does not leave from a nested place for now: a branch, the right of
  `&`. To lift with loops.

**Constraints**

- One way to write each thing.
- LL(1); few keywords; no rule for one construct alone.
- The tree-sitter grammar mirrors the compiler's.
- Concise and plain: Python's length or shorter.
- A helper is cheap to write, and nesting is capped.

## What Faun has today

**Where a pattern stands:** a clause's parameters, a binding's left side, a
lambda's parameters. A clause's patterns may fail, falling to the next
clause; a binding's and a lambda's must always match.

**What a pattern may be:**

| Form          | Example               | Notes                       |
| ------------- | --------------------- | --------------------------- |
| Name          | `x`                   | always binds, shadowing     |
| Wildcard      | `_`                   |                             |
| Constructor   | `Some(x)`, `Order.Lt` | qualified where ambiguous   |
| Numeral, char | `0`, `'a'`, `-1`      |                             |
| Range         | `0..9`, `_..-1`       | clauses only: a test        |
| String        | `"get"`               | clauses only: a test        |
| List          | `[a, b, *rest]`, `[]` | rest binds the tail         |
| Record        | `{x, y: p}`, `{x, *}` | `*` leaves the other fields |
| Tuple         | `(a, b)`              |                             |
| Or            | `A(x) \| B(x)`        | clauses only; same names    |
| Repeated name | `same([a, a])`        | clauses only; equal values  |

**Guards:** `if condition` after a clause's patterns. On failure, the next
clause.

**Missing:** binding a whole value while taking it apart, matching against
the value of a name already in scope, testing a computed value without a
helper definition, and a fallible binding.

## The functionality

Each question below is independent of how it is spelled. A design answers
every one.

### 1. Where a match happens

| Subject            | Example need                     | Today      |
| ------------------ | -------------------------------- | ---------- |
| Parameters         | `drain([])`, `drain([x, *rest])` | clauses    |
| A computed value   | what `heap.pop()` gave           | a helper   |
| A binding          | `(a, b) = pair`                  | yes, total |
| Lambda parameters  | `\|(k, v)\| …`                   | yes, total |
| A loop's element   | `for (k, v) in pairs`            | no loops   |
| A loop's condition | `while $stack is [x, *$stack]`   | no loops   |

### 2. How many ways it goes

- **Many ways:** one arm per shape, checked exhaustive. Clauses do this for
  parameters; nothing does it for a computed value.
- **Two ways:** a test that binds on success and does something else on
  failure. `if r is Ok(v) then … else …`.
- **One way or leave:** a fallible binding. On success the names go on with
  the block; on failure the clause, round or loop is left.
- **A plain test:** is it this shape, as a `Bool`, binding nothing used.

### 3. What failure does

| Failure goes to           | Where                                           |
| ------------------------- | ----------------------------------------------- |
| The next clause or arm    | clauses, `when` arms                            |
| An `else` branch          | `if`                                            |
| `False`                   | a plain test                                    |
| An exit                   | fallible binding: `return`, `continue`, `break` |
| A refusal at compile time | a binding or lambda whose pattern can fail      |

### 4. Guards

A pattern is often not enough on its own: `Move(d)` where `d > 100`. Two
strengths:

- **A `Bool` guard,** seeing the pattern's names.
- **A binding guard,** testing a computed value against a further pattern:
  the entry is `Ok` _and_ its key is below the limit. Haskell's pattern
  guards, Rust's `let` chains, Swift's `if case … , case …`.

### 5. Where names are seen

| Construct                    | Names seen in                                 |
| ---------------------------- | --------------------------------------------- |
| Clause, arm                  | its guard and its body                        |
| Two-way test                 | the rest of its `&` chain, the success branch |
| Fallible binding             | the rest of its line, every line below        |
| Under `\|`, `!`, an argument | nowhere                                       |

### 6. Exhaustiveness

Clauses and arms are checked to cover every value; a binding must always
match. A two-way test and a fallible binding are partial by design: their
failure path is the cover.

### 7. Pattern vocabulary, beyond today's

- **The whole and its parts:** bind `node` and also take it apart. Rust and
  Haskell `node @ Leaf(x)`, OCaml and Roc `Leaf(x) as node`.
- **Against a name in scope:** match where the value equals `limit`, not
  bind a new `limit`. Elixir pins, `^limit`; most languages make you write a
  guard. In Faun a name in a pattern always binds, so `n is limit` binds a
  fresh `limit`, which is a trap to refuse or warn of.
- **Not this shape:** `!(x is P)`, which binds nothing; C# has `x is not P`.
- **Or-patterns everywhere:** today only a clause's parameters take them.
- **View patterns:** match what a function answers of the value, Haskell's
  `(len -> 0)`. Rarely worth the syntax; a guard does it.

## Tensions

- **`|` is both or and alternatives.** `x is A | B` reads as an or of a test
  and a constructor. Or-patterns after `is` need parentheses, unless the
  boolean or becomes a word.
- **`if` is both a guard and an expression.** A line beginning `if` is a
  guard of the clause above where items are written, and an `if` in a block;
  the lexer and the tree-sitter scanner both carry that rule.
- **Names always bind.** Every pattern position shadows, so comparing with a
  name in scope needs a guard, and forgetting is silent.
- **`?` cannot leave from a nested place.** A branch, an arm, the right side
  of `&`: `?` there is refused until leaving from a nested match is built.
- **Clauses and `when` overlap.** `f(x) -> when x (…)` does what clauses do.

## How others spell it

Many-way, two-way test, fallible binding, and guard, in each:

- **Rust:** `match x { P => e }`; `if let P = x`; `let P = x else { … }`;
  `if`.
- **Swift:** `switch x { case P: }`; `if case P = x`; `guard case P = x
  else`; `where`.
- **Kotlin:** `when (x) { P -> e }`; `x is T`; `x as? T ?: return`; none.
- **C#:** `x switch { P => e }`; `x is P`; `if (x is not P) return;`;
  `when`.
- **Python:** `match x: case P:`; none; none; `if`.
- **Elixir:** `case x do P -> e`; `match?(P, x)`; `with P <- x do … else`;
  `when`.
- **Haskell:** `case x of P -> e`; a pattern guard `P <- x`; `do`; `|`.
- **OCaml, F#:** `match x with P -> e`; a `match` with `_`; none; `when`.
- **Zig:** `switch (x) { … }`; `if (x) |v|`; `x orelse return`; none.
- **Roc:** `match x { P => e }`; `match`; `x?` and `x ?? d`; `if`.

Two shapes recur. **A pattern first, then the value** (`if let P = x`, `let
P = x else`) keeps a binding's order, pattern on the left. **The value
first, then the pattern** (`x is P`) reads as a question and composes with
`&` as a `Bool`.

## Syntax options, part by part

### Many-way on a computed value

- **`when x ( P -> e … )`,** the draft. Arms read as clauses, and the
  grammar stays LL(1). A keyword, and `when x(` is a call.
- **`match x ( … )`.** Familiar, but takes a name programs want.
- **A postfix block, `x.( P -> e … )`.** No keyword, reusing a type's `.(`;
  cryptic.
- **Lambdas of several clauses, `x.match(|P| e, |Q| f)`.** No new
  construct, but heavy: a lambda an arm.

### Two-way test

- **`if x is Ok(v) & v > 0 then`,** the draft. A `Bool`, composing with
  `&`; the value comes first, where `=` puts the pattern first.
- **`if Ok(v) = x then`,** Rust's `if let`. The pattern on the left, as `=`
  has it; but `=` inside a condition reads as a test of equality.
- **`x.matches(Ok(_))`.** No syntax, and binds nothing.

### Fallible binding

- **A bare `else` line, `x is Ok(v) else return 0`.** Short, and any
  condition; the exit is at the line's end.
- **An `if` guard line, `if x is Ok(v) else return 0`.** Every conditional
  line begins `if`, so an exit is found at the margin; two keywords.
- **`let … else`, `Ok(v) = x else return 0`.** The pattern on the left, as
  `=` has it; a second form is wanted for a plain test.
- **`guard x is Ok(v) else return 0`.** Found at the margin, for a keyword.
- **`??` with an exit, `v = x ?? return 0`.** Shortest for a `Result`, and
  only for one: a second way to write that case.
- **A `with` block, `with (Ok(v) <- x, …) else return 0`.** Several steps
  and one failure path, in a block of its own.

### Guards

- **`f(Move(d)) if d > 100 ->`,** today. Familiar from Rust and Scala; `if`
  is also an expression.
- **`f(Move(d)) & d > 100 ->`.** Reads as `is P & c`, and the lexer's rule
  for a line beginning `if` goes; `|` in a guard needs parentheses.
- **`f(Move(d)) when d > 100 ->`.** Elixir's, OCaml's and F#'s; `when` is the
  many-way keyword here.
- **`f(Move(d)) | d > 100 ->`.** Haskell's; clashes with or.

### Or-patterns

- **`x is (A | B)`.** As clauses write it, with parentheses clauses need
  not.
- **`x is A or B`.** C#'s, with no clash; `or` beside `|` for one idea.
- **Word operators, `a and b`, `a or b`, leaving `|` to patterns.** The
  clash gone at its root; every `Bool` expression changes.

### The whole and its parts

- **`node @ Leaf(x)`.** Rust's and Haskell's; a new token.
- **`Leaf(x) as node`.** OCaml's and Roc's, reading as English; a keyword.
- **`node = Leaf(x)` inside a pattern.** No new token; `=` already ends a
  binding's left side.

### Against a name in scope

- **A guard, `x is n if n == limit`.** Nothing new; long, and easy to
  forget.
- **A pin, `x is ^limit`.** Elixir's; a sigil.
- **Refuse shadowing in a test.** The trap cannot happen, for a rule of its
  own.

## Whole designs

The same four programs in each design: a heap drain (fallible binding), a
path walk (a computed value, a guard), a parser step (many ways), and a
validation (a binding guard).

### A. `is`, `if` guards, `else` lines (the draft as it stands)

```
drain(heap, state) -> (
  heap.pop() is Ok({key, value, rest}) else return state
  next = visit(state, key, value)
  rest.drain(next)
)

back(settled, node, route) -> (
  settled.get_or(node, Err(Unreachable)) is Ok({from, *}) else return Err(Unreachable)
  walked = [node, *route]
  if from == node then Ok(walked) else back(settled, from, walked)
)

token(bytes) -> when bytes (
  [] -> End
  ['0'..'9', *rest] -> number(bytes)
  [c, *rest] if c.is_space() -> token(rest)
  [c, *rest] -> Symbol(c, rest)
)

admit(entry, limit) -> (
  entry is Ok({key, *}) & key < limit else return Rejected
  Admitted(key)
)
```

The exit sits at each line's end; one rule for names; `if` is both a guard
and an expression.

### B. `is`, `&` guards, `else` lines

```
token(bytes) -> when bytes (
  [] -> End
  ['0'..'9', *rest] -> number(bytes)
  [c, *rest] & c.is_space() -> token(rest)
  [c, *rest] -> Symbol(c, rest)
)
```

The rest as in A. A clause, an arm, a test and an `else` line all read
_pattern, then `&` conditions_. `if` means one thing, and the lexer's rule
for a line beginning `if` goes.

### C. `is`, `if` guards, `if` guard lines

```
drain(heap, state) -> (
  if heap.pop() is Ok({key, value, rest}) else return state
  next = visit(state, key, value)
  rest.drain(next)
)

admit(entry, limit) -> (
  if entry is Ok({key, *}) & key < limit else return Rejected
  Admitted(key)
)
```

`if` always introduces a condition; what follows says what success does:
`then` a value, `->` a body, nothing to go on with the block. Every exit is
found at the left margin.

### D. Pattern-first, Rust's way

```
drain(heap, state) -> (
  Ok({key, value, rest}) = heap.pop() else return state
  next = visit(state, key, value)
  rest.drain(next)
)

back(settled, node, route) -> (
  Ok({from, *}) = settled.get_or(node, Err(Unreachable)) else return Err(Unreachable)
  …
)

admit(entry, limit) -> (
  Ok({key, *}) = entry else return Rejected
  key < limit else return Rejected
  Admitted(key)
)
```

A pattern is always on the left of `=`, so a binding and a fallible one
read alike. A binding guard takes a second line, and a two-way test needs
`if let`-like syntax of its own: `if Ok(v) = x then`.

### Comparing

| Measure                 | A          | B        | C          | D         |
| ----------------------- | ---------- | -------- | ---------- | --------- |
| New keywords            | 4          | 4        | 4          | 3         |
| One rule for names      | yes        | yes      | yes        | two forms |
| Exits at the margin     | no         | no       | yes        | no        |
| `if` means one thing    | no         | yes      | by reading | no        |
| Binding guard, one line | yes        | yes      | yes        | no        |
| Guards migrate          | no         | ~100     | no         | no        |
| Grammar size            | middle     | smallest | largest    | middle    |
| Familiar from           | C#, Kotlin | Haskell  | Swift      | Rust      |

## Open questions

- Which of A, B and C, the three that share `is`.
- `@` or `as` for the whole and its parts, if either.
- Whether shadowing in a test is refused, pinned or left to a guard.
- Whether or-patterns need parentheses after `is`, or `or` becomes a word.
- Whether clauses and `when` are both kept, and which takes a parameter
  apart.
