# Pattern matching: the domain

An exploration, not a proposal (2026-10-04). What taking values apart has to
do, what Faun does today, how other languages spell each part, and a few
whole designs compared on the same programs. What came out of it is
[pattern matching](pattern-matching.md), which says what holds now and why;
loops, which it also shaped, were removed on 2026-11-10
([iteration](../iteration.md)). The `when` draft it replaced is
[below](#the-when-draft).

## Decided

As of 2026-10-05, after the designs below and two drawn up afresh from the
brief at the end (by Claude and by GPT-6 Astra, both of which arrived at
`is` with flowing names and a dedicated exit line), and revised 2026-10-07:

- **`value is pattern`** is a `Bool` that binds where it is known to have
  held: along `&`, into `then`, below an `else` line. Built.
- **`condition else …`,** a block's line, goes on where the condition
  holds, keeping its names for the lines below, and otherwise leaves: `else
  return x`, `return`'s value any expression, a block doing effects first
  among them; beside it, `if c return x` leaves where `c` holds. These
  replace design E's `if` lines. Both fresh designs led the line with a
  keyword, `guard`, and it was built first as `expect … else`; the keyword
  went on 2026-10-07, since `return` already marks every leave (and
  `continue` and `break` did, while there were loops), and a block ending
  in a leave as an `else`'s went on 2026-10-08, `return` taking a block.
  Built.
- **A bare `expect` in a body,** an assumption checked in development and
  skipped in optimized builds, binding nothing, is for later; until then a
  body's line beginning `expect` is refused.
- **Arms after `is`** are a line each; an arm may be a block. Built,
  with guards, 2026-10-07. Arms on a bare parameter are left to style:
  clauses by default, arms where the other parameters would repeat on every
  clause. Revised 2026-10-16: an arm's value follows `then`, as an `if`'s
  does, and a leave may stand in its place, `P return x`; see
  [pattern matching](pattern-matching.md#tests-and-arms).
- **Many ways on a value** are `is` with arms, `x is ( P then … )`, with no
  `match` or `when` keyword. Both fresh designs used `match`; the brief did
  not offer Finch's idea, so that says nothing against it.
- **`is` inside a pattern** binds the whole and its parts: `right is [y,
  *_]`. Built, 2026-10-06.
- **`==name` in a pattern** compares with a name from outside it:
  `Some(==node)`, a part only, never a test's or an arm's whole pattern,
  which `x == y` writes. Within one pattern, a name written twice asks its parts
  equal, `[a, a, *_]`, in a test as in a clause's head; `[a, ==a]` is
  refused, since `==` reads as reaching outside the pattern.
  Built, 2026-10-06.
- **`=` binds a name again as a shadow,** to the end of its block, at any
  type; a binding again that nothing reads is refused. Nothing changes in
  place, so a step is `order = order.append(node)`. A pattern binds a name
  in scope again where it matched, as `=` does (2026-10-11). No-rebinding
  (built 2026-10-05) gave way on 2026-10-07 to binding from here on,
  Python's model, past branches and across a loop's rounds; that gave way
  to shadowing on 2026-11-10, when loops went. See
  [binding again](#binding-again-the-designs-weighed).
- **Leaving where a test holds** is an `if` line, `if n1 is Bot return
  Bot`, beside the `else` line for what should hold: one passes names down,
  the other bails out. First accepted as a negated `else` line, to keep one
  direction to one form; revised 2026-10-07, the two lines doing two jobs.
- **`?` anywhere an expression goes,** as an `else` line will be in any
  block: in a branch, an arm, a block inside either, the right of `&`
  or `|`, leaving the clause or lambda from there. Today's refusals are a
  gap in lowering, closed by join points: the rest of a body after a branch
  made a local function each branch calls, so a branch can leave instead.
  Built, 2026-10-07.
- **A name both sides of `|` bind,** at one type, is seen where the `|` held:
  to its right along `&`, in `then`, below an `else` line. Whichever side held
  supplies it. A name only one side binds is seen nowhere past the `|`.
  Built, 2026-10-06.
- **What a guard's test binds is seen in its clause's body,** as `then` sees
  an `if`'s. Often the test belongs in the head instead: `describe(Ok(v))
  if v > 100`, or `describe(r is Ok(v))`; a guard's test is for a value the
  head cannot reach, `f(x) if lookup(x) is Some(v) -> …`. Built,
  2026-10-06.
- **Rules that pick between forms** are a linter's, not the compiler's:
  `x is 3` written `x == 3`; a two-arm `is` ending in `_` written as an
  `if`; an `else` line before a block's last line written as a ternary; a
  many-way `is` on a bare parameter written as clauses. Gathered in
  [lints](../lints.md).
- **Alternatives after `is` are parenthesized,** `x is (A(v) | B(v))`,
  since `|` is also the `Bool` or.
- **Clauses where the body is the dispatch;** `is` where a test is one step
  among several; the ternary for a choice of two values.

## What we want

**Kinds of match**

- **Clauses:** pattern, optional guard, `->` body. Kept as they are.
- **Ternary:** `if c then a else b`. Built.
- **Infallible destructure:** `(a, b) = pair`. A pattern that can fail is
  refused, with advice.
- **Fallible destructure:** pattern and optional conditions, else leave by
  `return`: `r is Ok(v) else return 0`. A
  default is a ternary, `n = if r is Ok(v) then v else 0`, or `r.ok_or(0)`.
- **Leave early on a test:** `if n == 0 return 0`, or `n != 0 else
  return 0` for what should hold.
- **Many-way on a computed value:** `x is ( arms )`, each arm a pattern,
  optional guard, `then` value; exhaustive. No `when`.
- **Plain test:** is it this shape, as a `Bool`: `x is P`. Several values
  at once as a tuple, `(a, b) is (Ok(x), Ok(y))`; a chain, `x is Some(y) &
  f(y) is Some(z)`, where a test reads what an earlier one bound.
- **Loops:** `for` took an infallible pattern and `while x is P` bound;
  removed 2026-11-10, a walk being recursion or a fold.
- **Lambda parameters:** infallible patterns, as today.

**Pattern vocabulary**

- Today's forms: constructors, literals, ranges, strings, lists with a
  rest, records open or closed, tuples, a repeated name as equality.
- Or-patterns everywhere, not only in a clause's parameters.
- The whole and its parts, `is` inside a pattern: `right is [y, *_]`.
  Built.
- A list's end, `[*init, last]`: elements after a rest, in clauses. Built.
- Against a name in scope: `==name`. Built; the name alone binds again,
  as `=` does.

**Rules**

- Names are seen where success is known: along the `&` chain, in the
  success branch or body, and below a guard line.
- A guard may bind, `r is Ok(v) & v > 0`, on one line.
- Exits are explicit: `return` and `?`. No `return` expression.
- `&` and `|` short-circuit on `Bool`. Built.
- Effects stand one to a line. Built.
- `?` leaves from a branch, an arm or a block inside either. Built. On the
  right of `&` or `|` it is refused, since that side may not be worked out.

**Constraints**

- One way to write each thing.
- LL(1); few keywords; no rule for one construct alone.
- The tree-sitter grammar mirrors the compiler's.
- Concise and plain: Python's length or shorter.
- A helper is cheap to write, and nesting is capped.
- **Clauses where the body is the dispatch.** A function whose first and
  only step is taking a value apart is clauses, through a helper if need
  be: each case a line, its pattern at the margin. `if … is` is for a test
  that is one step among several, and the ternary for a choice of two
  values.

## Faun's forms, simplest first

Every form programs keep writing, as Faun spells it on `main`, from a plain
binding to a match nested in a match. Several are the examples of the
ultimate and penultimate conditional syntaxes, translated. Each comment says
whether it is built or planned.

```faun
# Take a value apart where it cannot fail. Built.
(a, b) = pair
{x, y, *} = point
total = pairs.fold(0, |sum, (_, value)| sum + value)

# Choose between two values. Built.
sign = if n < 0 then -1 else if n == 0 then 0 else 1

# Pass a failure on to the caller. Built.
count = Nat.from_str(text)?

# A default where it fails. Built.
count = Nat.from_str(text).ok_or(0)

# Ask whether a value has a shape, as a Bool. Built.
empty = list is []
found = results.filter(|result| result is Ok(_))

# Go on only where a test holds: else leave the function. Built.
n != 0 else return 0

# Take apart, or leave: what it binds goes on below. Built.
heap.pop() is Ok({key, value, rest}) else return state
args is [_, name, *_] else return Err(Usage)

# The same, with conditions reading what it bound. Built.
entry is Ok({key, *}) & key < limit else return Rejected

# Compare with a name in scope, rather than bind. Built.
reached_from_itself = prev.get(node) is Ok(==node)

# A default for a shape `ok_or` cannot reach. Built.
width = if config is {width: Ok(w), *} then w else 80

# Several values at once, as a tuple. Built.
order = if (a, b) is (Ok(x), Ok(y)) & x <= y then Sorted else Unsorted

# One test reading what another bound. The paper's context lookup. Built.
value = if expr is Var(name) & context.get(name) is Ok(found) then found else Unbound

# Dispatch on a parameter's shape: clauses. Built.
len([]) -> 0
len([_, *rest]) -> 1 + len(rest)

# Classes, alternatives and a list's end, in clauses. Built.
kind('0'..'9') -> Digit
kind(' ' | '\t' | '\n') -> Space
kind(_) -> Other

last([*_, x]) -> Ok(x)
last([]) -> Err(Empty)

# Many ways on a computed value: `is` and arms. Finch's sign. Built.
sign = n is (
  _..-1 then -1
  0 then 0
  _ then 1
)

# Arms with guards. The paper's sizes, without its splits. Built.
size = foo(args) is (
  0 then "null"
  n if n.abs() > 100 then "large"
  n if n.abs() < 10 then "small"
  _ then "medium"
)

# Two values at once, many ways. Built.
fizz(n) -> (n % 3, n % 5) is (
  (0, 0) then "FizzBuzz"
  (0, _) then "Fizz"
  (_, 0) then "Buzz"
  _ then n.to_str()
)

# An arm going on into a further match. The paper's cache. Built.
answer = x is (
  Right(Err(_)) then default
  Right(Ok(cached)) then f(cached)
  Left(input) then compute(input) is (
    Err(_) then default
    Ok(result) then f(result)
  )
)

# Alternatives binding one name, at one type. The paper's evaluator. Built.
simple = e is (
  Lit(v) | Add(Lit(0), Lit(v)) | Add(Lit(v), Lit(0)) then Ok(Lit(v))
  _ then Err(NotSimple)
)

# The whole and its parts: `is` inside a pattern, after Finch. Built.
merge([x, *xs], right is [y, *_]) if x <= y -> [x, *merge(xs, right)]
merge(left, [y, *ys]) -> [y, *merge(left, ys)]
merge(left, []) -> left

# A chain of steps in one condition. The paper's `_1234`. Built.
identifier(name, arity) ->
  if digits_after(name) is Ok(digits)
    & Nat.from_str(digits) is Ok(index)
    & index < arity
  then Ok((index, name))
  else Err(Invalid(name))

# The same as early exits, a step to a line. Built.
identifier(name, arity) -> (
  digits_after(name) is Ok(digits) else return Err(Invalid(name))
  Nat.from_str(digits) is Ok(index) & index < arity else return Err(Invalid(name))
  Ok((index, name))
)

# Early exits instead of nesting. The paper's `normalize`, after Finch. Built.
meet(t1, t2) -> (
  n1 = normalize(t1)
  if n1 is Bot return Bot
  n2 = normalize(t2)
  if n2 is Bot return Bot
  if merge(n1, n2) is Ok(merged) then merged else glb(n1, n2)
)

# Clauses and `?` together. Finch's `zip_with`. Built.
zip_with(f, [x, *xs], [y, *ys]) -> (
  tail = zip_with(f, xs, ys)?
  Ok([f(x, y), *tail])
)
zip_with(_, [], []) -> Ok([])
zip_with(_, _, _) -> Err(Mismatch)
```

`r is Ok(limit)` where `limit` is a name already binds it again, as `=`
would, where the test holds; `Ok(==limit)` compares. Refused until
2026-10-11.

## What Faun had on 2026-10-04

This section and the questions after it describe the language when the
exploration began. [Pattern matching](pattern-matching.md) says what holds
now; Decided and the forms above are kept current.

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
| List's end    | `[*init, a, b]`       | clauses only: a split       |
| Record        | `{x, y: p}`, `{x, *}` | `*` leaves the other fields |
| Tuple         | `(a, b)`              |                             |
| Or            | `A(x) \| B(x)`        | clauses only; same names    |
| Repeated name | `same([a, a])`        | clauses and tests; equal    |
| Whole, parts  | `all is [x, *_]`      | clauses and tests           |
| Equal to name | `Some(==node)`        | a name from outside it      |

**Guards:** `if condition` after a clause's patterns. On failure, the next
clause.

**Missing,** until `is`, `expect` and the forms above (2026-10-05 and
2026-10-06): binding a whole value while taking it apart, matching against
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
| The next clause or arm    | clauses, `is` arms                              |
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
  Haskell `node @ Leaf(x)`, OCaml and Roc `Leaf(x) as node`; here `node is
  Leaf(x)`, after Finch.
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
- **Clauses and many-way `is` overlap.** `f(x) -> x is (…)` does what
  clauses do. Style, not grammar, sends a parameter to clauses.

## The ultimate and penultimate conditional syntax

Cheng and Parreaux's
[ultimate conditional syntax](https://lptk.github.io/files/ucs-paper.pdf)
(OOPSLA 2024) and Tony Finch's
[penultimate conditional syntax](https://dotat.at/@/2025-05-13-if-is.html)
(2025) turn pattern matching into a generalization of `if`, rather than
`if` into a case of matching. Both arrive where this note does:

- `x is P` is a `Bool`, and what it binds flows into whatever is known to
  follow its success: the rest of an `and` chain and the `then` branch,
  which the paper calls conditional pattern flowing.
- Chains interleave computation: `expr is Var(name) and ctx.get(name) is
  Some(value)`.
- Alternatives after `is` must be grouped, since `b is true || false`
  reads two ways. Finch requires braces where this note requires
  parentheses.
- Evaluation is left to right and short-circuiting, with no backtracking.
- Early returns and `?` flatten what nested matches would indent.

Taken from them:

- **A many-way match is `is` with arms.** Finch writes `x is { || P => a ||
  Q => b }`; here `x is ( P -> a … )`, so `when` is not needed. `is` always
  means matches: a pattern makes a test, arms make a value.
- **`is` inside a pattern binds the whole.** Finch's `Some(p is Pair(x,
  y))` names `p` and takes it apart, with no `@` or `as`.

Left with them:

- **Splits,** continuing a condition from a shared prefix, `if x == 0 then
  … > 0 then …`. They lean on an offside rule and on compiling away the
  tests they repeat; a many-way `is` does their work.
- **`let` inside a condition,** against rightward drift, which guard lines
  prevent.
- **`then` and `else` as operators,** Finch's `=>` and `|| =>`.
- **Relational patterns,** C#'s `Some(< 0)`. Ranges, `_..-1`, cover
  integers; perhaps later, for floats.

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

- **`x is ( P -> e … )`,** the lean, after Finch. No keyword: `is` already
  means matches. It parses as a parenthesis does, by what follows its first
  expression: `->` or a guard's `if` begins arms, so `x is (A | B)` stays a
  test.
- **`when x ( P -> e … )`,** the branching draft. Arms read as clauses, and the
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

- **`node is Leaf(x)` inside a pattern,** the lean, after Finch. No new
  token, and `is` means what it means anywhere: the name, which is that
  shape.
- **`node @ Leaf(x)`.** Rust's and Haskell's; a new token.
- **`Leaf(x) as node`.** OCaml's and Roc's, reading as English; a keyword.
- **`node = Leaf(x)` inside a pattern.** No new token; `=` already ends a
  binding's left side.

### Against a name in scope

- **A test, `r is Ok(n) & n == limit`.** Nothing new; long, and easy to
  forget.
- **A pin, `r is Ok(^limit)`.** Elixir's; a sigil.
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

### E. `is`, `if` guards, `if` lines that leave (the current lean)

C, with an exit allowed straight after the condition, leaving where it
holds, beside `else` and an exit, leaving where it fails; a many-way match
is `is` with arms, and `is` inside a pattern binds the whole.

```
drain(heap, state) -> (
  if heap.pop() is Ok({key, value, rest}) else return state
  next = visit(state, key, value)
  rest.drain(next)
)

back(settled, node, route) -> (
  if settled.get_or(node, Err(Unreachable)) is Ok({from, *}) else return Err(Unreachable)
  walked = [node, *route]
  if from == node return Ok(walked)
  back(settled, from, walked)
)

walk(graph, stack, seen) -> (
  if stack is [node, *rest] else return seen
  if seen.contains(node) return walk(graph, rest, seen)
  …
)

token(bytes) -> bytes is (
  [] -> End
  ['0'..'9', *rest] -> number(bytes)
  [c, *rest] if c.is_space() -> token(rest)
  [c, *rest] -> Symbol(c, rest)
)

merge([x, *xs], right is [y, *_]) if x <= y -> [x, *merge(xs, right)]
```

A line that may leave begins `if`; the token after its condition says
which way:

```
"if" condition ( exit                       # leave where it holds
               | "else" exit                # leave where it fails
               | "then" expr "else" expr )  # a value either way
exit = "return" expr | "continue" | "break"
```

Leaving where it holds reads best for a plain test, `if n == 0 return 0`;
leaving where it fails is what a binding needs, since what the condition
binds goes on with the lines below. A plain test could be written either
way; the style is the first, unless the condition binds for what follows.

Since decided otherwise: leaving where the condition fails became a line of
its own, `condition else …`, first spelled `expect condition else …`, and
leaving where it holds an `if` line beside it. See Decided, at the top.

### Comparing

| Measure              | A   | B     | C     | D    | E    |
| -------------------- | --- | ----- | ----- | ---- | ---- |
| New keywords         | 5   | 5     | 5     | 4    | 4    |
| One rule for names   | yes | yes   | yes   | no   | yes  |
| Exits at the margin  | no  | no    | yes   | no   | yes  |
| `if` means one thing | no  | yes   | yes   | no   | yes  |
| Binding guard inline | yes | yes   | yes   | no   | yes  |
| Plain test, short    | no  | no    | no    | no   | yes  |
| Guards migrate       | no  | ~100  | no    | no   | no   |
| Grammar size         | mid | least | most  | mid  | most |
| Familiar from        | C#  | Hask. | Swift | Rust | Ruby |

## The `when` draft

Drafted on 2026-10-01, before the exploration above, and superseded on
2026-10-14 by `is` with arms, which branch on a computed value as `when`
would have. It never was built.

A Faun body could not branch on a value it computed, so each such branch
was a definition of its own. The draft counted eight in the graph and heap
libraries: `visiting` and `drained` took apart `heap.pop()`, `stepped` the
step a path walks back through, `sorted` whether toposort ordered every
node, and `climb_past`, `sink_past`, `cheaper` and `either` the heap's
comparisons. Its answer was a value, then clauses in parentheses:

```ruby
back(settled, node, route) -> (
  step = settled.get_or(node, Err(Unreachable))?
  walked = [node, *route]
  when step.from (
    from if from == node -> Ok(walked)
    from -> back(settled, from, walked)
  )
)
```

- **Arms were clause lines,** `pattern [if guard] -> expr`, parted by line
  ends and never commas, as a block's lines are. After the value, a plain
  `(` could not go on with an expression, so it opened the arms, and the
  grammar stayed LL(1).
- **The parentheses were needed.** Without the `)`, a `when` ending a
  top-level body would take the next definition's clauses as arms; inside a
  block, a line after the arms could be the next statement or another arm
  until an `->` arrived; and a `when` inside another would take the outer
  one's later arms.
- **An arm could leave,** `Err(error) -> return Err(error)`, where the
  `when` was a block's line or a binding's value: the many-way form of a
  destructuring that can fail. Arms of `is` kept this.
- **The keyword was `when`,** after Kotlin's. `match` was left free as a
  name, which parsers, regular expressions and templates want, and Faun's
  guards being `if`, `when` did not read as a guard, as it does in Elixir,
  F# and OCaml.
- **The space before `(` mattered:** `when x(` is a call of `x`, so the
  formatter would always write the space and the parser name the likely
  mistake.
- **An unclosed `when`** ran on through every clause after it, since a
  top-level clause reads as an arm, and was to be told at its `(`.

Its costs were two ways to take a parameter apart, `f(x) -> when x (…)`
doing what clauses do; nesting, which languages with match expressions
tend to; less pressure to name a step that was a real one; and a keyword.

Weighed against it, and left:

- **Keep the grammar,** a helper and its signature for each branch on a
  computed value: a visible, bounded cost, but one falling hardest on data
  structures, where most of a step is comparisons partway through a walk.
- **A postfix form,** `heap.pop().( Err(Empty) -> …, Ok(e) -> … )`,
  reusing a type's `.(`: no keyword or token, but cryptic, and its gain is
  chaining, which naming each step works against.
- **Lambdas of several clauses** handed to a method, `popped.match(|Err(Empty)|
  -> …, |Ok(e)| -> …)`: one construct for branching in name, with a heavier
  spelling of the same meaning.
- **Commas between arms,** for one-line branches: they parse, but blocks
  and method blocks take line ends only, and a two-way branch on one line is
  usually better as a method call.
- **No separator between arms:** almost parses, except a pattern beginning
  with `-`, `n -> a -1 -> b` reading as a subtraction.
- **`if` expressions,** a `when` on a `Bool`, for the helpers that were
  two-way tests on a comparison. These were built, with `is`.

Discussed beside it on 2026-10-02 and recorded with it, aiming at one way
to write each thing and the classic algorithms as short as their Python:

- **A local function as a binding of a lambda,** `walk = |stack| …`,
  seeing its own name, lifted with what it reads as extra parameters, as
  Haskell's `where` and Erlang's named funs end the passing of context by
  hand. Clauses would stay the top-level form: a third of the 1,974
  definitions then written had several clauses, each of which would become
  a `when` on a tuple of its parameters if a lambda were the only form. Not
  built.
- **Local lambdas need no lambda sets** if what is bound must be a lambda
  written there or a named function, each name then standing for one known
  function.
- **Functions in data** would cost lambda sets, and every call being a
  static edge. Nothing written wanted it.
- **Guard conditions, `else` lines and a destructuring `if`** became the
  `is` design above.

## Binding again, the designs weighed

A step, `order = order.append(node)`, binds a name again. The designs
tried, in order, and what each cost:

- **No rebinding,** built 2026-10-05: a name meant one value for its whole
  scope, at the price of a fresh name for every step, `degrees2`.
- **`$` variables,** the loops draft's: a name a loop changed was marked at
  every use, `$order.append(node)`, a sigil on every mention.
- **A separate assignment operator,** `x := x + 1`, `=` binding only new
  names: every change and every new name would show on its line, and a
  typo would be refused rather than warned of; but a second binding
  operator for what one `=` says.
- **Binding from here on,** Python's model, built 2026-10-07: a name bound
  again was seen past branches and across a loop's rounds, at any type on
  a straight line and one type where paths met, if read there. It cost
  resolution a merge of every name each way bound again, join points
  taking those names as parameters, and a loop's round a call with them.
- **A name keeping one type everywhere,** as binding from here on was
  first built: a straight line of steps converting a value, `Str` to `Nat`,
  needed a name for each; held to one type only where read from
  2026-10-12.
- **A pattern only declaring,** `r is Ok(limit)` refused where `limit` was
  in scope, until 2026-10-11: it guarded against meaning a comparison, but
  made a name in a pattern read by what was in scope, and cost a worklist
  `ready = rest`, a step a `continue` above it would skip.
- **Writing back,** a bare `order.append(node)` changing `order`: whether a
  line changed a name would hang on its shape and the method's type.
- **Shadowing,** a name bound again hiding the one before to the end of its
  block. Turned down on 2026-10-07, since a branch's `count = count + 1`
  would vanish after the branch, silently; taken on 2026-11-10, when loops
  went and with them most of what binding from here on carried, together
  with refusing a binding again that nothing reads, which catches that
  case.

## Open questions

- **Relational patterns,** `Some(< 0)`, for floats. Later, if wanted.
- **Left for later in what is built:** a test of a value holding a
  resource, used up on the failing side where no shape it may still have
  holds one; a type taken apart by its own name, as `U8(…)`.

## A brief, without syntax

What a design has to do, stated with no syntax, so one can be drawn up
afresh and compared with the designs above. Hand this section over on its
own.

### The task

Design how a small, pure, strict language takes values apart and branches
on them: every construct for matching, testing, conditions and leaving
early. **The aim is code that is easy and natural to read**, then short,
then simple to parse. A reader new to the language should guess what a
line does.

The goals, qualities and non-goals below say what the language's authors
have found they want so far. They are evidence, not a contract, and none
outweighs the aim. Where one looks too onerous, or where letting it go buys
a more general or prettier design, relax it and say so: which, why, and what
a program loses. A design that covers fewer goals and reads better is a
good answer. Two things are fixed: the language section below, which says
what the language is, and that the grammar can be read without
backtracking.

Hand back:

- each construct, with a line on what it means;
- every program at the end of this brief, written in the design;
- what was relaxed or left out, and why;
- what the design does badly.

Write the rest of each program, calls, lists, records and lambdas, in
whatever ordinary syntax reads best; the constructs for matching are what
is judged.

Prefer one idea used everywhere to a construct for each case, and
spellings readers already know to new ones, unless the new one is clearly
better.

### The language

- **Pure and strict.** Every expression is worked out before it is used,
  except the right operand of a logical and or or, which is worked out only
  where the left has not decided. Values have no identity: no references,
  no aliasing, no mutation a caller can see.
- **Effects are marked.** A function that performs effects is marked as
  one by its name, and each effectful call stands alone, at the start of a
  line, as what a line tests, or as a whole body, never inside an
  expression.
- **Failure is a value.** There are no exceptions. A computation that can
  fail answers a result, success or failure, whose failures are a union of
  tags the type system tracks; an operator passes a failure on to the
  caller.
- **Functions are second class.** A function may be passed to a call, never
  stored or returned. Lambdas exist, as arguments.
- **Definitions are clauses today.** A function is a list of clauses tried
  in order, each a pattern per parameter and an optional boolean guard;
  together they must cover every input. A clause is the program's only way
  to take a value apart that may not have the shape asked for.
- **Bindings are total.** A local binding takes a value apart only where
  the shape cannot fail, and may shadow an earlier name.
- **Patterns look like the expressions that build what they match.**

### The data

- **Named sums:** constructors with positional fields, recursive allowed,
  each type's constructors known.
- **Structural tag unions:** tags with fields, open or closed, the usual
  type of a failure.
- **Records:** structural, fields by name; a pattern may name some fields
  and leave the rest.
- **Tuples** of two or more.
- **Lists:** taken apart at the front, at the back, or both, around one
  rest.
- **Naturals,** inductive in principle, written as numerals; fixed-width
  integers, floats, characters and strings, matched by literal, and the
  ordered ones by an inclusive range open at either end.
- **Nominal wrappers:** a named type around one value, taken apart by its
  name.

### Goals

1. **Dispatch on parameters,** case by case, as clauses do now.
2. **Branch on a computed value** two ways, and many ways with every case
   covered and checked.
3. **Ask whether a value has a shape,** as a boolean value.
4. **Take a value apart where it cannot fail.**
5. **Take a value apart where it can,** binding its parts for what
   follows, or else leave: the function with an answer, a loop's round, or
   a loop.
6. **Leave early on a plain condition.**
7. **Combine tests and conditions,** a later one reading what an earlier
   one bound, short-circuiting.
8. **Test several values at once.**
9. **A default where a shape is missing.**
10. **Name a value and take it apart at once.**
11. **Compare with a name in scope** without binding a new one by mistake.
12. **Alternatives,** binding the same names, wherever a pattern stands.
13. **Loops** that take each element apart, and that take a worklist apart
    as they go round.
14. **Names seen exactly where their match is known to have held,** and a
    clear message where one is used beyond that.

### Qualities

- One way to write each thing; where two forms could do one job, a rule
  says which.
- A grammar decidable by the next token, with few keywords and no rule
  for one construct alone.
- Layout carries no meaning: no indentation rule.
- Every exit is written, and is easy to find when scanning a body.
- A body reads top to bottom, a step to a line, and nests shallowly;
  pulling a step out into a named helper stays cheap.
- Programs as short as their Python, or shorter.
- Mistakes the compiler can see are refused, with a message saying what to
  write instead.

### Non-goals

- Exceptions, and a general early return usable anywhere in an expression.
- Flow typing: a name's type does not change because of a test above it.
- Laziness beyond the logical operators.
- References, identity and mutation a caller can see.
- Indentation-sensitive layout.
- View patterns, active patterns, pattern synonyms, and splitting a
  condition from a shared prefix.
- Macros and operators a program defines.
- Syntax for choosing a value, such as a default operator: a method or a
  conditional does it. Syntax is for control flow and for binding names.
- A conditional answering nothing, and an exit not written as one.
- A shorthand that only saves writing a name twice.
- Checking a partial test for completeness: only a many-way match, and a
  function's clauses, must cover every case.

### Programs to try a design on

- **Drain a priority queue:** take the cheapest entry off, or answer the
  state when it is empty; visit it, add what the visit found, go round.
- **Walk back a path:** look up how a node was reached; unreachable fails,
  reached from itself ends the path, otherwise go on from its predecessor.
- **Tokenize:** many ways on a byte list's front: empty, a digit, a space
  to skip, any other byte.
- **Validate an identifier:** it begins with an underscore, the rest
  parses as a number, the number is below a bound; any failure is one
  error.
- **Merge two sorted lists,** passing the untouched list on whole.
- **Topological sort** over a graph giving node count, neighbors and
  in-degrees, failing on a cycle.
- **Evaluate an expression tree,** with several shapes that simplify to the
  same value, and a lookup of a variable that may be missing.
