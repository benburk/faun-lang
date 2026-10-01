# Proposal: Blocks

- **Status:** Approved
- **Created:** 2026-09-29
- **Approved:** 2026-09-29
- **Affects:** the lexer, `grammar.ebnf`, the parser, grouping lines into
  items (`lines.rs`), which goes, the tree-sitter grammar, every body of more
  than one line, every `where` list of more than one line

---

## Summary

A clause maps a pattern to an expression, and an expression may be a block:
bindings, then the answer, in parentheses. A body of more than one line is
then a block, where today it is the lines after the clause's `->`. A body of
one expression is written as it is now. A `where` list's constraints are
parted by commas, where today each is a line of its own. With both, the
parser makes items directly, and the pass that groups lines into items goes.

| Form                   | Today                | Proposed                     |
| ---------------------- | -------------------- | ---------------------------- |
| Body of one expression | `f(x) -> x + 1`      | unchanged                    |
| Body with bindings     | the lines after `->` | `-> (`, the lines, `)`       |
| Lambda body            | one expression       | an expression or a block     |
| Grouping               | `(a)`                | `(a)`, a block of one line   |
| Tuple                  | `(a, b)`             | `(a, b)`                     |
| Alias with parameters  | not possible         | `Edge(e) = {target: Nat, …}` |
| `where` list           | a line per bound     | commas between bounds        |

```ruby
# Today
relax(search, from, candidate, target) ->
  entry = Queued(candidate, target, Empty, Empty)
  {queue: meld(search.queue, entry), *search}

# Proposed
relax(search, from, candidate, target) -> (
  entry = Queued(candidate, target, Empty, Empty)
  {queue: meld(search.queue, entry), *search}
)

# Unchanged: a body of one expression needs no parentheses
node_count(Graph({adjacency, *})) -> adjacency.len()

# New: a lambda with a body
edges.fold(state, |inner, edge| (
  target = edge.target
  discover(target, inner)
))
```

## Motivation

- **It generalizes what is there.** A clause is `pattern -> expression`, and
  nothing more. Parentheses already group; a block with no bindings is a
  grouping, `(a)`, and a tuple needs two members, `(a, b)`, so after the
  first expression the next token says which of the three it is.
- **Lambdas get bodies.** A lambda's body is one expression today, so a
  callback that needs an intermediate value becomes a named helper. The graph
  library (`crates/faun/examples/libraries/graph`) has `relax`, `discover` and
  `gather` partly for that reason. People will want lambdas with bodies
  whatever else is decided.
- **Scope is written.** A block's bindings are seen by its later lines and
  its answer, and nowhere else, so a nested block can group a calculation
  and its names leave with it. Rebinding a name in a body already works
  (`y = y * 2`); a block limits how far the new binding reaches.
- **The body is a thing an editor can select.** Visual-select-inside-parens
  takes a whole body, and tree-sitter gets a body node to fold and select.
- **It fixes type aliases with parameters.** `Edge(e) = {target: Nat,
  weight: e}` does not parse, and cannot as the syntax stands. With blocks it
  can, below.
- **One body of one expression stays bare.** The parentheses are paid only
  where a body has bindings.
- **The parser makes items.** Today the grammar reads a file as a flat list
  of lines, and a second pass decides which lines are whose. With blocks and
  comma-separated `where` lists, every item is whole when the parser reads
  it, and the grammar describes the program rather than its lines.

### The second pass

The grammar is LL(1) today, and `the_grammar_is_ll1_and_every_rule_is_used`
(`crates/faun/src/ebnf.rs`) holds it to that. What it describes is a file of
lines: which lines are a body, and which a signature's constraints, is
decided after it, by grouping (`crates/faun/src/lines.rs`). That pass does
six things:

| What grouping does                          | With this proposal         |
| ------------------------------------------- | -------------------------- |
| Gives a clause or `expect` its body's lines | the block holds them       |
| "this line belongs to no definition"        | a syntax error             |
| "a body ends with its answer"               | a syntax error             |
| Gives a signature its `where` lines         | the commas hold them       |
| Makes a head a pattern, a name or a type    | the parser, at `->` or `:` |
| Refuses a value thrown away                 | stays a check              |

A head is read as an expression and made a pattern afterwards under any
LL(1) grammar for this syntax: `f(x)` may be a call or a clause's head, and
only the `->`, `:` or `=` after it says which, as only the `=>` says a
JavaScript arrow function's parameters are not an expression. But that
conversion is of one line, and the parser can make it the moment the
deciding token arrives. It is not a pass over the file.

### The alias problem

The grammar is LL(1) and ignores indentation (`notes/syntax.md`), and a body
is the lines after its clause's `->`. A body line
`Read(value, rest) = parser(input)?` is a binding, and has the same tokens as
an alias's head and `=`.

A body is not simply bindings and then one answer, which would say where it
ends. An effect call may stand on a line of its own anywhere in it:

```ruby
main!(host) ->
  host.println!("first")
  Pair(a, b) = Pair(1, 2)
  host.exit!(U8.of_nat(a + b))
```

So after a body whose last line is an effect call, the next line is a
binding in that body or an alias, and only indentation tells which:

```ruby
main!(host) ->
  host.exit!(0)
Edge(e) = {target: Nat, weight: e}
```

With blocks, the top level holds no bindings. `Edge(e) = …` there is always
an alias, and inside parentheses always a binding.

## Design

- **Syntax.** `block = "(" statement { NEWLINE statement } ")"`, where a
  statement is `expr [ "=" expr ]` and the last is not a binding. After `(`
  and one expression, the next token decides: `=` is a binding, `,` a tuple,
  `)` a grouping, and a line end the next line of a block. The grammar stays
  LL(1).
- **Lines.** A line break inside a plain `(` ends a line as one does at the
  top level, as it already does inside a method block's `.(`. A call's `(`,
  a list and a record keep spanning lines freely. A line still runs on after
  `->`, `=`, a comma or an operator, and into a next line beginning `.`, an
  infix operator, `where` or `if`. No semicolons: a line end separates, as
  it does between items.
- **Answers.** A block's value is its last line. A line that is neither a
  binding nor the last must be an effect call; a value worked out and thrown
  away is refused, as now.
- **`?`** answers early from the clause or lambda it is written in, not from
  the block: a block is not a function.
- **Where blocks go.** Anywhere an expression goes, with no rule of their
  own anywhere: a clause's body, a lambda's body, an argument, a binding's
  value, an `expect`, and a guard. An expectation of several lines is a
  block, `expect (` … `)`, as a clause's body is. A guard may be a block
  because a guard is an expression, and nothing more is made of it.
- **Style.** The `(` ends the line that opens the block, its lines are
  indented one step, and the `)` stands on a line of its own at the
  indentation of the line that opened it:

  ```ruby
  expect (
    (found, _) = Lru.empty(2).put(1, "one").get(1)
    found == Ok("one")
  )
  ```

  The grammar ignores indentation, so this is the formatter's rule and not
  the parser's. Where two blocks close together, as a lambda's inside a
  call, each `)` keeps its opener's indentation: `))` only where both
  opened on one line.
- **Method blocks.** `.(` … `)` is unchanged; it holds signatures and
  clauses, not statements.
- **The top level.** Lines there are items: directives, signatures, data
  declarations, aliases, clauses and `expect`s. A binding there is a syntax
  error, where today the grouping step refuses it.
- **`where` lists.** Constraints are parted by commas, member constraints as
  alias constraints already are: `where a.zero : a, a.add : (a, a) -> a`. A
  comma never ends a line, so a list of one constraint per line is one
  line to the lexer:

  ```ruby
  sum : List(a) -> a where
    a.zero : a,
    a.add : (a, a) -> a
  ```

  The last constraint takes no trailing comma, since the line would run on
  into the next item. After a member constraint's type, `,` is the next
  constraint and anything else ends the list, so the grammar stays LL(1).
- **Type aliases with parameters.** `Name(a, b) = type` at the top level,
  resolved as `Hasher(h) = where …` constraint aliases are: always applied
  to as many arguments as it has parameters, no variable in the type but its
  parameters, every parameter used (a transparent alias cannot carry a
  phantom type), and no alias naming itself, directly or through another.

## Costs

- **Every multi-line body changes.** 536 of about 3,165 clauses in the 240
  `.fn` files, and about 50 bodies in the Rust tests. Each gains `(` after
  its `->` and a closing `)`, which in practice is an extra line.
- **A missing `)` can reach far.** A flat line recovers at the next line. An
  unclosed block could run to the end of the file. A clause's `->` never
  appears inside a block, so meeting one there is where to report the
  unclosed `(`.
- **The closing parenthesis is ceremony.** Ori's approved block proposal
  (below) replaced `run(a, b)`, a parenthesized block with commas, calling it
  "the most-typed construct in Ori" and its closing parenthesis "visual
  noise without semantic value". Faun's block has no keyword and no commas,
  so what is left of that complaint is the `)` itself, one per multi-line
  body.
- **Every multi-line `where` list changes.** 60 signatures and 8 constraint
  aliases in the `.fn` files, and 6 in the Rust tests, each gaining a comma
  after every constraint but its last.
- **A trailing comma after the last constraint** joins the next item onto
  the list, and is refused there, as an error about that item. The
  message should say where the list was left open.
- **One meaning changes.** Inside plain parentheses, `(a` then `-b` on the
  next line is `a - b` today, and would be two lines of a block, the first
  thrown away and refused. Top-level lines already read `-b` this way, and a
  spaced `- b` stays a subtraction in both. Every other token that would now
  begin a line inside parentheses is a syntax error there today (tried with
  names, numerals, strings, characters, `(`, `[`, `{`, `!`, `_` and
  constructors), so nothing else that parses changes meaning.

## Alternatives considered

- **Ori's `{ }` blocks.** Ori's
  [block-expression-syntax](https://github.com/upstat-io/ori-lang/blob/master/docs/ori_lang/proposals/approved/block-expression-syntax.md)
  proposal made `{ let $x = 1; x + 2 }` a block, with semicolons ending
  statements and the last expression without one as the value. Faun cannot
  use braces: `{x}` is a record punning `x`, and Ori needs up to two tokens of
  lookahead and a table of rules to tell its blocks from its maps and
  structs. Parentheses carry no such ambiguity, and newlines already separate
  lines, so Faun needs no semicolons.
- **Decide at grouping, from the next line.** After a binding or an effect
  line, a run of `Type(a) = …` lines is bindings when more of the body
  follows, and aliases when an item or the end of the file does. The right
  side is read as an expression and turned into a type, as expressions are
  turned into patterns. No grammar changes, but a function type is not an
  expression, the rule is invisible to the grammar files, and tree-sitter
  reads such an alias as a binding. It fixes aliases and nothing else.
- **Parameters after the `=`:** `Edge = |e| {target: Nat, weight: e}`.
  Unambiguous, but unlike every other declaration's head.
- **A keyword:** `type Edge(e) = {…}`. Familiar from Rust, Haskell and
  TypeScript; costs a keyword, and plain aliases would take it too.
- **An operator:** `Edge(e) := {…}`. A new token, and unlike
  `Hasher(h) = where`.
- **Layout.** A line at column 0 is an item. `notes/syntax.md` rules it out.

## Implementation impact

1. **Blocks.** The lexer gives a plain `(` line ends, as `.(` has. The
   parser reads a block as an expression, and a clause's body as one
   expression. `grammar.ebnf` and the tree-sitter grammar gain the block
   rule and lose bodies as the lines after a clause. Grouping lines into
   items loses its open body, and the errors "this line belongs to no
   definition" and "a body ends in a binding" become syntax errors where the
   mistake is.
2. **`where` lists.** The grammar reads a comma after a member constraint,
   and grouping loses its `where` lines. What is left of `lines.rs` is
   making a head a pattern, a name or a type, which the parser calls as it
   reads each item; the pass itself goes.
3. **Migration.** A script rewrites every `.fn` file and the Rust tests'
   programs, using today's parser for where each body and each `where` list
   ends.
4. **Aliases with parameters.** Resolution only: the grammar reads them once
   blocks are in.
5. **Documentation.** `notes/syntax.md`, the standard library README, and the
   language tests.

## Testing

- `crates/faun/src/ebnf.rs` holds `grammar.ebnf` to the parser, on every
  program and on probes for: a block, a grouping and a tuple after `(`; a
  block whose last line is a binding; `->` inside a block; a binding at the
  top level; `(a` then `-b`; a `where` list parted by commas, on one line and
  on several; and one ending in a comma.
- Refused cases, each with its `.err`: a block ending in a binding, an
  unclosed block, an alias using a variable it does not declare, an alias
  with a parameter it does not use, an alias naming itself, and an alias
  given the wrong number of arguments.
- A running case in the language tests: a lambda with a block, a nested
  block whose names do not leak, a `?` inside a block answering the clause,
  an `expect` block, a guard that is a block, and an alias with parameters
  used at two types.
- `just test` reads every program with the parser, the grammar and
  tree-sitter after the migration.

## Origin

Writing a graph library (`crates/faun/examples/libraries/graph`) wanted an
edge type, `Edge(e) = {target: Nat, weight: e}`, which does not parse.
Finding why led to the effect-line ambiguity above, and to blocks as the fix
that also gives lambdas bodies.

## Errata (added 2026-09-29)

Settled while building it:

- **A thrown-away value is refused after parsing, not by it.** Whether a
  line is an effect call depends on the name it calls, which the grammar
  does not see, so `grammar.ebnf` reads such a block and the items step
  refuses it, as it did a body's.
- **Refused syntax is not a case in `crates/cli/tests/refused/`.** Every
  program in the repository parses, by the parser, the grammar and
  tree-sitter alike. A block ending in a binding, an unclosed block, a body
  of several lines without its block and a `where` list ending in a comma
  are tested as the parser's own tests (`crates/faun/src/tests.rs`), the
  grammar's probes (`ebnf.rs`) and tree-sitter's refused corpus.
- **An unclosed block is told at its `(`,** where a line in it runs into a
  clause's `->` or a signature's `:`, neither of which a block holds.
- **A closing bracket never begins a line**, in the lexer and in
  tree-sitter's scanner, so a block's `)` on a line of its own ends it
  without a line end before it.
- **Lines are still made into items by `lines.rs`**, one line to one item:
  heads become patterns, names and types there. Nothing is grouped.
- **A nested block's bindings are taken out ahead of the expression it
  stands in** by pattern compiling, as a `?` is, and a guard's condition is
  compiled as a body so a guard may be a block. No pass after pattern
  compiling sees a block.
- **The standard library's `where` lists** were one constraint to a line
  and became comma-separated with the rest of the migration.
