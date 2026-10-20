# Grammar audit

As of 2026-10-09, after `is`, arms, leaving lines, loops and the prefix
rule went in. The question: does the grammar stay simple, unambiguous and
LL(1), with no edge cases a reader trips on?

## What holds

- **LL(1).** `grammar.ebnf` is checked LL(1), every rule used, by the
  `ebnf` tests, which also check that it reads and refuses what the parser
  does on each probe.
- **Space never chooses between two readings.** It decides only whether a
  spelling is valid: what binds touches what it binds, and infix stands
  apart. A call's `(`, `.`, `..`, `.*`, `?`, a prefix `-` or `!`, a rest's
  `*` and a pattern's `==` touch; `f (x)`, `x .y`, `x -3`, `! x`, `[a, *
  rest]`, `a *b` and `a ==b` are refused, each saying how to write it.
- **Every construct puts a word between its head and its body:** `->` a
  clause's and an arm's, `then` and `else` a branch's, `do` a loop's, and
  the leave itself a leaving line's.
- **A body leaves only by a leaving line,** `if c return x` or `c else
  return x`, and `return`, `continue` and `break` stand nowhere else.

## Tokens read more than one way

Each is decided by position or the next token, never by context the parser
cannot see.

- **`(`:** a call, a group, a tuple, a block, or arms. Touching an
  operand, a call; otherwise the token after its first line says which.
- **`if`:** the ternary, a leaving line, a clause's guard, an arm's guard.
  The token after its condition, and where it stands.
- **`else`:** the ternary's, or a line's. A ternary takes its own, so the
  next is the line's.
- **`|`:** the `Bool` or, pattern alternatives, a lambda's bars. A lambda
  only opens an argument, and alternatives in a test are parenthesized.
- **`-`:** negation, or subtraction. Touching its operand, or with a value
  before it.
- **`*`:** multiplication, or a list's or record's rest. A rest only begins
  an element, touching what it takes.
- **`==`:** a comparison, or a pattern's `==name`, which only begins an
  operand.
- **`is`:** a test, or inside a pattern the whole and its parts.
- **`->`:** a clause's, an arm's, or a function type's: where it stands.

## Line breaks

A line break ends a line, at line level (outside brackets but a block's `(`
and a method block's `.(`), where the token before can end a line and the
one after cannot continue one. A line ending in an operator, `=`, `->`, a
comma or an opening bracket runs on; so does one followed by a line
beginning with a closing bracket, `.`, `?`, `->`, `then`, `else`, `where` or
a spaced infix operator.

- **`if` at the start of a line** continues the clause above as its guard
  where items are written, and begins an `if` in a block. The lexer reads
  this from the bracket it is in. It is context, but a block holds no
  clauses, so the two never meet.

## Told after parsing, not by the grammar

- **What only a pattern holds,** `_`, a range, `==name`, a list's end: read
  as expressions, refused where a line says they are not a pattern.
- **Arms only after `is`.**
- **`continue` and `break` only in a loop's body.**
- **A block's last line is its answer.** A block's lines and a loop's
  body's are one rule; where the last is a binding, a leaving line or a
  loop, a block answers `{}` where the round would go on (2026-10-18;
  until then it was refused).
- **A tuple's member and an arm's pattern are values.** A parenthesis's
  first line is any block line; a binding, a leaving line or a loop before
  a `,` or `->` is refused.
- **The parser's own refusals** beyond the grammar: an `is` tested again or
  compared, an `if` as an operand, `expect` in a body, a one-member tuple,
  a block never closed.

## Findings

1. **`*` was not held to the prefix rule:** `[a, * rest]` was accepted,
   and `[a *b]` read as `a * b`, though it looks like a rest. Resolved
   2026-10-09: a rest touches what it takes, as a prefix `-` does, and `a
   *b` is refused.
2. **`if a then b else c else return 0`** parsed, as a ternary on a line
   whose `else` leaves, two `else`s meaning two things. Resolved
   2026-10-10 in the grammar, which got smaller: a line beginning with a
   ternary takes no `=` and no `else`, and `(if a then b else c) else
   return 0` says it. A binding's `else`, `w = if x then y else z else
   return 0`, is refused with a message of its own.
3. **Three readings of `|`.** Each is decided by position, but a reader
   learns three. Word operators, `and` and `or`, would free `|` for
   alternatives; the conditions draft considered and declined them, since
   every `Bool` expression would change.
4. **Paired rules.** `operand` and `untyped-operand`, `primary` and
   `untyped-primary`, differed only in a type's name, which begins a type's
   line at the top level. Resolved 2026-10-13: a line begins with the name
   it defines and its arguments, as every program wrote it, so the copies
   went and `(f) = 3`, read before as defining `f`, is refused.
5. **`clause` and `arm-tail`** were one rule written twice. Resolved
   2026-10-10: an arm is an expression and a clause.

What reads but is better written another way, `if if …` or `!!c`, is a
linter's to flag: see [lints](lints.md).
