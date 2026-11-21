# Operator precedence

How Faun groups an expression with more than one operator, the designs
other languages chose, the ones Faun considered, and why it settled where
it did. This note, written on 2026-11-21, records the decision; the rules
as they stand are owned by [operators](forms/operators.md#precedence).

## The aim

Faun wants as little syntax as it can have, and rules a reader can apply
the same way every time, or work out in their head without a table. For
precedence that means two things: every grouping the language makes for you
should be one most programmers already make, and where programmers
genuinely disagree, the language should ask rather than guess. A third
wish pulls against the second: a line should not be so noisy with
parentheses that it stops reading like the condition it is.

## The rule

Arithmetic as at school, then comparisons, then `&`, then `|`; and `^` must
be parenthesized beside `&` or `|`. Tightest first:

| Level | Operators                       | Example           |
| ----- | ------------------------------- | ----------------- |
| 1     | calls, `.member`, `?`           | `xs.len()`        |
| 2     | prefix `-` and `!`              | `!done`           |
| 3     | `*`, `/`, `%`                   | `i * 4 + 3`       |
| 4     | `+`, `-`                        | `i + 1 < n`       |
| 5     | comparisons, which do not chain | `x == 3 & y == 5` |
| 6     | `is`                            |                   |
| 7     | `&`                             | `a & b \| c`      |
| 8     | `\|`, and `^` with only itself  | `(a ^ b) & c`     |

So `x == 3 & y == 5` is `(x == 3) & (y == 5)`, `a & b | c` is
`(a & b) | c`, and `a ^ b & c` is refused with both groupings offered:

```text
error: `^` and `&` need parentheses together: write `(a ^ b) & c` or `a ^ (b & c)`
```

Each operator chains with itself, `a ^ b ^ c` among them; `a < b < c` is
refused, as it was.

Two things keep the table this short. Shifts, rotations, powers and
conversions are named methods, `x.shift_left(3)`, `2.pow(n)`,
`U64.of_nat(n)`, and a call binds tightest, so none of them has a place in
it. And `&`, `|` and `^` are each one method, `and`, `or` and `xor`, on
whatever type their left operand has: on `Bool` they are logic, on a word
they are bits, and the symbol means the same call either way.

## The space

| Language    | Bits vs `==`     | `&` vs `\|` | `^`       | Mixing          |
| ----------- | ---------------- | ----------- | --------- | --------------- |
| C, Java, JS | looser           | `&` first   | between   | allowed, warned |
| Rust        | tighter          | `&` first   | between   | allowed         |
| Go          | tighter          | `&` first   | with `\|` | allowed         |
| Python      | tighter          | `&` first   | between   | allowed         |
| Gleam, Roc  | no bit operators |             |           | named functions |
| Carbon      | ordered          | refused     | refused   | if unordered    |
| Pony, Pyret | none             | refused     | refused   | always refused  |

"Between" is between `&` and `|`. "Looser" means `a & b == c` is
`a & (b == c)`; "tighter", `(a & b) == c`. C and C++ compilers warn on some mixes
under `-Wall`; Carbon refuses a pair its partial order leaves unordered;
Pony and Pyret refuse any two different operators side by side.

Three things stand out. Languages agree that `&` binds before `|`, the
order Boolean algebra gives "and" and "or". They disagree about `^`:
`a | b ^ c` means one thing in C and another in Go. And the C trap,
`flags & 4 == 0` meaning `flags & (4 == 0)`, is common enough that GCC and
Clang warn on it under `-Wall`, as they warn on `&&` inside `||`, and that
Carbon's [precedence proposal](https://docs.carbon-lang.dev/proposals/p000555-operator-precedence.html)
names both as rules developers do not reliably remember. Carbon's answer is
a partial order: a rule only where "most or all developers" would
reliably remember it, and otherwise none, so the expression is refused;
when in doubt, leave the rule out, since one can be added later and not
easily taken away.

## What was considered

Counted over the repository's Faun code when the decision was made: about
450 lines join comparisons with `&` or `|`, about 75 use `&`, `|` or `^` on
bits, 17 mix `&` with `|`, and none mixes `^` with either.

- **C's order, as it was.** Bits looser than comparisons, `&` before `^`
  before `|`. A mask written without parentheses is a type error with a
  hint, not a silent wrong answer, which is better than C. But the order of
  `^` is one nobody remembers.
- **`&` and `|` for `Bool` only, bits as named methods**, as Gleam and Roc
  have no bit operators at all. It removes the mask trap outright and
  matches the shifts, which are already methods. Declined: `&` would stop
  being plain sugar for `.and()` on every type, an exception to a rule
  that otherwise has none.
- **A separate spelling for logic**, `&&` and `||` as in Rust or `and` and
  `or` as in Python, with the bit operators tighter than comparisons.
  Masks read naturally. Declined: a second spelling of one method, and
  every condition rewritten.
- **Every mix parenthesized**, as Pony and Pyret do. One rule with no
  table. Declined: `i * 4 + 3 < len` would become `((i * 4) + 3) < len`,
  noise for groupings nobody misreads.
- **A partial order with `&`, `|` and `^` unordered against comparisons.**
  The mask trap could not be written. Declined: since one `&` means both
  logic and bits, and the parser cannot tell which before types are
  known, every joined condition would need parentheses,
  `(x == 3) & (y == 5)`, about 270 lines.
- **Compare, then combine, with `&`, `|` and `^` unordered among
  themselves.** Carbon's design read onto Faun, whose `&` and `|` are its
  `and` and `or`. Built first, then relaxed: and-before-or is the one
  ordering among the three that languages agree on, and refusing it buys
  little, while a line such as MD5's `b & c | !b & d` reads naturally to
  anyone who knows it.
- **Compare, then combine; and before or; `^` unordered with both.** The
  rule above.

## Why this one

It is derivable: school arithmetic, then compare, then combine, and "and"
before "or" as in Boolean algebra. The only thing to remember is that
`^` has no place, and the compiler says so when it matters. Every grouping
the language makes for you is one the languages around it make too, and
the one they disagree on is the one it refuses.

It keeps lines quiet where they are most common. Conditions join
comparisons far more often than code masks bits, and they need no
parentheses. A mask needs them, `(flags & 4) == 0`, and forgetting them is
a type error that names the fix rather than a program that runs wrong.

## The risk taken

The rule leaves two groupings to the reader that a stricter one would ask
about:

- **And and or mixed in a condition.** `x == 0 | y == 1 & z == 2` is
  `x == 0 | (y == 1 & z == 2)`. That is the order Boolean algebra gives,
  but it is the mix GCC warns about, because someone sometimes means the
  other. Faun chose quiet lines over that warning.
- **A comparison of Booleans beside `&`, `|` or `^`.** Where every operand
  is a `Bool`, `a & b == c` is `a & (b == c)` and checks. It follows the
  rule, and comparing two Booleans with `==` is rare, but nothing flags it.

A [linter](lints.md) could flag both without the language refusing them.
The tree-sitter grammar keeps the order and accepts a `^` mixed with `&`
or `|`, so an editor does not underline it; the compiler refuses it.

## Related

- [Operators](forms/operators.md): operators as methods, and the rules as
  they stand
- [Syntax](forms/syntax.md): the grammar's goals
- [Lints](lints.md): what a linter should flag and the compiler leaves alone
- [Carbon: operator precedence](https://docs.carbon-lang.dev/proposals/p000555-operator-precedence.html)
- [Pony: operator precedence](https://tutorial.ponylang.io/expressions/ops)
