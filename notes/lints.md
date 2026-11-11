# Lints

What a linter should flag, and the compiler leaves alone. The compiler
refuses what has no meaning, or one a reader would misread; a lint flags
what means one thing plainly but is likely a slip, or is better written
another way. No linter is built yet. This list gathers what the design
notes left to one, so none is lost.

## Likely slips

- **An unused binding.** It catches a typo that makes a new name,
  `totl = total + 1`, since binding again is a binding, and a body ending
  in a binding by mistake, which answers `{}` where nothing declares what
  it answers.
- **`x = x`,** a binding to itself.
- **A test that always holds,** `n is _`, or `n is m` binding `m`.
- **Lines no path reaches,** after an unconditional leave.
- **An effect's answer dropped** where it is a `Result`: a `write!(…)` on
  a line of its own, neither bound nor passed on with `?`. See
  [effects](forms/effects.md#why-not-refuse-an-effects-answer-dropped-on-a-line-of-its-own).
- **A clause or arm no value reaches,** one after others that already
  cover every value, `area(_) -> 1` after `area(Dot)` and `area(Square(n))`,
  or one an earlier catch-all covers. Rust, OCaml and Haskell warn of it;
  the compiler, which has no warnings, accepts it.
- **A file name some host cannot create,** `CON`, `aux.txt`, a trailing
  dot, warned about on every host. See [files](effects/files.md).

## Forms with a plainer spelling

- **`x is 3`,** written `x == 3`.
- **A two-arm `is` ending in `_`,** written as an `if`.
- **An `else` line before a block's last line,** where the rest is one
  value, written as a ternary.
- **A many-way `is` on a bare parameter,** written as clauses.
- **A walk that is a method already,** a recursion over a list that is
  `sum`, `map`, `find`, `count`, `fold` or `fold_until`.
- **A conversion where a numeral would do,** `Int.of_nat(3)` where the
  type is known, written `3`.
- **Redundant parentheses,** and a doubled prefix, `!!c` or `--x`.
- **A ternary as a condition,** `if if a then b else c then …`, which
  reads but should be parenthesized.

## Style

- **Recursion nesting,** walks inside walks past a depth a style chooses.
  The compiler refuses no depth.
