# Proposal: Values

- **Status:** Approved
- **Created:** 2026-10-02
- **Approved:** 2026-10-02
- **Affects:** `grammar.ebnf`, the parser, grouping lines into items
  (`lines.rs`), name resolution, the checker's `where` bounds, the
  tree-sitter grammar, every definition of no parameters and every use of
  one

---

## Summary

A definition of no parameters is a value: it is written `name = value`, and
used by its name alone. `name() -> value` is refused, and so is calling a
value.

| Form              | Before                | After             |
| ----------------- | --------------------- | ----------------- |
| A top-level value | `pi() -> 3.14159`     | `pi = 3.14159`    |
| A type's value    | `zero() -> Vec3(…)`   | `zero = Vec3(…)`  |
| Using one         | `pi()`, `Vec3.zero()` | `pi`, `Vec3.zero` |
| A bound's value   | `a.zero()`            | `a.zero`          |
| Its signature     | `pi : F64`            | unchanged         |

## Motivation

The corpus had 178 definitions of no parameters, in 59 files: constants
(`solar_mass`, `mask`, `race_length`), test inputs (`example`), and each
type's `zero`, `empty`, `pi` and `nan`. Each is a value, but was written and
used as a function: `()` at every use, and a definition whose head names
parameters it does not have. Nothing else in the language is a function of
nothing: a lambda takes at least one parameter, and a function type at least
one type.

## Design

- **Syntax.** A line that is a lowercase name, `=` and an expression defines
  a value, at the top level or in a type's method block:

  ```
  line = … | ( NAME | EFFECT ) [ call ] ( ":" typed | clause | "=" expr ) ;
  ```

  After the head, `=` cannot go on with an expression, so the grammar stays
  LL(1). A line goes on after `=` as it does after `->`, so a value's
  expression may start on the next line. A signature stays optional and is
  written as before.
- **The head is one name.** A pattern, `(a, b) = …`, is refused, and so is
  an effect's name: a value is no effect.
- **A use is the name.** `pi`, `Vec3.zero`, and `a.zero` where a `where`
  bound gives `a.zero : a`. `pi()`, `Vec3.zero()` and `a.zero()` are
  refused, saying to drop the parentheses.
- **`name() -> …` is refused,** saying to write `name = …`.
- **Meaning.** Nothing changes below resolution: a value is still a
  definition of no parameters, and a use is a call of it. Faun is pure, so
  whether a value is worked out once or at each use cannot be told, and
  Barb already shares repeated calls of answered definitions.

## Costs

- **Every program.** 178 definitions and their uses changed. A script did
  it; the type-qualified uses needed the list of types' values, since
  `False.not()` is a method call on a constructor, not a value.
- **A value cannot be a function.** `f = |x| x` does not parse, since a
  lambda is written only as an argument, and `f = g` is refused as binding a
  function always was.

## Alternatives considered

- **Keep `name()`.** Costs `()` at every use of every constant and reads as
  a function of nothing.
- **Allow both.** Two spellings of one thing; the change is small enough to
  make whole.
- **Values worked out once at load.** No different in meaning, and a
  compile-time constant is already folded.

## Implementation impact

1. **The parser** reads `name = value` as a line (`Line::Value`), and
   `lines.rs` makes it a clause of no patterns, refusing a clause of no
   patterns written `name()`.
2. **Resolution** collects every definition of no patterns across the
   program, resolves a bare use of one as a call with no arguments, and
   refuses a call written on one.
3. **The checker** reads a bare `a.zero` as the bound's value, and refuses
   `a.zero()`.
4. **The tree-sitter grammar** gains `value`, highlighted as a constant.
5. **Every program,** the standard library, the libraries and examples,
   and the sources the Rust tests write.

## Testing

Refused cases for `name() -> …`, `zero()`, `Map.empty()` and `a.zero()`;
parser tests for a value and for a pattern or a type name before `=`; the
grammar tests reading `name = value` at the top level and in a method
block; and every example and test program, across all three backends,
written with values.

## Origin

Asked while comparing n-body with the branching draft: its `solar_mass`,
`days_per_year`, `bodies` and `system` are constants, and were written and
used as functions.
