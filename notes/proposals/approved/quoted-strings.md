# Proposal: A string inside a value is quoted

- **Status:** Approved
- **Created:** 2026-11-05
- **Approved:** 2026-11-05
- **Affects:** the standard library's `Str.to_str`, splices in the checker and
  specialization, the expectation runner, `notes/values/strings.md`, the
  standard library's README, every program printing a string inside a value

---

## Summary

A `Str`'s `to_str` writes it as a literal would, quoted and escaped. A
splice of a `Str` is still the string itself, decided once the splice's
type is known.

| Written                     | Before          | After             |
| --------------------------- | --------------- | ----------------- |
| `["a", "b, c"].to_str()`    | `[a, b, c]`     | `["a", "b, c"]`   |
| `Ok("").to_str()`           | `Ok()`          | `Ok("")`          |
| `(1, "a").to_str()`         | `(1, a)`        | `(1, "a")`        |
| `"a\tb".to_str()`           | the text itself | `"a\tb"`, escaped |
| `"${name}"`, a `Str`        | the text itself | the text itself   |
| A generic splice at a `Str` | the text itself | the text itself   |
| A runner answering `Ok(s)`  | `Ok(text)`      | `Ok("text")`      |

## Motivation

A value inside another is written by its own `to_str`, and a string was
written bare, so it could not be told from what surrounds it:
`["a", "b, c"]` and `["a", "b", "c"]` both printed `[a, b, c]`, `Ok("")`
printed `Ok()`, and a record holding `"x, y: 2"` printed as one with
another field. The tuples note said a tuple is written as it is written,
which held for every member but a string. A runner's `Ok(...)` is there to
say which way a program went, and is the text most programs print, so the
confusion reached most of them.

## Design

`Str.to_str` writes `"`, then each byte, then `"`: `"` as `\"`, `\` as
`\\`, a `$` followed by `{` as `\$`, `\n`, `\r`, `\t` and nought by their
escapes, any other byte below 32, and 127, as `\u{..}`, and every other byte
as it is. What it writes reads back as the same string. A `$` not opening a
splice is left alone, `"$5"`.

A splice the source writes, `${value}`, is the value's text: the value
itself where it is a `Str`, and its `to_str` otherwise. The resolver writes
a splice as a `to_str` call and marks the call; the checker types it as
before, so a generic splice still asks `to_str` through its `where` bound;
elaboration makes the marked call a splice; and specialization, once the
value's type is known, answers the value itself where it is a `Str`, as it
decides `&` on `Bool`. A width pads that text.

The structural and derived `to_str` of records, tuples and tags, and
`List`'s, ask each part's own `to_str`, so a string inside them is quoted.
The expectation runner's text is a `Str` already, and is spliced as one.

## Costs

`${x}` and `x.to_str()` differ for a `Str`, and only for a `Str`. A
definition writing its own `to_str` chooses: a splice for a part shown as
text, `"${degrees}°C"`, `to_str` for one shown as a value. clap's help
showed a default by its `to_str`, and now splices it, so `[default:
<stdout>]` stays unquoted.

A `Str`'s `to_str` now walks its bytes and builds a new string where it
answered the one it had.

## Alternatives considered

- **A second member for a value shown inside another,** Rust's `Debug`
  beside `Display`. Every type with `to_str` would need it too, a declared
  type's own `to_str` a matching one, and generic containers a bound on it:
  a second protocol for one type's sake.
- **Quoting only in the compiler-made `to_str`** of records, tuples and
  tags. `List` and `Result` are written in Faun and cannot ask whether an
  element is a `Str`, so a list of strings would stay ambiguous.
- **Deciding a splice where it is checked** rather than specialized. A
  generic definition splicing a value it was handed would quote a `Str`,
  and the runners, which splice what an app answers, would print a program
  answering a `Str` in quotes.
