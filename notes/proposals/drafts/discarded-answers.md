# Proposal: An effect's answer is read or thrown away in so many words

- **Status:** Draft
- **Created:** 2026-10-04
- **Affects:** the checker, the generated expectation runner, every
  program that prints on a line of its own

---

## Summary

An effectful call already stands only at the top of a line: as a binding's
value, as a line of its own, or as a body, its arguments pure. The checker
refuses one inside an argument, an operand or a guard
(`validate_effect_expr` in `check.rs`). What it does not refuse is an
effect on a line of its own whose answer is more than `{}`, which is thrown
away unread. This proposal refuses that too: such an answer is bound, or
thrown away with `_ = call!(…)`.

| Where                    | Today   | Proposed |
| ------------------------ | ------- | -------- |
| `text = file.read!()`    | allowed | allowed  |
| `log!(text)` alone, `{}` | allowed | allowed  |
| `file.read!()` alone     | allowed | refused  |
| `_ = file.read!()`       | allowed | allowed  |
| `f(file.read!())`        | refused | refused  |
| `a!() & b!()`            | refused | refused  |

## Motivation

- **An `Err` is lost without a word.** `host.stdin.read_to_end!()` on a
  line of its own answers a `Result` nothing reads: a failed read, or a
  failed write, goes by unseen. The rest of the language makes a caller
  handle an `Err`, through its type; a line that drops one undoes that.
- **What a line does should be read off it.** A line that is only an effect
  says it is asked for what it does. Where it also answers something, the
  reader cannot tell from the line whether dropping that was meant.
- **Effects already stand one to a line.** Every effectful call is already
  at the top of a line, so evaluation order inside an expression cannot be
  seen; this finishes the rule for the one form of line it leaves open.

## Design

- **An effect alone on a line answers `{}`,** or `[]` where it does not
  come back. One answering anything else is refused, the message showing
  what it answers.
- **`_ = call!(…)`** throws an answer away in so many words, as a binding
  to `_` already does.
- **An answer whose type is not yet known** is not refused.
- **Printing is no exception.** `print!` answers whether the write went
  through, and a program that does not care says so with `_ =`, as any
  other.

## Costs

- **`_ =` before every dropped print.** `print!`, `println!` and `write!`
  answer a `Result`, since a write can fail. Eleven lines in the corpus
  call one on a line of its own, in the hello examples and in programs the
  Rust tests write, and the runner `faun test` generates for expectations
  is a twelfth. Built on 2026-10-04, the rule refused about forty tests,
  nearly all through that one generated line.
- **A line longer by four characters** wherever a program means to ignore
  a failure. That is the point: the ignoring is written down.

## Alternatives considered

- **Leave it.** A dropped `Err` stays silent, as it is today.
- **Printing answers `{}`,** the host ending the program on a failed
  write, as Python does on a broken pipe. Every print line stays as
  written, but printing would be the one effect whose failure no program
  can see or answer, and a program writing a report it must not lose
  could not tell it was lost.
- **A warning, not a refusal.** Faun has no warnings; every diagnostic
  refuses.

## Implementation impact

1. **The checker.** A body's line records that it was written alone, and
   is refused where its answer is more than `{}` or `[]`. A sketch built on
   2026-10-04 carried a `discarded` flag from the syntax tree into the HIR's
   bindings and checked it after each binding's type settled.
2. **The expectation runner** in `expectations.rs` binds what its
   printing answers to `_`.
3. **Programs.** `_ =` before each of the eleven printing lines.

## Testing

- A refused case with its `.err`: `host.stdin.read_to_end!()` alone on a
  line.
- `_ = host.stdin.read_to_end!()` is accepted.
- The examples and libraries pass, with `_ =` where they print on a line
  of their own.

## Origin

Settling whether `&` on `Bool` should short-circuit (2026-10-04) led to
writing down that effects stand one to a line. Adding refused cases for
that rule showed it was already enforced, all but this one form: building
it refused every program that prints on a line of its own.
