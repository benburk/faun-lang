# Proposal: An effect's answer is read or thrown away in so many words

- **Status:** Draft
- **Created:** 2026-10-04
- **Affects:** the checker, the hosts' printing effects, the generated
  expectation runner, every program that prints on a line of its own

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

## Costs

Built and run on 2026-10-04, the rule refused about forty tests' programs.
Nearly all are printing:

- **`print!`, `println!` and `write!` answer a `Result`,** since a write can
  fail, and programs call them on lines of their own: three examples, the
  hosts' own code, and the runner `faun test` generates for expectations.
- **Each would need `_ =`,** or the hosts' printing effects would answer
  `{}` and handle a failed write themselves.

## Alternatives considered

- **Leave it.** A dropped `Err` stays silent, as it is today.
- **Printing answers `{}`.** A failed write to standard output is rarely
  something a program can act on; the host could end the program, as
  Python's does on a broken pipe, and every print line stays as written.
  Writes to files would still answer a `Result`, and be refused when
  dropped.
- **A warning, not a refusal.** Faun has no warnings; every diagnostic
  refuses.

## Implementation impact

1. **The checker.** A body's line records that it was written alone, and
   is refused where its answer is more than `{}` or `[]`. A sketch built on
   2026-10-04 carried a `discarded` flag from the syntax tree into the HIR's
   bindings and checked it after each binding's type settled.
2. **The hosts and the expectation runner** bind or throw away what their
   printing answers, or printing answers `{}`.
3. **Programs.** Each printing line, as the open question decides.

## Testing

- A refused case with its `.err`: `host.stdin.read_to_end!()` alone on a
  line.
- `_ = host.stdin.read_to_end!()` is accepted.
- The examples and libraries pass, changed as decided.

## Open questions

- **Printing.** `_ =` on every print line, or printing that answers `{}`
  and handles its own failure?

## Origin

Settling whether `&` on `Bool` should short-circuit (2026-10-04) led to
writing down that effects stand one to a line. Adding refused cases for
that rule showed it was already enforced, all but this one form: building
it refused every program that prints on a line of its own.
