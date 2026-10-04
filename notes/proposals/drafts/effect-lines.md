# Proposal: Effects one to a line

- **Status:** Draft
- **Created:** 2026-10-04
- **Affects:** the checker, the language tests

---

## Summary

An effectful call, one whose name ends in `!`, stands only at the top of a
line: as a binding's value, as a line of its own, or as a body. Its
arguments are pure. No operator, condition, argument or pattern test holds
one. A block's effects then happen in the order of its lines, one to a
line.

| Where                   | Today   | Proposed                |
| ----------------------- | ------- | ----------------------- |
| `text = file.read!()`   | allowed | allowed                 |
| `log!(text)` alone      | allowed | allowed, answering `{}` |
| `-> host.run!(app)`     | allowed | allowed                 |
| `f(file.read!())`       | allowed | refused                 |
| `a!() & b!()`           | allowed | refused                 |
| `file.read!() is Ok(t)` | —       | refused                 |

## Motivation

- **Order should be read off the lines.** Where an effect may stand inside
  an expression, which of two runs first is a question about evaluation
  order: argument order, operator order, whether an `&` short-circuits.
  Where each stands alone at the top of its line, a block reads top to
  bottom as what happens.
- **Pure expressions stay pure.** With no effect inside an expression, the
  order an expression is evaluated in cannot be seen, except by not
  terminating. The compiler may evaluate it in whatever order is fastest,
  and `&` may short-circuit or not with nothing to tell.
- **It costs no program.** Every effectful call in the examples, the
  libraries and the standard library already stands this way: a binding's
  value, as `input = host.stdin.read_to_end!()`; a block's last line, as
  `host.exit!(status)`; or a clause's answer, as `main!(host) ->
  host.run!(app)`. Their arguments are pure.

## Design

- **Where an effectful call may stand:**
  - as a binding's value, `pattern = call!(…)`, with `?` after it or not;
  - as a block line of its own;
  - as a body: a clause's, a lambda's, a branch's.
- **Its arguments are pure:** no argument holds an effectful call.
- **Nowhere else.** An operand, an argument, a condition, an `is`'s value,
  a guard, a record's or list's element: none holds one. The refusal says
  to bind the call's answer to a name on the line before.
- **A call alone on a line answers `{}`.** One answering anything else is
  bound, and `_ = call!(…)` throws its answer away in so many words.
- **A branch's body may be one**, since a branch runs one body: which
  effect happens is chosen, and when is still the line it stands on.

Reading in a loop, where the test needs what the effect answered, binds
first and tests on the next line:

```
loop (
  chunk = input.read!()
  chunk is Ok(bytes) else break
  …
)
```

## Costs

- **A line per effect.** `f(file.read!())` becomes a binding and a call.
  This is already the corpus's style.
- **The loop and a half.** A loop testing what an effect answers cannot
  test it in its head, and writes the effect as its body's first line.

## Alternatives considered

- **Effects anywhere, evaluated left to right.** Order is then defined, but
  read from inside expressions, and every pure expression's order is fixed
  with it.
- **Effects in conditions only,** for `while input.read!() is Ok(b)`, as
  Python's `:=` allows. The one place it helps is the loop and a half,
  which `loop` with an `else break` line writes plainly.

## Implementation impact

1. **The checker** refuses an effectful call where it may not stand, and
   one alone on a line whose answer is not `{}`.
2. **Tests.** Refused cases for each place, each with its `.err`.
3. **Documentation.** The standard library README's effects section.

## Testing

- Refused cases, each with its `.err`: an effectful call as an argument,
  as an operand of `&`, in a guard, as an `is`'s value, and alone on a
  line answering something other than `{}`.
- The examples and libraries pass unchanged.

## Origin

Settling whether `&` on `Bool` should short-circuit (2026-10-04): with
effects inside expressions the answer can be seen; without them it
cannot, and the corpus already writes none there.
