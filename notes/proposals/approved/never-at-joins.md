# Proposal: A path that never answers fits any join

- **Status:** Approved
- **Created:** 2026-11-04
- **Approved:** 2026-11-04
- **Affects:** the checker's joins (`if`, arms, `return`), `notes/types.md`,
  the refused programs

---

## Summary

`[]`, the tag row with no tags, is the type of what never answers:
`exit! : (Host, U8) -> []`, and `main!` answers it. Where paths join, one
whose type is `[]` now takes the type the others answer, and where every
path is `[]`, so is the whole.

| Written                                       | Before  | After      |
| --------------------------------------------- | ------- | ---------- |
| `if ok then 3 else host.exit!(2)`             | refused | a `Nat`    |
| `Ok(v) then v` / `Err(_) then host.exit!(1)`  | refused | `v`'s type |
| `… else return host.exit!(2)` in a `Nat` body | refused | accepted   |
| `bad : Nat -> []` answering `3`               | refused | refused    |

## Motivation

A program that cannot go on says so and exits, and it does that in a branch
or an arm beside the paths that do go on. Each of these was refused, since
the checker unifies the paths of a join, and unifying is asking two types
to be equal: `[]` equals only itself.

`main!` hid the gap, since its answer is `[]` and `else return
host.exit!(1)` fits it. A helper that reads an argument or exits, answering
a `Nat`, had no way to write the exit.

## Design

**The rule.** At a join, a path whose type is `[]` is not unified with the
join's type, which the other paths decide. If every path's type is `[]`, the
join's type is `[]`. The joins are the branches of an `if`, the arms of an
`is`, and the value of a `return` or a leaving line meeting its clause's or
lambda's answer.

**It is one-way.** Nothing becomes `[]` by this rule. `bad : Nat -> []`
answering `3` is refused as before, since its answer is not a path of type
`[]` but a `Nat` where `[]` is wanted. So no value is ever handed out as a
`[]`, and none of another type is handed out where a `[]` was.

**Why only at joins.** A path that never answers can stand anywhere a value
can, in principle, and Rust lets its `!` become any type wherever one is
wanted. In Faun an effect stands on a line of its own, so it is never an
argument or an operand. What never answers turns up as a branch's or an
arm's value, a `return`'s, or a whole body. The joins are every place it
needs to fit.

**What is held must be used up.** A branch that never answers ends the
program, as a `return` ends its clause, so it must use up the resources it
holds: a `File` still held where a branch calls `host.exit!` is refused,
"still held where this never answers", as it already was where `main!`
answers by `exit!`. It no longer has to agree with the branches that go on.

**Only what is known to be `[]`.** A path whose type is still unknown when
its definition is checked joins as before. In an unsigned helper whose
`host` is generic, `host.exit!(2)` is `[]` only once a caller names a
`Host`, so its `else return host.exit!(2)` is refused there; a signature,
`port! : Host -> Nat`, makes it known. When every path is `[]`, the join is
`[]`, so an `if` both of whose branches exit cannot be used as a number.

**Lowering.** Barb already treats a call that never comes back as answering
whatever type its position wants, so a `[]` path lowers at the join's type.

## Costs

One rule in the checker, applied where it already unifies paths, and 2–4%
of checking time on the benchmark's cases. A reader meets it only as code
that now builds, and as a refusal where a branch that exits leaves a file
open.

## Alternatives considered

- **`[]` equal to every type.** Unification is symmetric, so values would
  flow into `[]` as freely as out of it: `bad` above would check, and its
  `3` could be read as a `Str`. Unsound.
- **A free result type, `exit! : (Host, U8) -> a`,** as OCaml's `exit`.
  Hindley–Milner needs no new rule, and each call picks its type. But the
  signature stops saying the call never answers, and every helper that
  exits would need the same idiom.
- **A coercion wherever a type is wanted,** as Rust's `!`. More general,
  and a form of subtyping in inference, with nothing left for it to do here.
- **An explicit `absurd : [] -> a`,** as Haskell's. No rule, but
  `host.exit!(2).absurd()` in exactly the code this is meant to tidy.

## Origin

Asked while weighing a never type: `[]` was already the right type for
`exit!`, and the branches beside it could not be written.
