# Syntax

## Goals

- No symbol table required to parse it
- Fast to parse
- Layout- and indentation-agnostic
- small deterministic parser, limited lookahead, no explosive search through alternative interpretations
- LL(1) grammar for simpler parsing, incremental parsing, error recovery, better error messages
- few keywords

## FAQ

> Why commas?

- They are what every reader expects, so the syntax spends none of its
  strangeness on separators.
- An argument with an operator in it stays readable: `lower(r * 10, s, k - 1)`.
- Spacing never changes meaning. `f(a, -b)`, `[h, *t]` and `f(a, |x| x)` read
  the same however they are spaced, and a dropped comma is a syntax error rather
  than a silently different call.
- Any sequence may end with a comma, so a list written one element per line
  changes one line when an element is added.
- A function type's parameters are parenthesized, as a clause head's are:
  `add : (Nat, Nat) -> Nat`, and `fib : Nat -> Nat` for one.
- A tuple has at least two members: `(a)` groups, and `(a,)` is an error.

The case for and against, with measurements, is in [the commas proposal](../proposals/approved/commas.md).
