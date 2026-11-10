# Anti-features

Everything Faun leaves out. The [README](../README.md) gives the short list;
this is the whole one, grouped by what each absence protects. Each bullet
links the note that owns the trade-off and the way around it. No rationale is
repeated here.

## Control flow

- No exceptions, and no panics: every operation answers a value. Division by
  zero answers zero, and a lookup that can miss answers a `Result`
  ([numbers](values/numbers.md), [collections](values/collections.md)).
- No hidden control flow. A function or host call happens only where it is
  written. There are no implicit constructors or destructors, no coercion
  hooks, and no cleanup callbacks ([effects](forms/effects.md)).
- No partial pattern matches. Clauses and arms must cover every value
  ([pattern matching](forms/pattern-matching.md)).
- No promise that a pure call comes back. Termination is not checked, and
  unneeded pure work may be left out ([computation](computation.md)).
- No loops, and so no `goto`, `break` or `continue`. A walk is a function
  calling itself, a fold or a library function, and a body leaves only by
  `return` or `?` ([recursion](proposals/approved/recursion.md),
  [pattern matching](forms/pattern-matching.md)).

## State, memory and lifetime

- No mutation in the source. `=` binds a name again, and a value never
  changes in place ([pattern matching](forms/pattern-matching.md),
  [memory](machine/memory.md)).
- No global state, and no null.
- No pointers, no references, no borrow syntax, and no lifetime annotations
  ([memory](machine/memory.md)).
- No tracing garbage collector, no reference cycles, and no manual memory
  management ([memory](machine/memory.md)).
- No ambient authority. An effect needs the `Host`, or a capability it hands
  out ([effects](forms/effects.md)).

## Types and dispatch

- No inheritance, no subtyping, and no implicit conversions
  ([types](types.md)).
- No traits, typeclasses or runtime dictionaries. A `where` bound asks for a
  member by name and shape ([types](types.md)).
- No higher-kinded types, no higher-rank types, and no polymorphic recursion
  ([types](types.md)).
- No dependent types and no user-written proofs
  ([dependent types](dependent-types.md)).

## Functions and calls

- No first-class functions. A function or lambda may be passed straight into
  a call, but not bound to a name, returned, or stored in data
  ([functions](values/functions.md)).
- No currying and no partial application ([functions](values/functions.md)).
- No functions of no parameters. A definition with no parameters is a value
  ([functions](values/functions.md)).
- No default, named or variadic arguments ([functions](values/functions.md)).
- No overloading by argument type. A name means one definition in a scope,
  and a method is chosen by its receiver's type
  ([methods](forms/methods.md)).

## Metaprogramming

- No macros, no runtime reflection, and no general compile-time
  metaprogramming. Derived members (`equals`, `cmp`, `to_str`, `hash_into`)
  are asked for by a signature with no body ([methods](forms/methods.md)).

## Modules

- No wildcard imports and no import cycles ([modules](forms/modules.md)).
- Nothing is exported unless an export list names it
  ([modules](forms/modules.md)).

## Machine

- No source-level object layouts, calling conventions, target intrinsics or
  inline assembly ([architecture](machine/architecture.md)).
- No dependency on LLVM or libc ([architecture](machine/architecture.md)).
- No separate compilation. A program is compiled whole, from the source of
  every package it uses ([architecture](machine/architecture.md)).

## Not yet decided

These are open rather than refused:

- a foreign-function interface
- concurrency
- indexed types ([indexed types](indexed-types.md))
