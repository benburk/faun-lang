# Proposal: Branching on a computed value

- **Status:** Draft
- **Created:** 2026-10-01
- **Affects:** the grammar, the parser, pattern compiling, every helper
  definition that exists only to take a computed value apart

---

## Summary

A Faun body cannot branch on a value it computed: only a definition's
clauses take values apart, and only its parameters. So every such branch is
a definition of its own, with a signature. This records the ways that could
change, and why none is chosen yet: match expressions, `if` expressions,
lambdas bound to names, and lambdas of more than one clause. Each makes some
programs shorter and more like Python, and each costs one of three things
the current grammar has: one way to write a branch, code that stays flat,
and functions that are visibly not values.

## Motivation

Taking a computed value apart means writing a function for it. In the graph
and heap libraries alone, seven definitions exist only for that:

- `visiting` and `drained` take apart `heap.pop()`
- `stepped` takes apart the step a path walks back through
- `sorted` takes apart whether toposort ordered every node
- `climb_past`, `sink_past` and `cheaper` take apart the heap's comparisons

Each is mostly its signature. The same holds for a branch inside a loop: the
standalone components example is three definitions where the Python
cookbook's `connected` is one, because each test (seen before, or not) is a
definition's guard.

Written with match expressions, `if` expressions and a local recursive
lambda, the components example becomes one definition in the Python
version's shape:

```
connected(graph) -> (
  walk = |stack, walked| match stack (
    [] -> walked
    [current, *rest] if walked.seen.contains(current) -> walk(rest, walked)
    [current, *rest] -> (
      next = graph.get_or(current, [])
      walk(next.extend(rest), {seen: walked.seen.insert(current), path: walked.path.append(current)})
    )
  )
  start = {seen: Set.empty(), groups: []}
  found = graph.keys().fold(start, |found, node|
    if found.seen.contains(node) then found else (
      walked = walk([node], {seen: found.seen, path: []})
      {seen: walked.seen, groups: found.groups.append(walked.path)}
    ))
  found.groups
)
```

What stays different from Python is not syntax: `seen` is threaded through
every call and rebuilt in a record, because Python mutates one shared set.

## Design

Nothing is decided. These are the options and what each costs.

### What the current grammar gives

- **One way to branch.** A definition's clauses are a match on its
  arguments, and they are the only match a program writes.
- **Flat code.** Every branch point is a top-level definition, so nesting
  is at most a block inside a clause.
- **Named steps.** A helper forced by a branch gets a name and a signature
  saying what it does, which is the habit of naming intermediates the
  grammar enforces.
- **Functions that are visibly not values.** A definition is written as
  clauses, never as a value bound to a name, which fits a language where a
  function is never stored and every call is defunctionalised.

### Match expressions

`match expr ( clauses )`, its arms clauses as a definition's are, `pattern
[if guard] -> expr`, in parentheses as a body's block and a type's method
block are. Barb already has a match term, and pattern compiling already
turns clauses into decision trees, so lowering is mostly reuse. It removes
every helper above.

It costs the first two things. A match on a parameter and a clause do the
same, so a definition can be written either way and nothing says which. A
rule that a match may not take a parameter apart would remove the overlap,
but it is an odd rule to explain. And match expressions nest: languages that
have them, Gleam, Elixir, OCaml, tend to nested `case` in practice.

### `if` expressions

`if c then a else b` is `match c (True -> a, False -> b)`, so it adds a
second spelling of a two-armed match on a `Bool`. With match expressions it
earns little; without them it covers only branches on a `Bool`.

### Lambdas bound to names

`walk = |stack, walked| …` inside a body, called or passed to a call and
never stored, returned or put in a record: the rule function parameters
already follow, so it defunctionalises as a lambda does today. What it gives
is Python's nested function: `walk` reads `graph` from where it was written
instead of being handed it every call. That needs it to call itself, so the
name is in scope in its own body, and lifting it makes a recursive top-level
definition with what it reads as extra parameters.

Whether locals may call each other, not only themselves, is open.

### Every function a lambda

Top-level definitions could be bindings too, `main = |host| …`, so a
function is written one way everywhere. It costs flatness everywhere: most
definitions have several clauses, and each would become `f = |n| match n
(…)`, a level deeper. And a name bound to a lambda reads as a value bound to
a name, which Faun's functions are not.

### Lambdas of more than one clause

Generalising a construct the language has instead of adding one: a lambda
may have several clauses, as a definition does. A function is then always a
group of clauses, named at the top level or anonymous inline, and branching
on a computed value is handing it to an anonymous group:

```
popped = heap.pop()
popped.match(
  |Err(Empty)| -> state,
  |Ok({key, value, rest})| -> rest.push_all(added).drain(next, visit),
)
```

The spelling is open. There is still one way to branch, clauses; a nest is
a lambda in the source, no deeper than a `fold` with a lambda of several
lines today; and top-level definitions and lambdas are the same thing, named
or not, without functions becoming values.

## Costs

Each option's are above. Common to all of them: a second way to write what
a helper definition writes today, and less pressure to name each step.

## Alternatives considered

**Keep the current grammar.** The cost is bounded and visible: a helper and
its signature for each branch on a computed value. It is the option this
draft leans to until the count below says otherwise.

## Implementation impact

For whichever option is chosen: `grammar.ebnf` and the tree-sitter grammar;
the parser; pattern compiling, which a match expression or a lambda of
clauses would reuse; lambda lifting, for a lambda bound to a name that calls
itself; and the programs, whose helper definitions could fold back into the
bodies that call them.

## Open questions

- **How much does it cost now?** Count, across the ported programs and the
  libraries, the definitions that exist only to take a computed value
  apart, against those that take apart their parameters. A large share
  argues for a change; a small one for leaving the grammar alone.
- **Which option, if any?** Lambdas of more than one clause keep one way to
  branch; match expressions are more familiar.
- **For a lambda bound to a name:** may locals call each other, or only
  themselves?

## Origin

Comparing the standalone components example with the Python cookbook's
`connected`, after the termination check went and its step limits with it,
left the helper definitions as the largest difference that was syntax
rather than the absence of mutation.
