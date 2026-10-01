# Proposal: Containers take a policy

- **Status:** Draft
- **Created:** 2026-10-01
- **Affects:** the standard library's `Map`, `Set`, `SortedMap` and
  `SortedSet`, the heap library, every signature that names one of them, the
  standard library's README

---

## Summary

A container whose layout depends on how its keys compare takes that
comparison as a type parameter: a policy, a type whose methods answer what
the container asks of a key. The container keeps a value of the policy
beside its entries, and each call it makes to it is resolved by the policy's
type at specialization, so dispatch stays static. Two containers with
different policies have different types, so the checker refuses mixing them.
The standard library's `Own` policy answers through the key's own methods,
which is what every container does today.

| Wanted                 | Today                 | After                  |
| ---------------------- | --------------------- | ---------------------- |
| `Str` keys, case-blind | a wrapper key         | `CaseFold({})`         |
| A heap, largest first  | a wrapper key         | `Reverse(Own({}))`     |
| By length, then text   | a wrapper per pairing | `Lex({first, second})` |
| A map's type           | `Map(Str, Nat)`       | `Map(Str, Nat, Own)`   |

A wrapper key is wrapped at every insert and lookup and unwrapped on the way
out; a policy is passed once, `Map.empty_by(CaseFold({}))`, and the keys stay
what they are.

No compiler change is needed: every rule this uses is in the language now.

## Motivation

A key type has one `equals`, one `hash_into` and one `cmp`, defined in its
own block and nowhere else. That is what keeps every map coherent, and it
also makes one way of comparing a key the only way any container may compare
it. Haskell's `Hashable` shows where that leads: a policy choice, how to
compare or hash, is made to look like a property of the type, and a program
that needs two policies for one type has to invent a type for the second.

**The standard library already separates part of this.** A key's
`hash_into` says only what the key is made of, generic over any hasher, and
the hasher decides how to mix (`hasher.fn`). What a key _is_ stays the
type's, and how it is mixed is the container's. What is still the type's
alone is which keys count as the same, and in what order they go.

**A second meaning costs a wrapper type.** Case-insensitive keys need a
`CiStr` around `Str` with its own `equals` and `hash_into`, a wrap at every
insert and lookup, and an unwrap of every key `to_list` answers. An order
needs a wrapper for each order, Haskell's `Down` or Rust's `Reverse`, and
another for each combination of them. The heap library is a min-heap only,
"after Rust's `BinaryHeap` turned round", so a heap answering largest first
is a wrapper key reversing `cmp`.

**The corpus has no such wrapper yet.** Nothing in the ported programs or the
libraries wraps a key only to change how it compares. The evidence is from
the languages Faun's libraries follow: Haskell's `case-insensitive` package
and `Down`, Rust's `Reverse` and its `HashMap<K, V, S>`, which takes the
hasher as a type parameter because one fixed hasher did not serve. This
draft records the design before the first program needs it.

## Design

### A policy is a type with methods

A policy is any type with the methods a container asks for, its first
argument the policy itself:

```
CaseFold : {}.(
  same : (CaseFold, Str, Str) -> Bool
  same(_, a, b) -> folded(a) == folded(b)

  feed : (CaseFold, Str, h) -> h where Hasher(h)
  feed(_, key, hasher) -> folded(key).hash_into(hasher)
)
```

A policy without fields is written `{}` and passed as `CaseFold({})`. A
policy may hold what its comparison needs, a locale or a tolerance, and is
still resolved by its type.

### What each container asks

`Map` and `Set` ask which keys are the same and what each is made of; the
sorted containers and the heap ask the order:

```
KeyHash(p, k) = where
  p.same : (p, k, k) -> Bool,
  p.feed : (p, k, Mixer) -> Mixer

KeyOrder(p, k) = where
  p.compare : (p, k, k) -> Order
```

`feed` is written generic over any hasher and met at `Mixer`, as a key's
`hash_into` is today, so the mixer stays the library's: a policy can feed it
and never read a digest out, and `mixer.fn`'s promise that the mixing may
change without changing a program holds.

The names are not `equals`, `hash_into` and `cmp`. Those are the structural
members, with rules of their own: a type with `cmp` takes its `equals` from
it and is refused one written, so a policy answering both an order and an
equality under those names would be refused.

### The container holds its policy

Each container's record gains a `policy` field, and its type a trailing
parameter: `Map(k, v, p)`, `Set(k, p)`, `SortedMap(k, v, p)`,
`SortedSet(k, p)`, `Heap(k, v, p)`. Every method that compares keys has the
container's bound on `p` in place of today's bound on `k`, and calls the
policy it holds:

```
get : (Map(k, v, p), k) -> Result(v, [Missing]) where KeyHash(p, k)
```

`empty`, `of_list` and their kin answer a container under `Own`, so an
unsigned `Map.empty()` means what it means today. `empty_by(policy)` and
`of_list_by(entries, policy)` take one.

### The standard policies

The standard package exports two:

- `Own`, whose `same`, `feed` and `compare` are the key's `equals`,
  `hash_into` and `cmp`.
- `Reverse(p)`, whose `compare` is `p`'s with its arguments swapped.

Others, `Lex(p, q)` or `ByLength`, are a library's to write; any type with
the methods is a policy.

### Coherence

A container's policy is in its type, so a map under `CaseFold` and one under
`Own` are different types, and an operation taking two containers takes two
of one type. What a type cannot tell apart is two values of one policy type,
`Within(0.01)` and `Within(0.1)`: an operation taking two containers keeps
the receiver's policy and inserts the other's entries under it, as an
operation built from `insert` already does.

### Operations take callbacks

Policies are for containers, whose entries stay laid out by one comparison
from one call to the next. An operation that compares and is done, a sort
or a `max`, takes a callback, which is already specialized at each call and
cannot disagree with anything kept. This draft changes no operation on
`List`.

## Costs

- **Every signature naming a container gains a parameter.** `Map(Str, Nat)`
  is `Map(Str, Nat, Own)`. Outside the files defining them, 20 lines in 7
  files name a standard container: four Advent of Code days, the components
  example, `memoize` and `list.fn`. The heap library's examples and the graph
  library name `Heap`.
- **A generic signature bounds the policy, not the key.** A definition over
  any map writes `KeyHash(p, k)` where it wrote `k.hash_into` and
  `k.equals`: as many lines, read one step further from the key.
- **A policy is a named type.** Functions are never held, so a policy cannot
  be a lambda; each is a declaration with a block.
- **Equality of two containers is the receiver's.** Under a policy holding a
  value, `a == b` compares by `a`'s policy and may differ from `b == a`.

## Alternatives considered

**Wrapper keys.** The current way, and it stays available. It suits a value
that means something different everywhere, an `Email` rather than a `Str`.
For a comparison only one container needs, it costs a wrap and an unwrap at
every boundary and a type per combination of orders.

**A comparison passed to each call.** `map.get(key, policy)` lets two calls
on one map disagree, and a map filed under one comparison read under
another answers wrongly. The policy has to be the container's.

**A policy held but not in the type.** Scala's `TreeMap` takes its
`Ordering` as an implicit value, so two maps of one type can be ordered two
ways and merged silently. Putting the policy in the type is what makes the
checker refuse it.

**Methods added to a type from outside its block, or instances chosen in a
scope.** Either gives one type two meanings in one program, which is the
incoherence the one-block rule exists to prevent.

**ML functors.** `Map.Make(CaseFold)` in OCaml is this design with a module
system to carry it. Faun gets the same application from a type parameter and
specialization, without modules as a second language.

**A default for the parameter, `Map(k, v, p = Own)`.** It removes the cost
to signatures but adds syntax for one purpose. An alias would do it without
any, if an alias answered for the methods of what it names; see the open
questions.

**The hasher as a parameter too.** `Map` and `Set` answer in insertion
order, so no program observes the mixing; choosing a hasher would change
only speed and how well a map resists keys chosen to collide. That is
`Mixer`'s to get right, and stays its.

## Implementation impact

1. `standard/`: `Own`, `Reverse`, `KeyHash` and `KeyOrder` in a module of
   their own, exported from `standard.fn`; `map.fn`, `set.fn`,
   `sorted_map.fn` and `sorted_set.fn` take and hold a policy; `group_by`
   answers a map under `Own`; the README's paragraphs on keys and maps.
2. The heap library takes a policy, and the graph library's Dijkstra passes
   `Own`.
3. The programs: each signature naming a container gains its policy.
4. The compiler: nothing, unless a policy without fields turns out to take
   space in the container's record, in which case an empty field is dropped
   in lowering.

No grammar change, so nothing in `grammar.ebnf` or the tree-sitter grammar.

## Testing

- Each container under `Own` answers as today: the existing expectations
  hold unchanged on all three backends.
- Each container under another policy: a map under a case-folding policy
  finds `"Pear"` by `"pear"` and answers the key as it was inserted; a
  sorted set under `Reverse(Own({}))` answers largest first; a heap under it
  pops largest first.
- A refused program in `crates/cli/tests/refused/`: a map under one policy
  handed where a map under another is wanted, with the checker's message in
  its `.err`.
- A policy without fields adds nothing at run time: the heap's sort
  benchmark under `Own` runs as fast as before, and the emitted Barb holds
  no field for it.

## Open questions

- **Should an alias answer for the type it names?** With `Map(k, v) =
  HashMap(k, v, Own)`, signatures would keep `Map(k, v)`, but `Map.empty()`
  is refused today: an alias names a type and has no methods. Letting it
  answer for the methods of what it names would remove most of the cost to
  signatures, without new syntax.
- **The method names.** `same`, `feed` and `compare` avoid the structural
  members; whether they read well is open.
- **Does the field cost nothing?** Measure before approving.

## Origin

Comparing Faun's structural `where` bounds with Haskell's type classes,
after a comment on Haskell's `Hashable` describing a policy choice made to
look like a property of a type. Faun's methods share the problem: one block
decides each type's comparisons for every container in a program. The
hasher split already solved half of it. Trying the rest in `/tmp`, a policy
type held by a container and asked through bounds checked as written:
`Own`, `Reverse` over any key, combinators of policies, and a policy holding
a value all met their bounds under `faun test` without a compiler change.
