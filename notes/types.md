# Types

This note owns how Faun gives every value a type: inference, signatures and
`_`, `where` bounds, aliases, and specialization. Rows are summarized here
and owned by [records](values/records.md) and [tags](values/tags.md);
numerals by [numbers](values/numbers.md).

## Inference

Faun infers types by Hindley–Milner (HM): each definition gets its most
general type by unification, with no annotation needed. Polymorphism is
rank-1: a type variable is chosen once per use, and quantifiers stand only
at the outside of a type. An unsigned definition is generic, and anything
it asks of a value becomes a `where` bound on that value's type:

```ruby
double(x) -> x.mul(2)
name_of(v) -> v.name

expect double(3) == 6
expect double(U8.of_nat(200)) == U8.of_nat(144)
expect name_of({name: "Ada", age: 36}) == "Ada"
```

`double` serves every type with a `mul`, and `name_of` every value with a
`name`. A use whose type lacks the member is refused there: `double(True)`
says "`Bool` has no field or method `mul`".

Records and tag unions are row-polymorphic: a row is a set of fields or
tags that may be open (a caller's value can hold more) or closed. Rows are
unified like any other type, so `{name: Str, *}` takes any record with a
`name`, and the failure tags of two `?`s join into one row.

```ruby
greet : {name: Str, *} -> Str
greet(person) -> "Hello, ${person.name}"

expect greet({name: "Ada", age: 36}) == "Hello, Ada"
expect greet({name: "Bo"}) == "Hello, Bo"
```

## Signatures

A signature is optional. Where one is written, the body is checked against
it and may use only what it says: `flip : a -> a` with `flip(x) -> x.not()`
is refused, with the help "write `a.not : a -> a` in the signature's
`where`".

A signature can also choose a type that nothing else would. A numeral that
nothing types is a `Nat`, so the signature here changes the answer:

```ruby
t = 200
s : U8
s = 200

expect t + t == 400
expect s + s == U8.of_nat(144)
```

A signature may write `_` for any part of a type it leaves to the clauses.
The definition is then inferred as an unsigned one is, starting from what
is written, so it takes no `where` bounds. `_` stands for a type only in a
function's signature; a data declaration or an alias states its type in
full.

```ruby
app : {stdin: List(U8), *} -> Result({part1: Nat, part2: Nat}, _)
```

(`examples/aoc/201505.fn`: the input and the answer are written, and the
failure row is whatever the body's `?`s join.)

## Bounds

A `where` bound asks a type variable's type for a member by its shape. It
is structural: any type that has the member meets it, and nothing declares
that it does. An unsigned definition infers its bounds; a signed one writes
them, parted by commas, on one line or a line apiece:

```ruby
sum_of : List(a) -> a where
  a.zero : a,
  a.add : (a, a) -> a
sum_of(values) -> values.sum()
```

A bound may name a variable the signature does not, when an implementation
determines it: in `r.fold : (r, Nat, (Nat, x) -> Nat) -> Nat`, `x` is
whatever `r`'s `fold` hands over. A bound on a variable nothing reaches is
refused, and so is one whose types no implementation fixes at its use.

## Aliases

`Name(a) = type` names a type. It is transparent: it expands where it is
used, so `Edge(Nat)` is the record `{target: Nat, weight: Nat}` and nothing
downstream sees `Edge`. An alias must use every parameter and may not name
itself, directly or through another.

`Name(a) = where …` names a set of bounds, applied in a `where` clause and
nowhere else. From the graph library (`libraries/graph/src/edge.fn`):

```ruby
Edge(e) = {target: Nat, weight: e}

Walkable(g, e) = where
  g.node_count : g -> Nat,
  g.edges_from : (g, Nat) -> List(Edge(e))
```

A type with an identity of its own is declared with `:`, as
`Stack(a) : [Empty, Push(a, Stack(a))]`.

## Specialization

Faun compiles a whole program at once and monomorphizes it: each generic
definition is compiled once for each set of concrete types it is used at,
and each bound becomes a direct call of that type's own member. Barb, below
the frontend, is monomorphized: no type variable or bound reaches it, and
nothing of them exists at run time. Functions passed to a call are
specialized the same way ([functions](values/functions.md)).

Polymorphic recursion, where a definition calls itself at another type, is
never inferred: unsigned, it fails with "a type would contain itself". With
a signature it is checked, and accepted where the types it reaches are
finite:

```ruby
swap : (a, Nat) -> Nat
swap(_, 0) -> 0
swap(x, n) -> 1 + swap(True, n - 1)
```

A call that grows the type each round is refused, since it would need a
definition for every round. From the refused cases:

```ruby
nest : (a, Nat) -> Nat
nest(_, 0) -> 0
nest(x, n) -> 1 + nest([x], n - 1)
```

"this call asks for `nest` again, at a larger type". A type that holds
itself at a larger type, `Nest(a) : [Flat(a), Deeper(Nest((a, a)))]`, is
refused at its declaration for the same reason.

## Rationale

### Why Hindley–Milner with rows?

HM gives every definition a principal type: one most general type, found
without annotations, of which every other valid type is an instance. That
is what lets signatures be optional. Rows add structural records and tags
without leaving HM: an open row is one more variable to unify, so a
function can ask for "a record with a `name`" and failure tags can join
across `?` without a declared error type.

The cost is that inference is whole-program and not local: a type error can
surface at a use rather than in the definition that is wrong. Writing the
signature moves the error back to the definition.

### Why are signatures optional, and why `_`?

A signature should be written for a reader, not for the compiler. The
n-body benchmark is in the repository twice: `examples/nbody` with 20
signatures and `examples/nbody-untyped` with none. Both compile to
identical x86-64 code.

Most signatures restate what inference finds. Some do choose: `s : U8`
above is part of the program, and deleting it changes the answer. That
happens only where nothing else picks the type; it is the same defaulting
Haskell has.

`_` covers the common middle case. A function's input and answer are worth
writing; its failure row is the union of whatever its `?`s pass on, and
writing that out by hand means editing the signature every time a callee
gains a failure. 59 of the 1,095 signatures in the examples write `_`.

### Why structural `where` bounds instead of traits or typeclasses?

A type meets a bound by having the member, as a Go interface is met. There
is no trait to declare, no `impl` to write, and no instance to import, so
there is no orphan rule and no overlap: a type has one `add`, and every
bound asking for `add` gets it. Bounds can be inferred, because the member
a body calls is the bound.

The cost is that a bound says nothing about meaning. Any type with a
`zero : a` and an `add : (a, a) -> a` meets `sum_of`'s bounds, whether or
not its `add` is associative, as with any interface. Constraint aliases
give a set of bounds a name, as `Hasher(h)` does, without making it a
nominal thing a type must sign up to.

### Why no runtime dictionaries?

Haskell passes a typeclass's methods to a generic function as a record at
run time, a dictionary. Faun's functions are second-class: they cannot be
stored in data ([functions](values/functions.md)), and a dictionary is a
record of functions. Monomorphization removes the need: every bound is
known at each specialization, so each call is a direct call, which the
optimizer can then inline.

The cost is code size, one copy per instantiation, and no separate
compilation of generic code. Faun compiles whole programs from source, so
the second costs nothing it did not already pay.

### Why are aliases transparent?

An alias is for naming a long type, such as a record of options or a row of
failures, not for making a new one. Structural values are built anywhere,
from literals, so an alias that minted an identity would refuse the very
records it names. Where identity is wanted, `:` declares a type, and its
constructor can be kept private with `export {T}`.

Because an alias is the type it names, `Tagged(unit) = Nat` cannot tell
`Tagged(Meters)` from `Tagged(Feet)`, so it is refused rather than
promising a distinction it does not keep.

### Why no subtyping?

HM with subtyping can infer (Dolan's MLsub), but what it infers is a type
plus a set of constraints that needs simplifying heuristics to read, so a
user can no longer predict the inferred type. Variance would also reach
into layout, method resolution and specialization.

Rows cover most of what subtyping is used for: a function asks for
`{name: Str, *}` and takes any record with a `name`, and tag rows widen by
joining. The cost is no heterogeneous collections and no implicit widening
of a declared type: a conversion is written.

### Why no higher-kinded or higher-rank types?

Unifying `f(a)` with `List(Nat)` has more than one answer, and
higher-order unification is undecidable in general (Goldfarb 1981).
Higher-rank types, where a function's parameter is itself generic, need an
annotation at every such binder to stay decidable.

The abstraction would also buy little here. Under monomorphization a
`Functor` over `List` and over a tree compiles to per-type code anyway, so
it shares only a name. Structural resolution already finds `xs.map(f)` on a
`List`. The library has little to share: `map` is defined on `List` alone,
and the five `fold`s take callbacks of different shapes, `(b, a) -> b` for
a list and `(a, k, v) -> a` for a map.

The cost is real: code generic over any container, such as `traverse`, is
written once per container, and there is no monad abstraction or
`do`-notation.

### Why is polymorphic recursion limited?

Inferring it is undecidable (Henglein 1993), so an unsigned definition
never gets it. A signature makes it checkable, and Faun accepts it.
Specialization adds the second limit: each instantiation is a definition of
its own, so a definition must reach finitely many. `nest` above would need
one for `a`, `List(a)`, `List(List(a))` and so on without end.

The cost is non-regular datatypes, such as a syntax tree whose variables
are typed by the binders around them, `Lam(Term(Maybe(a)))`. The recourse
is a regular encoding: de Bruijn indices, `Var(Nat)`, give the same tree
with scope checked by the program rather than the type.

## Related

- [Records](values/records.md): record rows, update and builders
- [Tags](values/tags.md): tag rows, how they join and close
- [Numbers](values/numbers.md): how a numeral takes its type
- [Functions](values/functions.md): callbacks, specialized like bounds
- [Methods](forms/methods.md): type blocks, and members a type derives
- [Dependent types](dependent-types.md): why types stop here
