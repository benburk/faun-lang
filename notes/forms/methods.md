# Methods

This note owns a type's own functions: the `.( )` block a type declaration
carries, the methods and values in it, how a dot call finds them, the
members a type asks the compiler to write (`equals`, `cmp`, `to_str` and
`hash_into`), and which of a type's parts other modules see. Operators are
methods by another spelling, owned by [operators](operators.md); export
lists by [modules](modules.md).

## Type blocks

A type declaration may end in a block, `.(` … `)`, holding signatures,
clauses and values, as the top level does:

```ruby
Vec2 : {x: Int, y: Int}.(
  zero = Vec2({x: 0, y: 0})

  add : (Vec2, Vec2) -> Vec2
  add(Vec2({x: a, y: b}), Vec2({x: c, y: d})) -> Vec2({x: a + c, y: b + d})

  twice(v) -> add(v, v)

  equals : (Vec2, Vec2) -> Bool
)

v : Vec2
v = Vec2({x: 1, y: 2})

expect v.add(v) == v.twice()
expect Vec2.add(v, Vec2.zero) == v
```

Outside the block a method is called with a dot on a value, `v.add(w)`, or
qualified by its type, `Vec2.add(v, w)`; a value of the block is named by
its type, `Vec2.zero`. A bare `add(v, w)` outside the block is an unknown
name. Inside it, a sibling is called by its bare name, and the dot works
too. A method written without a signature is a method all the same; its
type is inferred before its callers' are.

`receiver.method(arguments)` is the method called with the receiver first.
Which method is meant is decided while checking, by the receiver's type:
there is no runtime dispatch and no table of methods in a value. A method
of a value's type is reached whether or not the caller imported the type,
so a module that imports only `boxed` from a module declaring `Box` may
still write `boxed(3).peek()`.

A type has one block, in its declaration. A second `Box.(` … `)` does not
parse, and neither does `Nat.(` … `)` in a program adding to the standard
library's `Nat`.

### A sum standing for its constructors

Among a clause's parameters, a sum's own name matches whichever constructor
holds the value and binds its payload, and the same name in the clause's
body builds that constructor again. So a sum whose methods forward to each
payload's own writes one clause per method, from the arena example
(`examples/rps-arena/main.fn`):

```ruby
Bot : [
  AlwaysRock(AlwaysRock),
  BeatLast(BeatLast),
  Rotate(Rotate),
  RandomBot(RandomBot),
  Freq(Freq)
].(
  name : Bot -> Str
  name(Bot(bot)) -> bot.name()

  open : Bot -> (Throw, Bot)
  open(Bot(bot)) -> (
    (throw, next) = bot.open()
    (throw, Bot(next))
  )

  answer : (Bot, Throw) -> (Throw, Bot)
  answer(Bot(bot), last) -> (
    (throw, next) = bot.answer(last)
    (throw, Bot(next))
  )
)
```

The clause is checked once for each constructor, so each copy's payload has
one type. The rules for this spelling are in the standard README's Tags
section and in [tags](../values/tags.md).

## Derived members

A type's block asks for `equals`, `cmp`, `to_str` or `hash_into` by writing
its signature with no clauses, and the compiler writes the member from what
the type holds:

```ruby
Size : [Small, Medium, Large].(
  cmp : (Size, Size) -> Order

  to_str : Size -> Str
)

Box(a) : [Box(a)].(
  equals : (Box(a), Box(a)) -> Bool where a.equals : (a, a) -> Bool
)

expect Small < Large & Large.to_str() == "Large"
expect Box("a") != Box("b")
```

- A sum's values are equal where they are one constructor with equal
  fields, ordered by which constructor the type declares first and then by
  their fields in turn, written as a tag is, `Filled(1, x)`, and hashed as
  the constructor's place and then each field.
- A wrapper's member is what it wraps: `Vec2` above is equal where its
  records are, and written as its record is, `{x: 1, y: 2}`. A record has
  no order, so neither has a wrapper of one.
- A field whose type is a variable is asked through a `where` bound the
  signature writes, as `Box(a)` does.
- Only the four shapes are derived: `(T, T) -> Bool`, `(T, T) -> Order`,
  `T -> Str` and `(T, h) -> h`, each over the type itself.
  `equals : (Point, Nat) -> Bool` with no body is refused.
- Any other signature without clauses is refused: "`Box.peek` has a
  signature and no clauses". Only the host leaves a definition for its
  target to answer.

A type with `cmp`, written or derived, has `equals` from it: equal where
`cmp` answers `Eq`. Declaring both is refused, with "leave `equals` out: an
ordered type's `equals` is its `cmp`'s `Eq`".

Structural types need no declaration. A closed record has `equals`,
`to_str` and `hash_into`; a tuple has those and `cmp`, position by
position; a closed tag row has `equals` and `to_str`. An open record, or a
row a caller may still add tags to, has none of them, since part of the
value is the caller's. A nominal type has none until it asks:
`Size : [Small, Large]` with no block makes `Small != Large` say "`Size`
has no field or method `equals`".

## Visibility

Exporting a type exports its methods; its constructors stay private unless
it is exported as `T.*` ([modules](modules.md)). A method has no visibility
of its own: whoever holds a value can call every method of its type, even
where the type itself is not exported. A helper that should stay private is
a top-level definition the module does not export.

## Rationale

### Why are methods written in a block on the type?

So that a dot call has one place to look. `x.len()` means the `len` in the
block of `x`'s type, decided by the type alone, with no import, no trait in
scope and no search through instances. The block also keeps each type's
operations in one place for the reader, and lets two types each have a
`len` or a `to_str` without their names meeting at the top level, where a
second `len` would clash.

Generic code does not need a trait to ask for a method: a `where` bound
names the member and is met by any type whose block has it
([types](../types.md)).

### Why can no other module add a method to a type?

A method added from elsewhere would make what `x.m()` means depend on which
modules are loaded. Rust's orphan rule exists for that problem across
separately compiled crates; Faun compiles the whole program at once, so the
rule is not forced by the compiler, but keeping a type's methods in its
declaration keeps every member, derived or written, readable in one place.
The cost is the half of the expression problem this leaves open: adding an
operation to a type you do not own means a top-level function, called as
`triple(n)` rather than `n.triple()`, or a type of your own that wraps it.

### Why is a derived member asked for by a bodyless signature?

The signature is what a written member would start with anyway, so asking
costs one line and adds no keyword. It says exactly what is derived and at
what bounds: `Box(a)`'s `equals` asks `a.equals` of its field, and the
signature is where that bound is written, as it would be for a body.

Ori tried inferring which bodyless method was wanted, and withdrew it
twice. Deciding by name made `to_str` and `to_string` adjacent lines of
identical shape and opposite behaviour, so renaming a method inverted it.
Deciding by shape meant that adding a nullary constructor to a working type
silently switched a method from forwarding to its payload to rendering its
constructor. Both were a declaration whose meaning came from somewhere
other than what it says. Faun keeps the rule narrow: only the four names,
only at their one shape each, and any other clause-less signature is
refused, so a forgotten body is an error rather than a derivation.

### Why does a nominal type not get `equals` without asking?

A type's name is a claim that its meaning may differ from its shape. A
version that ignores its build tag, or a fraction where 2/4 is 1/2, is
equal by a rule the fields do not show. A record or a tuple has no name to
make that claim, so its shape is its meaning and its members are derived
unasked. The cost is a line in each nominal type that wants the structural
member, and a refusal that names the missing method when it is used
without one.

### Why at most one of `equals` and `cmp`?

Two definitions of one fact can disagree. Rust allows `PartialEq` and `Ord`
to be written separately and documents that they must agree; nothing checks
it. In Faun a type with an order has its equality from that order, so
`a.cmp(b) == Eq` with `a != b` cannot be written:

```ruby
Version : {major: Nat, minor: Nat, build: Str}.(
  cmp : (Version, Version) -> Order
  cmp(Version(a), Version(b)) -> a.major.cmp(b.major) | a.minor.cmp(b.minor)
)

v : (Nat, Nat, Str) -> Version
v(major, minor, build) -> Version({major, minor, build})

expect v(1, 2, "x") == v(1, 2, "nightly")
```

The build tag takes part in neither the order nor the equality, and the
two cannot disagree about it.

A type may still have equality without an order. `List` has `equals` and no
`cmp`: an `equals` drawn from a `cmp` asks what that `cmp` asks, so lists
of records, which have no order, could not be compared at all. The cost is
a type whose `==` should differ from its order's `Eq`. The floats are that
case: their `cmp` is the standard's total order, so `==` follows it and a
NaN equals itself, and IEEE 754's comparison is the named `numeric_equals`
([floats](../values/floats.md)).

## Related

- [Operators](operators.md): `==`, `<` and the rest as calls of these
  members
- [Modules](modules.md): export lists, and `T` against `T.*`
- [Types](../types.md): `where` bounds, which generic code uses instead of
  traits
- [Tags](../values/tags.md): constructors, `Type.Ctor`, and structural rows
- [Records](../values/records.md) and [tuples](../values/tuples.md): the
  members they have without declaring them
- [Functions](../values/functions.md): definitions, values and callbacks
