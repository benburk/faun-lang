# Tuples

A tuple is a product of two or more values told apart by position, `(1,
"a")`. This note owns tuples: how they are written, built and taken apart,
the members they have without declaring them, and why they stay apart from
records.

## Tuples and their types

A tuple and its type are written the same way, members between parentheses
and parted by commas: `(1, "a")` is a `(Nat, Str)`. A tuple has two members
or more. One expression in parentheses is that expression grouped, `(x)` is
`x` and `(Nat)` is `Nat`, and a trailing comma does not make one:

```text
x = (1,)
error: a tuple has at least two members: write `(a)` to group one
```

There is no unit tuple; the unit value is the empty record `{}`. A tuple is
structural, like a record: no declaration, no `Tuple2` family, and no limit
on the number of members.

A function type's parameters are parenthesized too, so `(Nat, Nat) -> Nat`
takes two values. A function taking one tuple writes the tuple inside the
parameter list:

```ruby
swap : ((Nat, Bool)) -> (Bool, Nat)
divmod : (Nat, Nat) -> (Nat, Nat)
```

## Building and taking apart

A tuple is built by its literal and taken apart by a pattern, and by
nothing else. There is no `pair.0`. A pattern takes one apart wherever a
value can be named: in a binding, a clause's head, a lambda's parameters, a
test or a `for`:

```ruby
(q, r) = divmod(7, 2)
swap((n, b)) -> (b, n)
keys(map) -> to_list(map).map(|(key, _)| key)
gap(a, b) -> if (a, b) is (Ok(x), Ok(y)) & x <= y then y - x else 0
```

Since a binding cannot fail, it may take a tuple apart, and `(a, b) = (b,
a)` swaps two names. Matching on a pair is how a definition cases on two
values at once, and coverage is judged over the pair: clauses for
`(True, True)` and `(False, _)` leave `(True, False)` uncovered, which is
refused ([pattern matching](../forms/pattern-matching.md)).

The standard library answers tuples where the two parts have no better
names: `zip` and `cross` answer `List((a, b))`, `enumerate` answers
`List((Nat, a))`, `split_at` and `partition` answer a pair of lists, and a
map's `to_list` answers its entries as `(key, value)`.

A tuple never unifies with a record. `{_0: Nat, _1: Str}` is an ordinary
record with odd field names, and neither passes for the other:

```text
expected `{_0: Nat, _1: Str}`, found `(Nat, Str)`
```

A tuple has no fields either, so an unsigned `x_of(v) -> v.x` refuses one.

## Equality, order, text and hashing

A tuple has `equals`, `cmp`, `to_str` and `hash_into` without declaring
them, each by its members' own, taken in position order. `cmp` compares the
first members and goes on to the next only on a tie, through `Order.or`, so
`(1, 2) < (1, 3)` and `(2, 0) > (1, 9)`. `to_str` writes a tuple as it is
written, `(1, True)`.

```ruby
expect [(2, "b"), (1, "z"), (1, "a")].sort() == [(1, "a"), (1, "z"), (2, "b")]
by_pair = SortedMap.of_list([((2, 1), "b"), ((1, 9), "a")])
expect by_pair.keys() == [(1, 9), (2, 1)]
```

So a tuple is a sort key and a compound map key with nothing declared.

## Rationale

### Why have tuples when records exist?

Some pairs have no names worth inventing. `zip` answers pairs of an `a` and
a `b`; calling them `{first, second}` or `{left, right}` adds words that say
nothing, and each library would pick different ones. A tuple lets the
caller name the parts where it takes them apart, `|(key, value)| ...`,
which is where the names mean something. Records stay the default when the
parts have meaning, and especially when a value travels far from where it
was built.

### Why must a tuple have two or more members?

Because one value in parentheses is grouping, as everywhere else. A
one-member tuple would need a spelling of its own, and Python's and Rust's
`(x,)` makes a trailing comma change what an expression is. Faun allows a
trailing comma in every sequence, so it refuses `(x,)` outright rather than
let it mean something.

With `{}` as the unit, the arities have no gap: every tuple has two or
more, and `()` is never a value. One constructor argument is not a tuple
either: `Ok(value)` and `List(a)` use parentheses only to hold their
arguments. A value that needs a structural wrapper of one field uses a
record, `{value: a}`.

### Why is there no `pair.0`?

A position says nothing at the site that reads it: `result.2` does not say
what the third member is. A pattern names each part where it is used, and
the moment a part deserves a lasting name, the value deserves to be a
record.

Ori had `.0` once and dropped it. It bought nothing a pattern did not
already say, and it cost inference a deferral: `|t| t.0` needs a type for
"a tuple of some length whose first member is an `a`", an open tuple, which
nothing else needs. The cost is a destructuring line where a projection
would have been shorter.

### Why do tuples never unify with records?

They are different type formers: one is positional, the other named. If a
tuple were a record with numbered fields, `{_0: Nat, _1: Str}` would be a
pair, a pair would have fields, and row polymorphism would apply to tuples,
reviving the open tuples the previous answer avoids. Keeping them apart
also keeps their members apart: a tuple has `cmp` and a record does not.
How either is laid out in memory is the machine's business and shows in no
type.

### Why does a tuple have `cmp` when a record does not?

A tuple's positions are an order its author wrote, so comparing first
members first is the only reading there is. A record's fields have no
order ([records](records.md)). This is what makes a tuple the way to sort
records by several keys, `people.sort_on(|p| (p.surname, p.name))`, and to
key a `SortedMap` by two things at once. A tuple whose order should mean
something else becomes a declared type that writes its own `cmp`.

## Related

- [Records](records.md): named products, unordered, with no `cmp`
- [Collections](collections.md): tuples as map entries and keys
- [Pattern matching](../forms/pattern-matching.md): taking tuples apart,
  and coverage over several values
- [Operators](../forms/operators.md): `cmp`, and how `<` reads it
- [Functions](functions.md): parameters, and why a function type's are
  parenthesized
