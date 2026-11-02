# Collections

This note owns the standard containers: `List`, the hashed `Map` and `Set`,
the ordered `SortedMap` and `SortedSet`, and how a key says what it is made
of through `hash_into`. Each container is ordinary Faun in the standard
library (`list.fn`, `map.fn`, `set.fn`, `sorted_map.fn`, `sorted_set.fn`);
none is built into the compiler. The full list of methods is in the
[standard library README](../../crates/faun/standard/README.md).

## Lists

`List(a)` is declared `[Nil, Cons(a, List(a))]`, and written with brackets:
`[1, 2, 3]`. A literal may end with a tail, `[x, *xs]`, which builds exactly
what the same pattern takes apart. A pattern's rest may stand first, so
`[*_, a, b]` matches the last two, and may go unnamed, `[a, b, *]`.

The methods follow Ori's standard list: `map`, `filter`, the folds,
searches, `zip`, `windows`, `sort`, `sort_on` and the rest. `sort` is a
stable merge sort by the element's `cmp`, and `sort_on` by a key's. A lookup
that can miss answers a structural tag rather than failing, so a caller's
own failures join it in one row ([tags](tags.md)):

```ruby
expect [1, 2, 3].get(5) == Err(OutOfBounds)
expect [0].drop(1).first() == Err(Empty)
expect [1, 2, 3].find(|x| x > 5) == Err(NotFound)
expect [1, 2, 3].set(5, 9) == Err(OutOfBounds)
expect [1, 2, 3].put(5, 9) == [1, 2, 3]
```

Nothing about a list is recognized by its name. `len` is a walk in the
source, and is answered from the length a list holds because Barb
recognizes what the walk computes; how a list is laid out and when one is
written in place is [memory](../machine/memory.md)'s business.

## Map and Set

`Map(k, v)` is a persistent hash map, and `Set(k)` is a map whose values
say nothing. Both keep their entries in insertion order: `to_list`, `keys`,
`values` and `fold` answer in the order keys were first inserted.
Inserting a key already there changes its value and keeps its place.

```ruby
m : Map(Str, Nat)
m = Map.of_list([("a", 1), ("b", 2), ("c", 3)])

expect m.get("z") == Err(Missing)
expect m.insert("a", 9).keys() == ["a", "b", "c"]
expect m.remove("a").insert("a", 9).keys() == ["b", "c", "a"]
```

Entries live in a list in insertion order, and an index of buckets points
into it by position, so the hash decides only where a key is looked up.
The index doubles above three quarters full, and removed entries are
compacted away when it does.

A map updates a key as Python's `defaultdict` does, with
`update_or(key, missing, change)`:

```ruby
counts = counts.update_or(word, 0, |count| count + 1)
```

Two maps or sets are equal where they hold the same entries, however each
was built; equality is by lookup, linear in the size.

## SortedMap and SortedSet

`SortedMap(k, v)` and `SortedSet(k)` are AVL trees ordered by the key's
`cmp`, for keys that must come back in order. Lookup, insertion and removal
take time logarithmic in the size, in the worst case. `to_list`, `keys` and
`fold` answer in ascending key order, and two sorted maps are equal where
their ascending entries are. Their constructors are not exported, so the
tree is `sorted_map.fn`'s business alone. `len` walks the tree.

## Building a container

A container is built from a list by the container, so the caller says
which. `Map` and `SortedMap` each have `of_list(entries)`,
`grouped(values, key)`, gathering values by a key, and `counted(values)`,
counting how many times each occurs, as Python's `Counter` does:

```ruby
expect Map.counted(["a", "b", "a"]).to_list() == [("a", 2), ("b", 1)]
expect SortedMap.counted(["b", "a", "b"]).to_list() == [("a", 1), ("b", 2)]
groups = Map.grouped([1, 2, 3, 4, 5], |n| n % 2)
expect groups.to_list() == [(1, [1, 3, 5]), (0, [2, 4])]
```

`Set` and `SortedSet` have `of_list`.

## Hashing

A key says what it is made of through `hash_into : (T, h) -> h`, generic
over any hasher. `Hasher(h)` is an alias for a type with two methods and
nothing more:

```ruby
Hasher(h) = where
  h.write_u64 : (h, U64) -> h,
  h.write_bytes : (h, List(U8)) -> h
```

So a key can feed a hasher but never read a digest out of one. The numbers,
`Bool`, `Str` and `List` define `hash_into`, and a tuple or a closed record
has its own, feeding its members. A declared type asks for the structural
one by writing its signature with no body, or writes its own:

```ruby
Point : {x: Nat, y: Nat}.(
  equals : (Point, Point) -> Bool
  hash_into : (Point, h) -> h where Hasher(h)
)

Celsius : Int.(
  equals : (Celsius, Celsius) -> Bool
  hash_into : (Celsius, h) -> h where Hasher(h)
  hash_into(Celsius(degrees), hasher) -> degrees.hash_into(hasher)
)
```

`Map` and `Set` feed the standard library's own hasher, `Mixer`. The
standard package exports `Mixer` as a type alone, so a generic signature
over a map can bound its key, `k.hash_into : (k, Mixer) -> Mixer`; neither
its seeding nor its digest is exported. `Map.seeded(seed)` starts an empty
map whose hashing begins from `seed`; `Map.empty` begins from nought.

Any type with the two write methods is a hasher, so a library can write its
own, with containers over it, and reuse every `hash_into` there is.

## Rationale

### Why an insertion-ordered map, with a mixer no program sees?

Because then nothing a program observes depends on the hash. Every
observation of a `Map` is in insertion order, so `to_list` answers the same
whatever the mixer computes. The mixer can change without changing any
program's output, and no test depends on it. The order a reader sees is the
order the program wrote, as in Python's dictionaries since 3.7.

The seed follows from it. A hidden seed chosen per run would need
randomness, and pure code has none: an effect needs the `Host`
([effects](../forms/effects.md)). So the default map begins from nought and
is deterministic. A program that must resist keys chosen to collide, where
whoever picks the keys could otherwise make every lookup walk one bucket,
gives `Map.seeded` a seed it obtained as an effect. The map stores only the
seed, and insertion order keeps it out of every result. No host hands out
random bytes yet; entropy is planned in the
[effects roadmap](../effects/roadmap.md).

The cost is a list of slots beside the index, removed slots kept until the
next resize, and equality by lookup rather than by walking two structures
side by side.

### Why is the default map hashed rather than ordered?

A hashed map asks a key for `equals` and `hash_into`, and every closed
record and tuple has both. An ordered map asks for `cmp`, which a record
does not have ([records](records.md)). So `Map` takes record keys with
nothing declared, `Map.of_list([({x: 1, y: 2}, "p")])`, where a `SortedMap`
would need a wrapper type with a written `cmp`.

### Why are SortedMap and SortedSet AVL trees?

For keys that must come back in order, a balanced tree answers in key
order by construction. AVL keeps the tree balanced on every insertion and
removal, so every operation is logarithmic in the worst case, with no
randomness and no input that degrades it. The tree is persistent: an
insertion answers a new tree sharing every untouched node with the old.

The representation is private, so it is a choice that can be revisited: a
B-tree would change `sorted_map.fn` and nothing else. The cost against
`Map` is a logarithmic factor and a `cmp` on the key; `len` is also a walk,
since the tree keeps heights, not sizes.

### Why is a container built by the container?

Because which container a list becomes is the caller's to say, and the
choice decides both the order and what the key must have: `Map.counted`
answers in first-seen order and needs `hash_into`, `SortedMap.counted` in
ascending order and needs `cmp`. As methods on `List`, `group_by` and
`counts` had to pick one container, and made the list module depend on the
map module. On the container, the same names serve both, and `List` depends
on neither. The cost is that a count reads `Map.counted(words)` rather than
chaining `words.counted()`.

### Why is `hash_into` generic over a hasher it cannot read?

It separates what a key is from how it is mixed. The key's author knows
which parts make it up and in what order; the container's author knows how
to mix them. A key that could read a digest could depend on the mixing,
and then the mixer could never change. With the hasher write-only, a key's
`hash_into` serves `Mixer` and any hasher a library writes, and a derived
`hash_into` is the same few lines for every type.

Rust's `Hash` is generic over a `Hasher` too, but that trait has `finish`,
so a key's `hash` can read one. Faun's alias leaves it out. The cost is a
`where Hasher(h)` on each hand-written `hash_into`, and on a derived one's
signature.

### Why can a map not take a hasher of its own choosing yet?

Because, with insertion order, a hasher choice changes only speed and how
well a map resists colliding keys, not what any program answers, and that
is `Mixer`'s to get right. A library that needs another hasher writes it,
with a container over it, and reuses every `hash_into`.

A different need is open: comparing keys another way, such as case-blind
strings or a reversed order. Today that takes a wrapper key with its own
`equals`, `hash_into` or `cmp`, wrapped at every insert and lookup. The
[policies draft](../proposals/drafts/policies.md), an open proposal, would
let a container take a policy as a type parameter, `Map(k, v, p)`, whose
methods say which keys are the same and in what order they go. It keeps
the hasher `Mixer`'s, and it would add a parameter to every signature that
names a container.

## Related

- [Tags](tags.md): the structural tags a lookup answers on a miss
- [Records](records.md) and [tuples](tuples.md): keys with `equals` and
  `hash_into` they never declare, and why only tuples have `cmp`
- [Methods](../forms/methods.md): asking for a derived `hash_into`
- [Types](../types.md): `where` bounds and constraint aliases such as
  `Hasher(h)`
- [Memory](../machine/memory.md): in-place updates of a list nothing else
  holds
