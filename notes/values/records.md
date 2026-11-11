# Records

A record is a product of named fields, `{name: "Ada", age: 36}`. This note
owns records: their structural, unordered types, the open row `*`, field
reads, update, the members a record has without declaring them, and record
builders.

## Records and their types

A record is written with its fields between braces, and its type the same
way: `{name: Str, age: Nat}`. A field may be written `{name}`, short for
`{name: name}`, in a literal, an update or a pattern. `{}` is the empty
record, and serves as the unit value: a block whose last line is a binding
answers `{}`, and `close!` answers `Result({}, CloseError)`.

The type is structural. No declaration is needed, two records with the same
fields have the same type, and the order fields are written in means
nothing: `{x: 1, y: 2}` and `{y: 2, x: 1}` are one value.

A closed record type has exactly the fields it names. `{name: Str, *}` is
open: a record with at least a `name`, whatever else it holds. The `*`
stands for fields that are the caller's business, and it is never named:
`{x, *r}` in a pattern is refused, `{x, *}` takes the rest unnamed.

```ruby
get_name : {name: Str, *} -> Str
get_name(r) -> r.name

expect get_name({name: "Ada", age: 3}) == "Ada"
```

The runners show the open row in use: a program handed to `run_stdin!`
declares only the fields it reads, `app : {stdin: List(U8), *} -> ...`, and
leaves the arguments alone.

### Reading a field

`r.name` reads a field. In an unsigned definition, a read off a value of
unknown type is a bound, met by anything with the field: a record, whatever
else it holds, or a declared type whose record has it.

```ruby
Point : {x: Nat, y: Nat}
x_of(v) -> v.x

expect x_of({x: 4, z: True}) == 4
expect x_of(Point({x: 5, y: 0})) == 5
```

A signature that writes a record, `{x: Nat, *}`, asks for a record, so it
does not take a `Point`; there is no way yet to write a bound on a field
alone. How inference handles rows in general is in [types](../types.md).

### Update

`{x: e, *r}` is `r` with `x` replaced. The `*r` comes last, as the tail does
in `[head, *tail]`, and supplies every field the update does not name. An
update replaces a value: it adds no field and changes no field's type.
Like a read, it works on any record with the field and answers that
record's type. The clap library builds an option's doc this way:

```ruby
flag_parsed(Found(value, claims), doc) -> Value(value, {claims, *doc})
```

An update asks for a record, not a declared type, since it would build the
type without its constructor.

A field named in an update may be a path, replacing a field of a field and
keeping the rest of each record the path goes through. `{a.b: e, *r}` is
`{a: {b: e, *r.a}, *r}`, with `r` worked out once:

```ruby
step(cpu, to) -> {regs.pc: to, flags.zero: False, *cpu}
```

Paths sharing a start are one update of that field, so `regs.pc` and
`regs.sp` together update `regs` once. A field is replaced whole or in
part, never both in one update, and a path is given its value: `{a.b,
*r}` has no name to pun. A path is only an update's: a record with no base
has nothing to keep, and a pattern takes a field of a field apart by
nesting, `{a: {b, *}, *}`.

### Equality, text and hashing

A closed record has `equals`, `to_str` and `hash_into` without declaring
them, each by its fields' own. Equality ignores the order fields were
written in, and so does hashing: one record type always feeds its fields in
one order. Text writes them in the order of their names, so
`"${{y: 2, x: 1}}"` is `"{x: 1, y: 2}"`.

A record with `*` has none of the three: its other fields are a caller's,
and comparing them would make a function's behaviour depend on fields its
signature says it does not know.

```text
error: a record with `*` has no `equals`: its other fields are a caller's
```

A record has no `cmp`, so `a < b` on records is refused. A declared type
over a record may ask for `equals`, `to_str` and `hash_into` by writing
their signatures without bodies, and has the record's; it cannot ask for
`cmp`, and writes its own ([methods](../forms/methods.md)).

## Record builders

A record literal handed alone to a function whose signature pairs two values
of one shape, `(F(a, e), F(b, e), (a, b) -> c) -> F(c, e)`, is that function
applied a field at a time:

```ruby
parse_dimensions(width_text, height_text) -> Result.map2({
  width: Nat.from_str(width_text),
  height: Nat.from_str(height_text),
})

expect parse_dimensions("3", "4") == Ok({width: 3, height: 4})
expect parse_dimensions("3", "x") == Err(Malformed)
```

The first two fields are paired into a record, then that record with the
third, and so on, so every step answers a record and the last is the one
written. Each field is worked out once, in the order written. The `e` stays
fixed, as `Result`'s error type does. `List.map2({x: xs, y: ys})` zips two
lists into a list of records; the JSON and command-line libraries decode
and parse a record's fields with their own `sequence`:

```ruby
fields.finish(Decode.sequence({
  display_name: fields.string("name").required(),
  age: fields.nat("age").required(),
  balance: fields.int("balance").default(0),
  active: fields.boolean("active").default(False),
  scores: fields.list("scores", Json.nat).default([]),
}))
```

A builder needs two fields or more, and a function whose signature is
written: `Result.map2({a: Ok(1)})` is refused as a call of the wrong shape,
and so is a builder call to an unsigned function.

## Rationale

### Why are records structural?

Most records are shapes passed between a few functions: a runner's input,
an option's doc, a decoded line. Declaring a type for each would add a name
and a constructor to wrap and unwrap at every boundary. A structural record
needs neither, and a function reading `.name` serves every record that has
one. Names also prevent the swap a positional product allows: `{width,
height}` cannot be passed as `{height, width}` by mistake, since order means
nothing.

The cost is that an error message names a shape rather than a type. An
alias names the shape without making a new type, as the arena's
`Settings = {seed: Nat, rounds: Nat}` does, and a declared type over a
record gives it methods and, if sealed, a wall.

### Why unordered, and why no `cmp`?

Nothing in `{name, age}` says whether name or age comes first. Equality
needs no order, since fields are matched by name, and text uses name order
only because it needs some fixed order. An ordering of records
would be that same arbitrary choice made into a meaning: a sort by name
order would sort people by age because `age` precedes `name`.

So the order is left to whoever knows the domain. A declared type writes
the `cmp` it means; `sort_on` takes a key, and a tuple key orders by its
positions: `people.sort_on(|p| (p.surname, p.name))`. The cost is a line or
a wrapper wherever records must be ordered.

### Why can the rest not be named?

Naming the rest, `{x, *r}`, would only let a signature say that two records
share the same unnamed fields. That restricts callers rather than giving
the function anything: it still cannot read those fields, since it does not
know them. What the rest holds differs from one call to the next, so a name
has nothing to say about it. Update needs no name either: `{x: e, *r}`
takes the rest from the value `r`, not from a type variable.

### Why may an update name a path?

State threaded through a walk is a record of records: a CPU's registers in
the CPU, an assembler in its cursor. Without paths, changing one field
deep down names every record on the way twice, once to build it and once
to keep its rest:

```ruby
{asm: {macros, *cursor.asm}, lines: cursor.lines.drop(end + 1), *cursor}
```

With them, the line says only what changes, as a read of the same field
would name it:

```ruby
{asm.macros: macros, lines: cursor.lines.drop(end + 1), *cursor}
```

The path is the read's `cursor.asm.macros` with the base moved to the
`*`, so there is nothing new to learn, and the deeper the field the more it
saves: three levels down, the nested form names the base three times.
Lenses, as Haskell has them, do the same and more, composing getters and
setters as values; they are a library and a vocabulary, where a path is
one rule in the update a reader already knows. Writing `.` in a key also
reads as a field read on the left of a `:`, which no other record form
has, and that is the cost: a reader meets `a.b` in a key once and learns it.

Paths stay out of patterns because a pattern already nests, and binding
`{a.b: n, *}` would be a second spelling of `{a: {b: n, *}, *}`.

### Why builders by signature shape, and never by name?

The shape is the whole requirement. A function that pairs two `F`s with a
combiner is enough to fold any number of fields, whatever it is called:
`map2` for `Result` and `List`, `sequence` for the command-line `Match` and
the JSON `Decode`. Keying the feature to a name would bless
one spelling, and a library whose pairing reads better as `sequence` or
`both` would lose it or have to adopt the blessed name. By shape, nothing
is registered and any library gets builders by writing the signature.

The rewrite is safe because Faun has no currying or partial application: a
three-parameter function called with one record is otherwise always a type
error, so the builder reading never changes a program that compiled. The
cost is that the function must have its signature written, since the shape
is read from it.

### Why not let a declared type pass where a record is written?

`Point : {x: Nat, y: Nat}` mints a wrapper; a value of it is a `Point`, not
a record, and an expected type checks an identity rather than converting
one. Letting a `Point` through where `{x: Nat, *}` is written would read
the expected type to strip a constructor, a conversion the language does
not make anywhere else. An unsigned field read already serves both, as
`x_of` above does. The cost is that a signature cannot yet say "anything
with an `x`"; the recourse is to leave that definition unsigned.

## History

- **2026-11-11:** an update's fields may be paths, `{a.b: e, *r}`. Writing
  an assembler in Faun turned up the nested form,
  `{asm: {macros, *cursor.asm}, *cursor}`.

## Related

- [Tags](tags.md): variant rows, the other kind of row, which have no
  written tail
- [Tuples](tuples.md): positional products, which do have `cmp`
- [Types](../types.md): row polymorphism and inference
- [Methods](../forms/methods.md): declared types over records, and asking
  for derived members
- [Effects](../forms/effects.md): a record's fields holding a file are each
  used up on their own
