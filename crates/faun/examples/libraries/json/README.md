# JSON

Parse JSON text into a `Json` tree, render a tree as text, and decode a tree
into your own types or build one from them. Codecs are written out, a line a
member, and nothing is derived; a type with its own `from_json` is found by
its type wherever a member of it is read, so codecs compose.

```ruby
package {
  json: "../src/json"
}

import json {Json, Decode, Fields}

User : {name: Str, age: Nat, tags: List(Str)}.(
  from_json : Json -> Decode(User)
  from_json(value) -> (
    fields = Fields.of(value)
    fields.finish(Decode.sequence({
      name: fields.string("name").required(),
      age: fields.nat("age").required(),
      tags: fields.list("tags", Json.string).default([]),
    })).map(User)
  )

  to_json : User -> Json
  to_json(User(user)) -> Json.object([
    ("name", Json.of_str(user.name)),
    ("age", Json.of_nat(user.age)),
    ("tags", Json.of_list(user.tags, Json.of_str)),
  ])
)
```

[`examples/basic.fn`](examples/basic.fn) adds a tagged union, a record
holding other codecs, maps, `null`, and the round trip that checks a codec.

## Parsing and rendering

`Json.from_str(text)` answers a `Json` or a `ParseError`, which says what was
wrong and the line and column where parsing stopped:
`unexpected JSON token at line 3, column 11`. The grammar is RFC 8259's
exactly, so `[1,]` and `01` are refused.

A number without a fraction or an exponent is an `Int`, of any size, and one
with either is a `Float`, the nearest `F64`. A string's escapes, surrogate
pairs included, are decoded to UTF-8.

`value.to_str()` writes compact text, and `value.pretty()` writes one
element or member to a line, indented two spaces a level. A float that is
not finite has no JSON spelling and is written `null`.

To read a tree without decoding it, `value.get("name")` answers an object's
member and `value.at(0)` an array's element, each a `Result` for `?`.

## Decoding

A decoder answers a `Decode(a)`: `Decoded` with the value, or `Failed` with
a `DecodeError` that says where it failed. `.result()` turns it into a
`Result`:

```text
at field `events`: at array index 1: at field `x`: expected u16
```

An object is read through `Fields.of(value)`, bound once. Each member is
read by name and kind, then told what its absence means:

| Read                                | Decodes                             |
| ----------------------------------- | ----------------------------------- |
| `fields.string("name")`, `nat`, ... | one of the standard types           |
| `fields.decode("owner")`            | a type with its own `from_json`     |
| `fields.list("events", decoder)`    | an array, each element by `decoder` |
| `fields.field("prices", decoder)`   | the member by any decoder           |

| Then                 | Where the member is absent |
| -------------------- | -------------------------- |
| `.required()`        | refused                    |
| `.default(fallback)` | `fallback`                 |
| `.opt()`             | `Err(Missing)`             |

`Decode.sequence({...})` gathers a record's members, and `fields.finish`
refuses any member no field read; `fields.finish_loose` lets them pass. A
member written twice is refused either way.

The standard types decode with `Json.string`, `boolean`, `int`, `nat`,
`u8` to `u64` and `f64`. `value.array(decoder)` reads an array,
`value.object_of(decoder)` reads an object as a `Map(Str, a)`, and
`value.nullable(decoder)` reads `null` as `Err(Missing)`.
`value.string_as(reader)` reads a string through a reader such as a tag's
own `from_str`.

A tagged union reads its tag, then lets the tag choose the rest with
`and_then`, handing the fields along:

```ruby
from_json(value) -> (
  fields = Fields.of(value)
  fields.finish(fields.string("type").required().and_then(fields, body))
)

body("scroll", fields) -> fields.int("amount").required().map(Scroll)
body("quit", _) -> Decoded(Quit, [])
body(other, _) -> Failed(InvalidValue("unknown event `${other}`"))
```

## Encoding

`Json.object([(name, value), ...])` builds an object in the order given.
Values come from `Json.of_str`, `of_bool`, `of_int`, `of_nat`, `of_u8` to
`of_u64`, `of_f64`, `of_list(values, encode)` and `of_map(map, encode)`, or
from a type's own `to_json`.

## Writing a codec

A codec names each wire key twice, once in each direction, and nothing
checks that the two agree. An expectation that encodes a value and decodes
it again catches a key misspelled one way:

```ruby
expect User.from_json(ada.to_json()).result() == Ok(ada)
```

## Performance

[`bench/`](bench) times parsing, and decoding with writing back, against
serde_json, Node and Python on the same input; `python3 bench/run.py --cpu 3`
runs it. The results and what they found are in the
[JSON performance note](../../../../../notes/json-performance.md).

## Why it is shaped this way

- **`Fields` is bound once, and decoders are called, not stored.** A Faun
  function is passed and called but never kept in a value, so decoders are
  not values to combine as Elm's are. Each read scans the members for its
  name and answers at once, and the names read travel with the result, which
  is how `finish` knows what nothing read.
- **Nothing is derived.** A codec says every wire name, default and kind,
  and renaming a field in Faun does not change the format. A type's
  `from_json` is reached through a `where` bound, as `to_str` is, so the
  library blesses no protocol.
- **Integers keep every digit.** An `Int` is arbitrary precision, so an
  identifier larger than 2^53 survives a round trip, where JavaScript and
  many libraries round it.
