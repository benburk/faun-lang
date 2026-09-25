# Primary frontend standard library

`standard.fn` is the bootstrap package root. It exports `Bool`, `Nat`, `Int`,
`U8`, `List`, `Result`, and `Str` from sibling modules.

`List` follows Ori's standard list wherever a function needs no tuples,
records, method constraints, or `?`: `len`, `is_empty`, `append`, `extend`,
`prepend`, `map`, `map2`, `flat_map`, `flatten`, `join`, `filter`, `count`,
`any`, `all`, `fold`, `fold_right`, `trail`, `reverse`, `first`, `last`,
`get`, `get_or`, `set`, `find`, `find_index`, `take`, `drop`, `take_while`,
`drop_while`, and the constructors `List.range(n)` and `List.repeat(x n)`. A
lookup that can miss answers `Err(OutOfBounds)`, `Err(Empty)` or
`Err(NotFound)`. Ori's are loose tags; until Faun has those, each is a
nominal one-constructor type the list module exports, spelled the same at
every use. Nothing is recognized by name: `len` is answered from the length a
list holds because Barb recognizes what it computes.

```sh
cargo run -- check crates/faun/examples/utilities.fn
cargo run -- emit --target x86_64-linux barb crates/faun/examples/main.fn
```

The package deliberately omits hashing, tuples, record rows and updates, method
constraints, and bodyless derivation. Concrete core equality methods are written manually;
generic equality for `List` and `Result` waits for method constraints.

`Nat`, `Int`, and `U8` define `+`, `-`, `*`, `/`, and `%`. Natural subtraction is
monus. Signed division truncates toward zero and its remainder has the dividend's
sign. For every type, division by zero returns zero and `a % 0` returns `a`.
`U8` arithmetic uses unsigned representatives and wraps modulo 256; in particular,
`0 - 1` is 255 rather than natural zero.

The structural empty variant type `[]` is the uninhabited result used by
applications; it needs no blessed standard-library name. `Never` remains an
ordinary available constructor spelling. Each target has its own host module,
`hosts/<target>.fn`, mounted at `std.host`. They start out identical and will
diverge as targets offer different capabilities. Each declares

```
Host : {argc: Nat}.(
  exit! : Host Nat -> []
  write! : Host Str -> {}
  read_byte! : Host -> Nat
)
```

where `read_byte!` answers nought at the end of input and one more than the
byte otherwise. The `Host` constructor remains private, so only the target
makes one.

`Host` is authority carrying the startup values its target produces. A field
such as `host.argc` is read like any record field; the target produces it into
the entry's frame before `main!` runs, and nothing asks for it again. In Barb,
`Host` holds its fields itself, `Host(argc: Nat)`, and `main!` is the entry as
written; nothing there says how wide `argc` is. Machine lowering recognizes a
field named for one of the target's startup values, holds it as the target's
startup table says, names the entry's parameter for it, and drops the ones
nothing reads, so a target produces only the startup values a program uses. A
read field the target cannot produce is refused by the target.

`Host`'s bodyless methods are the effects the target answers for, called as
`host.write!(text)`. A program orders its effects by threading `Host` through
them. Barb calls each routine with the `Host` it was handed, as the source
says, and keeps the order and number of calls to anything bodyless. A routine
asked with authority reads nothing of it, so machine lowering hands nothing
for it, and passing `Host` along is not reading what it carries: a program
that never reads `host.argc` makes its target produce nothing.
