# Primary frontend standard library

`standard.fn` is the bootstrap package root. It exports `Bool`, `Nat`, `Int`,
`U8`, `List`, `Result`, and `Str` from sibling modules.

```sh
cargo run -- check crates/faun/examples/utilities.fn
cargo run -- build --emit barb --target x86_64-linux crates/faun/examples/main.fn
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
the entry's frame before `main!` runs, and nothing asks for it again. Lowering
generates a Barb entry `start` taking one named parameter per field, which
builds `Host` and calls `main!`. Machine lowering drops parameters nothing
reads, so a target produces only the startup values a program uses. A field
the target cannot produce is refused when lowering.

`Host`'s bodyless methods are the effects the target answers for, called as
`host.write!(text)`. A program orders its effects by threading `Host` through
them. Barb declares and calls each routine without its `Host` receiver, since
the target answers the same whoever asks; Barb keeps the order and number of
calls to anything bodyless.
