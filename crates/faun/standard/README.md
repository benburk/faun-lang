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
ordinary available constructor spelling. `host.fn` is mounted at `std.host` for
every standard target. It provides a `Host` carrying nothing, a `Unit` for
effects answering nothing, and bodyless `argc! : Host -> Nat`,
`exit! : Host Nat -> []`, `write! : Host Str -> Unit` and
`read_byte! : Host -> Nat`, which answers nought at the end of input and one
more than the byte otherwise. The `Host` constructor remains private.

`Host` is authority and nothing else. It carries no startup payload, so what a
host module offers it offers as ordinary bodyless declarations taking one, and
a program orders its effects by threading that authority through them. Barb
retains the parameter and the threading; both are erased below it, because a
type with one value says nothing by being itself. So the machine entry takes
nothing and no target binds a startup parameter by name to supply it.
