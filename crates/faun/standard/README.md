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
ordinary available constructor spelling. Files under `hosts/`
are target-selected modules mounted at `std.host`; each initial module provides
`Host : {argc: Nat}` and bodyless `exit! : Host Nat -> []`. The
`Host` constructor remains private. Barb nevertheless retains the target-provided
value and its projections; the target constructs the represented `host` entry
parameter in its physical startup adapter.
