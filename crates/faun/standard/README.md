# Primary frontend standard library

`standard.fn` is the bootstrap package root. It exports `Bool`, `Never`, `Nat`,
`Int`, `U8`, `List`, `Result`, and `Str` from sibling modules.

```sh
cargo run -- check notes/examples/utilities.fn
cargo run -- lower --target x86_64-linux notes/examples/main.fn
```

The package deliberately omits hashing, tuples, record rows and updates, method
constraints, and bodyless derivation. Concrete core equality methods are written manually;
generic equality for `List` and `Result` waits for method constraints.

`Nat`, `Int`, and `U8` define `+`, `-`, `*`, `/`, and `%`. Natural subtraction is
monus. Signed division truncates toward zero and its remainder has the dividend's
sign. For every type, division by zero returns zero and `a % 0` returns `a`.
`U8` arithmetic uses unsigned representatives and wraps modulo 256; in particular,
`0 - 1` is 255 rather than natural zero.

`Never` is the uninhabited result type used by applications. Files under
`hosts/` are target-selected modules mounted at `std.host`; each initial module
provides `Host : {argc: Nat}` and bodyless `exit! : Host Nat -> Never`. The
`Host` constructor remains private, so only the synthesized startup adapter can
create that authority value.
