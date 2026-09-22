# Primary frontend standard library

`standard.fn` is the bootstrap package root. It exports `Bool`, `Never`, `Nat`,
`Int`, `U8`, `List`, `Result`, and `Str` from sibling modules.

```sh
ORI_STD=crates/frontend/standard/standard.fn \
  cargo run -- check notes/examples/utilities.fn
ORI_STD=crates/frontend/standard/standard.fn \
  cargo run -- lower --host x86-64-linux notes/examples/main.fn
```

The package deliberately omits hashing, tuples, record rows and updates, method
constraints, and bodyless derivation. Concrete core equality methods are written manually;
generic equality for `List` and `Result` waits for method constraints.

`Never` is the uninhabited result type used by applications. Files under
`hosts/` are target-selected modules mounted at `std.host`; each initial module
provides `Host : {argc: Nat}` and bodyless `exit! : Host Nat -> Never`. The
`Host` constructor remains private, so only the synthesized startup adapter can
create that authority value.
