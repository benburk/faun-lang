# Primary frontend standard library

`standard.fn` is the bootstrap package root. It exports `Bool`, `Nat`, `Int`,
`U8`, `List`, `Result`, and `Str` from sibling modules.

```sh
ORI_STD=crates/frontend/standard/standard.fn \
  cargo run -- check notes/examples/utilities.fn
ORI_STD=crates/frontend/standard/standard.fn \
  cargo run -- lower --entry mapped notes/examples/utilities.fn
```

The package deliberately omits hashing, records, tuples, method constraints,
and bodyless derivation. Concrete core equality methods are written manually;
generic equality for `List` and `Result` waits for method constraints.
