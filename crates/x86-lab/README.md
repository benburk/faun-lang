# Experimental x86-64 Linux backend

This crate starts with the x86 emitter and machine IR from Faun commit
`711f676`. The CLI selects it with `--backend=x86-lab` for `build`,
`run`, `test` and `emit`. The host is `x86_64-linux`.

The frontend produces the same optimized Barb program for both backends.
In this crate, `src/ir/lower.rs` lowers it to the local machine IR,
`src/ir/ownership.rs` and `src/ir/uniqueness.rs` provide ownership
analysis, and `src/ir/legalize.rs` lowers representations to scalar code.
`src/selected.rs`, `src/encode.rs` and `src/elf.rs` select instructions,
encode them and write the executable. The crate shares Barb, the register
allocator and general utilities with the stock compiler.

From the implementation worktree:

```sh
nix develop -c cargo build --locked --release -p faun-cli
target/release/faun build --backend=x86-lab crates/faun/examples/hello.fn -o target/hello-lab
target/release/faun emit --backend=x86-lab machine crates/faun/examples/hello.fn
```

Measure future changes from the prep worktree with the
[experiment contract](../faun/examples/benchmarks-game/LAB.md).
