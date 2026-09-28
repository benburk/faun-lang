# Repository guidance

Apply [rust-module-design](.claude/skills/rust-module-design/SKILL.md) for substantial
Rust design, refactoring, and review.

Read the relevant contracts: [Barb](crates/core/src/barb/README.md),
[machine IR](notes/machine-ir.md), and the [primary standard library](crates/faun/standard/README.md).
Migrate callers and docs together; preserve useful coverage across all three backends.
A program the compiler refuses is a case in `crates/cli/tests/refused/`, with what
`faun check` says in its `.err`; run `just bless` after changing a message and review the diff.

Validate with `nix develop --command just check` and
`nix develop --command just test`.
