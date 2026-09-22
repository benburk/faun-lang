# Repository guidance

Apply [rust-module-design](.claude/skills/rust-module-design/SKILL.md) for substantial
Rust design, refactoring, and review.

Read the relevant contracts: [Barb](crates/faun/src/barb/README.md),
[machine IR](notes/machine-ir.md), and the [primary standard library](crates/frontend/standard/README.md).
Migrate callers and docs together; preserve useful coverage across all three backends.

Validate with `nix develop --command just check` and
`nix develop --command cargo test --workspace`.
