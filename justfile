# Display available recipes
default:
    just --list --unsorted

# Install dependencies and set up the development environment
bootstrap:
    cargo build

alias fmt := format

# Format code
format:
    just --fmt
    dprint fmt
    cargo fmt --all
    fd -e nix -X nixfmt
    rg -l '[^\n]\z' --multiline . | xargs -r sed -i -e '$a\\'

# Run linters and static analysis
check:
    just --fmt --check
    dprint check
    @fd -e md --hidden -E .git -X awk '/^[[:space:]]*[|]/ && length($0) > 80 {print FILENAME ":" FNR ": table row is " length($0) " chars (>80)"; bad=1} END {exit bad}'
    cargo fmt --all -- --check
    cargo clippy --workspace --all-targets -- -D warnings
    RUSTDOCFLAGS='-D warnings' cargo doc --workspace --no-deps
    fd -e nix -X nixfmt --check
    ! rg -l '[^\n]\z' --multiline .
    just tree-sitter-fresh

# Run the test suite: every test at once, the doc tests nextest skips, then the tree-sitter grammar's
test:
    cargo nextest run --workspace
    cargo test --workspace --doc
    just tree-sitter

# Generate the tree-sitter grammar, run its corpus, and read every program with it
tree-sitter:
    cd editors/tree-sitter-faun && tree-sitter generate && tree-sitter test
    fd -e fn -0 | xargs -0 tree-sitter parse --quiet --stat -p editors/tree-sitter-faun

# Fail if the committed tree-sitter parser is not what grammar.js generates
[private]
tree-sitter-fresh:
    #!/usr/bin/env bash
    set -euo pipefail
    out=$(mktemp -d)
    trap 'rm -rf "$out"' EXIT
    cd editors/tree-sitter-faun
    tree-sitter generate -o "$out"
    if ! diff -rq -x scanner.c "$out" src; then
        echo "editors/tree-sitter-faun/src is stale: run just tree-sitter and commit it" >&2
        exit 1
    fi

# Build the tree-sitter grammar and link it, with its queries, into Helix's runtime
helix:
    #!/usr/bin/env bash
    set -euo pipefail
    runtime="${XDG_CONFIG_HOME:-$HOME/.config}/helix/runtime"
    mkdir -p "$runtime/grammars" "$runtime/queries"
    # The out-link keeps the build from garbage collection.
    nix build .#tree-sitter-faun --out-link "$runtime/tree-sitter-faun"
    ln -sfn ../tree-sitter-faun/parser "$runtime/grammars/faun.so"
    ln -sfn ../tree-sitter-faun/queries "$runtime/queries/faun"

# Write every refused program's .err from what the compiler says now; read the diff
bless:
    FAUN_BLESS=1 cargo nextest run -p faun-cli --test refused

# Build release binary
build:
    cargo build --release

# Run the project
run *args:
    cargo run -- {{ args }}
