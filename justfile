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

# Run the test suite: every test at once, then the doc tests nextest skips
test:
    cargo nextest run --workspace
    cargo test --workspace --doc

# Write every refused program's .err from what the compiler says now; read the diff
bless:
    FAUN_BLESS=1 cargo nextest run -p faun-cli --test refused

# Build release binary
build:
    cargo build --release

# Run the project
run *args:
    cargo run -- {{ args }}
