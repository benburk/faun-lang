# tree-sitter-faun

A tree-sitter grammar for Faun, for editors: Helix highlights, indents, and
selects by it.

`grammar.js` ports `crates/faun/src/grammar.ebnf` rule for rule. What the
compiler's lexer reads by looking past a token, `src/scanner.c` reads here:
where a line ends, and whether a name's `!` makes it an effect's. Lines stay
flat, as in the EBNF, so a clause's body is the lines after it rather than a
node under it.

`just tree-sitter`, part of `just test`, generates the parser, runs the corpus
in `test/corpus`, and reads every `.fn` file in the repository, failing on
any error. A change to `grammar.ebnf` goes here too. The generated parser in
`src/` is committed, so editors build it without the tree-sitter CLI or Node;
`just check` fails if it is stale.

## Helix

Helix needs three things: the language, declared in `languages.toml`; the
parser, as `runtime/grammars/faun.so`; and the queries, as
`runtime/queries/faun/`. The runtime is `~/.config/helix/runtime`. The queries
here use Helix's scopes; another editor would need its own.

Declare the language in `~/.config/helix/languages.toml`. Editing inside this
repository, `.helix/languages.toml` already does.

```toml
[[language]]
name = "faun"
scope = "source.faun"
file-types = ["fn"]
comment-token = "#"
indent = { tab-width = 2, unit = "  " }
roots = []
```

Then install the parser and queries one of three ways, and check with
`hx --health faun`, which should tick the parser and all three queries.

**From a clone, with Nix.** `just helix` builds the grammar and links it and
its queries into the runtime, where garbage collection leaves them. Rerun it
after the grammar or a query changes.

**Without a clone, with Nix.** The flake's `tree-sitter-faun` package holds
`parser` and `queries/`; link them into the runtime by hand, or with
home-manager:

```nix
xdg.configFile = {
  "helix/runtime/grammars/faun.so".source = "${faun.packages.${system}.tree-sitter-faun}/parser";
  "helix/runtime/queries/faun".source = "${faun.packages.${system}.tree-sitter-faun}/queries";
};
```

**Without Nix.** Let Helix fetch and build the grammar, which needs git and a
C compiler. Add to `languages.toml`, pinning a commit:

```toml
[[grammar]]
name = "faun"
source = { git = "https://github.com/cullback/faun-lang", rev = "<commit>", subpath = "editors/tree-sitter-faun" }
```

and run:

```sh
mkdir -p ~/.config/helix/runtime/grammars ~/.config/helix/runtime/queries
hx --grammar fetch && hx --grammar build
git clone https://github.com/cullback/faun-lang ~/src/faun-lang
ln -s ~/src/faun-lang/editors/tree-sitter-faun/queries ~/.config/helix/runtime/queries/faun
```

Helix fetches no queries with a grammar, hence the clone.

## Where it reads more than the compiler

The grammar reads every program the compiler reads, and refuses most of what
it refuses, but not all: an editor needs a tree, not a verdict.

- `.`, `..` and `.*` may stand apart from what they join, as in `x .y`. The
  compiler allows a detached `.` only at a line's start, and tree-sitter
  cannot tell a space from a line break there without scanning every `.`.
- What `lines.rs` refuses after reading, such as a `_` left in an expression
  or a binding after a body's answer, is read without complaint.
