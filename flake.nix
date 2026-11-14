{
  inputs.nixpkgs.url = "github:nixos/nixpkgs/nixos-26.05";

  outputs =
    { self, nixpkgs }:
    let
      supportedSystems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      forAllSystems = nixpkgs.lib.genAttrs supportedSystems;
      # The command is one crate of several, and its manifest is the one
      # place it is named. The version is the workspace's, being every
      # crate's.
      cargoToml = builtins.fromTOML (builtins.readFile ./crates/cli/Cargo.toml);
      workspace = builtins.fromTOML (builtins.readFile ./Cargo.toml);
    in
    {
      packages = forAllSystems (
        system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in
        {
          default = pkgs.rustPlatform.buildRustPackage {
            pname = cargoToml.package.name;
            version = workspace.workspace.package.version;
            src = ./.;
            cargoLock.lockFile = ./Cargo.lock;
            meta = {
              mainProgram = "faun";
            };
          };
          # The parser as an editor loads it, at `parser`, with its queries.
          tree-sitter-faun = pkgs.tree-sitter.buildGrammar {
            language = "faun";
            version = workspace.workspace.package.version;
            src = ./editors/tree-sitter-faun;
          };
        }
      );

      devShells = forAllSystems (
        system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in
        {
          default = pkgs.mkShell {
            packages = with pkgs; [
              just
              dprint
              fd
              ripgrep
              nixfmt
              cargo
              rustc
              clippy
              rustfmt
              rust-analyzer
              # `just test` runs the tests with nextest, and the backends'
              # programs on wasmtime and cc65's sim65.
              cargo-nextest
              wasmtime
              cc65
              # `just tree-sitter` generates the grammar from grammar.js,
              # which tree-sitter evaluates with node.
              tree-sitter
              nodejs
              # The benchmarks game's C pidigits does its arithmetic with GMP.
              gmp
              python3
            ];
          };
        }
      );
    };
}
