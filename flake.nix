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
            # Each test in a process of its own, as `just test` and CI run
            # them: several tests build into a directory named by the
            # process, which side by side in one would remove each other's.
            useNextest = true;
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
          # Every tool but Python, which the evaluator's shell takes with a
          # library the default one has no use for.
          tools = with pkgs; [
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
          ];
          # cc65's sim65 saying, where `SIM65_METRICS` is set, how many cycles
          # a program took and how many bytes of memory it wrote. Only the
          # simulator is built, the rest of cc65 being the default shell's.
          sim65 = pkgs.gccStdenv.mkDerivation {
            pname = "sim65-metrics";
            inherit (pkgs.cc65) version src;
            patches = [ ./eval/sim65-metrics.patch ];
            buildPhase = "make -C src sim65";
            installPhase = "install -Dm755 bin/sim65 $out/bin/sim65";
          };
          # Clang for wasm32 WASI with its C library, and the linker clang
          # looks for by name.
          wasi = pkgs.pkgsCross.wasi32;
          wasiCc = pkgs.writeShellScript "wasi-cc" ''
            PATH=${wasi.buildPackages.llvmPackages.lld}/bin:$PATH
            exec ${wasi.stdenv.cc}/bin/wasm32-unknown-wasi-cc "$@"
          '';
        in
        {
          default = pkgs.mkShell {
            packages = tools ++ [ pkgs.python3 ];
          };
          # What `just eval` measures with, as RATCHET.md says: kept out of
          # the default shell so that everyday work and CI need not fetch a
          # second C compiler or build an emulator.
          eval = pkgs.mkShell {
            packages = tools ++ [ (pkgs.python3.withPackages (python: [ python.wasmtime ])) ];
            # Named rather than put on the path: a cross compiler there
            # would become the shell's `CC`, and this sim65 is not the tests'.
            WASI_CC = wasiCc;
            SIM65 = "${sim65}/bin/sim65";
          };
        }
      );
    };
}
