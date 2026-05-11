{ inputs, ... }:
{
  perSystem =
    {
      config,
      pkgs,
      system,
      ...
    }:
    let
      inherit (pkgs) lib;

      # Include this cluster + the sibling leios-trace-hs referenced by
      # cabal.project's `packages: . ../leios-trace-hs`. haskell.nix is told
      # the cabal.project is in the subdir, so the relative `..` resolves
      # correctly inside src.
      src = lib.fileset.toSource {
        root = ./..;
        fileset = lib.fileset.unions [
          ./.
          ../leios-trace-hs
        ];
      };

      hsProject = import (inputs.self + "/nix/mk-haskell-project.nix") { inherit inputs system; } {
        name = "ouroboros-leios-sim";
        inherit src;
        cabalProjectFileName = "simulation/cabal.project";
      };
    in
    {
      devShells.dev-simulation = pkgs.mkShell {
        buildInputs =
          config.pre-commit.settings.enabledPackages
          ++ (with pkgs; [
            zlib
            cairo
            pango
            glib
            gtk3
            graphviz
            gnuplot
            sqlite
          ]);
        nativeBuildInputs = [
          hsProject.hpkgs.ghc
          pkgs.cabal-install
          hsProject.hpkgs.haskell-language-server
          hsProject.hpkgs.fourmolu
          pkgs.pkg-config
        ];
        shellHook = ''
          ${config.pre-commit.settings.shellHook}
          echo
          echo "simulation dev shell. Build from this directory:"
          echo "  cabal build all"
        '';
      };

      legacyPackages.simulation = hsProject.flake;
    };
}
