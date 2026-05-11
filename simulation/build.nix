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
      hpkgs = pkgs.haskell.packages.ghc910;

      hnPkgs = import ../nix/haskell-nix-pkgs.nix { inherit inputs system; };

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

      project = hnPkgs.haskell-nix.cabalProject' {
        name = "ouroboros-leios-sim";
        inherit src;
        cabalProjectFileName = "simulation/cabal.project";
        compiler-nix-name = "ghc9101";
        inputMap = {
          "https://chap.intersectmbo.org/" = inputs.CHaP;
        };
        shell.withHoogle = false;
      };
      flake = project.flake { };
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
          hpkgs.ghc
          pkgs.cabal-install
          hpkgs.haskell-language-server
          hpkgs.fourmolu
          pkgs.pkg-config
        ];
        shellHook = ''
          ${config.pre-commit.settings.shellHook}
          echo
          echo "simulation dev shell. Build from this directory:"
          echo "  cabal build all"
        '';
      };

      legacyPackages.simulation = flake;
    };
}
