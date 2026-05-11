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
      hsProject = import (inputs.self + "/nix/mk-haskell-project.nix") { inherit inputs system; } {
        name = "leios-deltaq";
        src = ./.;
      };
    in
    {
      devShells.dev-analysis-deltaq-linear-leios = pkgs.mkShell {
        buildInputs = config.pre-commit.settings.enabledPackages ++ [
          pkgs.zlib
          pkgs.cairo
          pkgs.pango
        ];
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
          echo "leios-deltaq dev shell. Build from this directory:"
          echo "  cabal build all"
          echo "For local deltaq fork: drop a cabal.project.local with"
          echo "  packages: <path/to/fork>/lib/deltaq <path/to/fork>/lib/probability-polynomial"
          echo "and comment out the source-repository-package in cabal.project."
        '';
      };

      legacyPackages.leios-deltaq = hsProject.flake;
    };
}
