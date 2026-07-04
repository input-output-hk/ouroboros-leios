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
        name = "betti0";
        src = ./.;
      };
    in
    {
      devShells.dev-post-cip-tx-measurements-betti0 = pkgs.mkShell {
        buildInputs = config.pre-commit.settings.enabledPackages ++ [
          pkgs.zlib
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
          echo "betti0 dev shell. Build from this directory:"
          echo "  cabal build all"
        '';
      };

      legacyPackages.betti0 = hsProject.flake;
    };
}
