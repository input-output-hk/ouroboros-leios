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
        name = "leios-trace-hs";
        src = ./.;
      };
    in
    {
      devShells.dev-leios-trace-hs = pkgs.mkShell {
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
          echo "leios-trace-hs dev shell. Build from this directory:"
          echo "  cabal build all"
        '';
      };

      legacyPackages.leios-trace-hs = hsProject.flake;
    };
}
