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
      hpkgs = pkgs.haskell.packages.ghc910;

      hnPkgs = import ../../../nix/haskell-nix-pkgs.nix { inherit inputs system; };
      project = hnPkgs.haskell-nix.cabalProject' {
        name = "betti0";
        src = ./.;
        compiler-nix-name = "ghc9101";
        inputMap = {
          "https://chap.intersectmbo.org/" = inputs.CHaP;
        };
        shell.withHoogle = false;
      };
      flake = project.flake { };
    in
    {
      devShells.dev-post-cip-tx-measurements-betti0 = pkgs.mkShell {
        buildInputs = config.pre-commit.settings.enabledPackages ++ [
          pkgs.zlib
        ];
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
          echo "betti0 dev shell. Build from this directory:"
          echo "  cabal build all"
        '';
      };

      legacyPackages.betti0 = flake;
    };
}
