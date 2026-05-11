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

      hnPkgs = import ../nix/haskell-nix-pkgs.nix { inherit inputs system; };
      project = hnPkgs.haskell-nix.cabalProject' {
        name = "leios-trace-hs";
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
      devShells.dev-leios-trace-hs = pkgs.mkShell {
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
          echo "leios-trace-hs dev shell. Build from this directory:"
          echo "  cabal build all"
        '';
      };

      legacyPackages.leios-trace-hs = flake;
    };
}
