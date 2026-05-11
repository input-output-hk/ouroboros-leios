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
        name = "leios-deltaq";
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
      devShells.dev-analysis-deltaq-linear-leios = pkgs.mkShell {
        buildInputs = config.pre-commit.settings.enabledPackages ++ [
          pkgs.zlib
          pkgs.cairo
          pkgs.pango
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
          echo "leios-deltaq dev shell. Build from this directory:"
          echo "  cabal build all"
          echo "For local deltaq fork: drop a cabal.project.local with"
          echo "  packages: <path/to/fork>/lib/deltaq <path/to/fork>/lib/probability-polynomial"
          echo "and comment out the source-repository-package in cabal.project."
        '';
      };

      legacyPackages.leios-deltaq = flake;
    };
}
