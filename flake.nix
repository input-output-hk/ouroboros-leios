{
  description = "Ouroboros Leios";

  nixConfig = {
    extra-substituters = [
      "https://cache.iog.io"
    ];
    extra-trusted-public-keys = [
      "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ="
    ];
    allow-import-from-derivation = true;
  };

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";

    iogx.url = "github:input-output-hk/iogx";

    leios-spec.url = "github:input-output-hk/ouroboros-leios-formal-spec?rev=2ccae64440bf8834cbed69acfd1993a808b9046a";

    flake-parts.url = "github:hercules-ci/flake-parts";

    pre-commit-hooks.url = "github:cachix/git-hooks.nix";
  };

  outputs =
    inputs@{
      nixpkgs,
      flake-parts,
      ...
    }:
    let
      inherit (nixpkgs) lib;
      # Collect all the build.nix files (flake-parts module)
      buildDotNixes = import ./nix/findFilesRecursive.nix {
        inherit lib;
        toInclude = lib.hasSuffix "build.nix";
        dir = ./.;
      };
    in
    flake-parts.lib.mkFlake { inherit inputs; } {

      imports = [
        inputs.pre-commit-hooks.flakeModule
        ./pkgs.nix
      ]
      ++ buildDotNixes;

      debug = true;

      systems = [
        "x86_64-linux"
        # "x86_64-darwin"
        # "aarch64-linux"
        # "aarch64-darwin"
      ];
    };

}
