{
  description = "Ouroboros Leios";

  nixConfig = {
    extra-substituters = [
      "https://cache.iog.io"
      "https://tweag-jupyter.cachix.org"
    ];
    extra-trusted-public-keys = [
      "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ="
      "tweag-jupyter.cachix.org-1:UtNH4Zs6hVUFpFBTLaA4ejYavPo5EFFqgd7G7FxGW9g="
    ];
    allow-import-from-derivation = true;
  };

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";

    iogx.url = "github:input-output-hk/iogx";

    leios-spec.url = "github:input-output-hk/ouroboros-leios-formal-spec?rev=a654a1761476fcf8e6a43aeedbc1455bd7ad77db";

    flake-parts.url = "github:hercules-ci/flake-parts";

    pre-commit-hooks.url = "github:cachix/git-hooks.nix";

    # Used by analysis/deltaq/
    jupyenv.url = "github:tweag/jupyenv";
    # NOTE: Also pinned in cabal.project (source-repository-package) for the
    # Haskell build. Keep both pins in sync.
    deltaq-src.url = "github:DeltaQ-SD/deltaq";
    deltaq-src.flake = false;

    # Used by demo/
    ouroboros-consensus.url = "github:intersectmbo/ouroboros-consensus?ref=bladyjoker/leios-in-praos"; # TODO(bladyjoker): Update ref before merging
    cardano-node-leios.url = "github:intersectmbo/cardano-node?ref=bladyjoker/leios-integrate-837"; # TODO(bladyjoker): Update ref before merging
    cardano-node.url = "github:intersectmbo/cardano-node?ref=bench/leios"; # For latest tools
  };

  outputs =
    inputs@{
      self,
      nixpkgs,
      flake-parts,
      ...
    }:
    let
      inherit (nixpkgs) lib;
      # Collect all the build.nix files (flake-parts modules)
      buildDotNixes = import ./nix/findFilesRecursive.nix {
        inherit lib;
        toInclude = lib.hasSuffix "build.nix";
        dir = ./.;
      };
    in
    flake-parts.lib.mkFlake { inherit inputs; } {

      imports = [
        inputs.pre-commit-hooks.flakeModule
        ./nix/pkgs.nix
      ]
      ++ buildDotNixes;

      debug = true;

      systems = [
        "x86_64-linux"
        "x86_64-darwin"
        "aarch64-linux"
        "aarch64-darwin"
      ];

      flake.hydraJobs = import ./nix/hydra.nix {
        flake = self;
        inherit lib;
        systems = [
          "x86_64-linux"
          "x86_64-darwin"
          "aarch64-linux"
          "aarch64-darwin"
        ];
      };

    };

}
