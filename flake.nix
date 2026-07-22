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
    # Keep iogx's API (mkHaskellProject), but bump its pinned package indices
    # forward to 2026 so cardano-api / cardano-cli (leios-prototype) resolve.
    # Without this, plan-to-nix silently falls back to the ~2024-11 index.
    iogx.inputs.CHaP.url = "github:intersectmbo/cardano-haskell-packages/e8a483522ee73c8c9493ea6055553e5c2532e66b";
    # The old haskell.nix can't consume the 2026 hackage.nix; bump it too.
    iogx.inputs.haskell-nix.url = "github:input-output-hk/haskell.nix/ef52c36b9835c77a255befe2a20075ba71e3bfab";
    iogx.inputs.haskell-nix.inputs.hackage.url = "github:input-output-hk/hackage.nix/06fa3e96f4d7ced3496ec984c8016aad5282db67";
    # Some Nix versions resolve the nested override above as iogx's declared
    # `follows = "hackage"` instead, re-locking haskell-nix/hackage to iogx's
    # own hackage pin. Pin that one to the same snapshot so both resolutions
    # agree (otherwise plan-to-nix fails: index older than cabal.project's
    # index-state).
    iogx.inputs.hackage.url = "github:input-output-hk/hackage.nix/06fa3e96f4d7ced3496ec984c8016aad5282db67";

    leios-spec.url = "github:input-output-hk/ouroboros-leios-formal-spec?rev=1f8afb1276183d2cb19bb88e31d0d593dee1ab82";

    flake-parts.url = "github:hercules-ci/flake-parts";

    pre-commit-hooks.url = "github:cachix/git-hooks.nix";

    # Used by analysis/deltaq/
    jupyenv.url = "github:tweag/jupyenv";
    # NOTE: Also pinned in cabal.project (source-repository-package) for the
    # Haskell build. Keep both pins in sync.
    deltaq-src.url = "github:DeltaQ-SD/deltaq";
    deltaq-src.flake = false;

    # Used by demo/
    ouroboros-consensus.url = "github:intersectmbo/ouroboros-consensus?ref=leios-prototype";
    # Patched cardano-node — source of cardano-node and cardano-cli
    # across the repo.
    cardano-node-leios.url = "github:intersectmbo/cardano-node?ref=leios-prototype";
    # tx-centrifuge only. TODO: track latest bench/leios once that
    # branch is rebased onto something with no cooldown.
    cardano-node-tx-centrifuge.url = "github:intersectmbo/cardano-node?rev=0ab6523057298eae80cb1aa1b23f4472480084be";
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
