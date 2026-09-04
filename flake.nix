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

    leios-spec.url = "github:input-output-hk/ouroboros-leios-formal-spec?rev=73d61e931ebd93ea58dacf2ad3e2562dbbdc0fbe";

    # Trace verifier only: it links cardano-api against the Leios prototype
    # node's pins (cabal.project.trace-verifier), which need newer
    # CHaP/hackage snapshots than iogx's. A dedicated haskell.nix instance
    # keeps the rest of this flake identical to main. Snapshots must be
    # at/after cabal.project.trace-verifier's index-states
    # (hackage 2026-07-15T21:58:35Z / CHaP 2026-07-27T20:44:57Z, the
    # prototype-2026w32 node's pins).
    haskell-nix-tv = {
      url = "github:input-output-hk/haskell.nix/ef52c36b9835c77a255befe2a20075ba71e3bfab";
      inputs.hackage.url = "github:input-output-hk/hackage.nix/956836e90e902e23b7bf080a0c9d0a88ddf0273a";
    };
    CHaP-tv = {
      url = "github:intersectmbo/cardano-haskell-packages/60ad9c29de7b30cb480547110cffad0cb6c71ab2";
      flake = false;
    };

    flake-parts.url = "github:hercules-ci/flake-parts";

    pre-commit-hooks.url = "github:cachix/git-hooks.nix";

    # Used by analysis/deltaq/
    jupyenv.url = "github:tweag/jupyenv";
    # NOTE: Also pinned in cabal.project (source-repository-package) for the
    # Haskell build. Keep both pins in sync.
    deltaq-src.url = "github:DeltaQ-SD/deltaq";
    deltaq-src.flake = false;

    # Used by demo/
    # Uses git+https (not github:) because the leios-prototype branch pulls in a
    # git submodule; the tarball-based github fetcher rejects `submodules=1`.
    ouroboros-consensus.url = "git+https://github.com/intersectmbo/ouroboros-consensus?ref=leios-prototype&submodules=1";
    # Patched cardano-node — source of cardano-node, cardano-cli, and
    # tx-firehose across the repo. The tx-firehose bench/ package now
    # lives on top of leios-prototype so a single input suffices.
    cardano-node-leios.url = "github:intersectmbo/cardano-node?ref=jl/leios-prototype-w35-patched";
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
        # Release artifacts (release tarball + docker image) live in
        # nix/release.nix rather than a build.nix so the auto-discovery
        # above doesn't pick them up automatically — we want this module
        # named for its purpose, not the convention.
        ./nix/release.nix
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
