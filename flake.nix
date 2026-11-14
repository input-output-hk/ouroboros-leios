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

    leios-spec.url = "github:input-output-hk/ouroboros-leios-formal-spec?rev=426f3756655d8b6b562d49b33243f796c5ab39b3";

    # The Praos formal spec, used by leios-trace-verifier's Leios.Base.Praos
    # to wrap the real Praos node as a Leios BaseMachine (see
    # leios-trace-verifier/docs/praos-base-machine-sketch.md).
    praos-spec-src = {
      url = "github:input-output-hk/ouroboros-praos-formal-spec/847697eec805983c6ac2afa793443e4da954d11a";
      flake = false;
    };

    # Trace verifier only: it links cardano-api against the Leios prototype
    # node's pins (cabal.project.trace-verifier), which need newer
    # CHaP/hackage snapshots than iogx's. A dedicated haskell.nix instance
    # keeps the rest of this flake identical to main. Snapshots must be
    # at/after cabal.project.trace-verifier's index-states
    # (hackage 2026-09-02T14:05:07Z / CHaP 2026-10-09T14:30:01Z, the
    # cardano-node 11.2.0.164 release pins).
    haskell-nix-tv = {
      url = "github:input-output-hk/haskell.nix/ef52c36b9835c77a255befe2a20075ba71e3bfab";
      inputs.hackage.url = "github:input-output-hk/hackage.nix/309393e86ccda97e642ff30dfb0c0aee16d0b94b";
    };
    CHaP-tv = {
      url = "github:intersectmbo/cardano-haskell-packages/0f444414db3931fb70d8667f4791dec49e1e23bf";
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
    cardano-node-leios.url = "github:intersectmbo/cardano-node?ref=leios-prototype";
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
        "aarch64-linux"
        "aarch64-darwin"
      ];

      flake.hydraJobs = import ./nix/hydra.nix {
        flake = self;
        inherit lib;
        systems = [
          "x86_64-linux"
          "aarch64-linux"
          "aarch64-darwin"
        ];
      };

    };

}
