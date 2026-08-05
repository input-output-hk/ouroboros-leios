{
  repoRoot,
  pkgs,
  lib,
  system,
  ...
}:

let

  inherit (repoRoot.nix) project agda;
  artifacts = import ./artifacts.nix { inherit pkgs; };

  # haskell.nix's raw project.flake exposes packages/apps under compound
  # component names (e.g. "trace-parser:exe:linear-leios-trace-verifier").
  # iogx's mkHaskellProject used to flatten these; now that nix/project.nix
  # drives haskell.nix directly (see its comment), re-add short aliases for
  # the names CI, docs, and scripts already reference. Aliases whose package
  # is absent from the current cabal.project are skipped: the w31-aligned
  # cabal.project trims the project to the trace-verifier's needs (the
  # simulation et al. still pin the older cardano stack), so e.g. `ols` is
  # not built from this flake at the moment.
  aliasNames = {
    ols = "ouroboros-leios-sim:exe:ols";
    linear-leios-trace-verifier = "trace-parser:exe:linear-leios-trace-verifier";
    linear-leios-trace-verifier-chain = "trace-parser:exe:linear-leios-trace-verifier-chain";
    test-trace-verifier = "trace-parser:test:test-trace-verifier";
    leios-trace-processor = "trace-processor:exe:leios-trace-processor";
  };

  presentAliases =
    set: lib.filterAttrs (_: v: v != null) (lib.mapAttrs (_: name: set.${name} or null) aliasNames);

in

[
  (lib.optionalAttrs (system == "x86_64-linux") project.flake)
  {
    packages = agda // artifacts;
  }
  (lib.optionalAttrs (system == "x86_64-linux") {
    packages = presentAliases project.flake.packages;
    apps = presentAliases project.flake.apps;
  })
]
