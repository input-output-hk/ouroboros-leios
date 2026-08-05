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

in

[
  (lib.optionalAttrs (system == "x86_64-linux") project.flake)
  {
    packages = agda // artifacts;
  }
  # haskell.nix's raw project.flake exposes packages/apps under compound
  # component names (e.g. "trace-parser:exe:linear-leios-trace-verifier").
  # iogx's mkHaskellProject used to flatten these; now that nix/project.nix
  # drives haskell.nix directly (see its comment), re-add short aliases for
  # the names CI, docs, and scripts already reference.
  (lib.optionalAttrs (system == "x86_64-linux") {
    packages = {
      ols = project.flake.packages."ouroboros-leios-sim:exe:ols";
      linear-leios-trace-verifier = project.flake.packages."trace-parser:exe:linear-leios-trace-verifier";
      linear-leios-trace-verifier-chain =
        project.flake.packages."trace-parser:exe:linear-leios-trace-verifier-chain";
      test-trace-verifier = project.flake.packages."trace-parser:test:test-trace-verifier";
      leios-trace-processor = project.flake.packages."trace-processor:exe:leios-trace-processor";
    };
    apps = {
      ols = project.flake.apps."ouroboros-leios-sim:exe:ols";
      linear-leios-trace-verifier = project.flake.apps."trace-parser:exe:linear-leios-trace-verifier";
      linear-leios-trace-verifier-chain =
        project.flake.apps."trace-parser:exe:linear-leios-trace-verifier-chain";
      test-trace-verifier = project.flake.apps."trace-parser:test:test-trace-verifier";
      leios-trace-processor = project.flake.apps."trace-processor:exe:leios-trace-processor";
    };
  })
]
