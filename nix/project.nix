{
  repoRoot,
  inputs,
  pkgs,
  lib,
  ...
}:

let

  # NOTE: unlike main, the trace verifier is NOT part of this project: it
  # needs a newer cardano stack than the simulation packages and is built
  # from cabal.project.trace-verifier by its own haskell.nix instance (see
  # ./trace-verifier.nix). This project mirrors main's.
  sources = pkgs.stdenv.mkDerivation {
    name = "leios-hs-sources";
    src = ./..;
    patchPhase = ''
      # Clean up troublesome symbolic links.
      rm -r simulation/test/data
      cp -r data simulation/test/
    '';
    buildPhase = ''
      cp -r . $out
    '';
    fixupPhase = ''
      # Skip fixup phase, so as not to mangle any of the source.
    '';
  };

  cabalProject' = pkgs.haskell-nix.cabalProject' {
    src = sources.out;
    shell.withHoogle = false;
    inputMap = {
      "https://chap.intersectmbo.org/" = inputs.iogx.inputs.CHaP;
    };
    name = "ouroboros-leios";
    compiler-nix-name = lib.mkDefault "ghc9101";
  };

  cabalProject = cabalProject'.appendOverlays [ ];

  # Docs for mkHaskellProject: https://github.com/input-output-hk/iogx/blob/main/doc/api.md#mkhaskellproject
  project = lib.iogx.mkHaskellProject {
    inherit cabalProject;

    shellArgs = repoRoot.nix.shell;
  };

in

project
