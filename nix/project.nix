{
  repoRoot,
  inputs,
  pkgs,
  lib,
  ...
}:

let

  agda = import ./agda.nix { inherit pkgs lib inputs; };

  sources = pkgs.stdenv.mkDerivation {
    name = "leios-hs-sources";
    src = ./..;
    patchPhase = ''
      # Add the trace verifier package.
      sed -i '/^packages:/a\ \ leios-trace-verifier/dist/haskell' cabal.project
      # Clean up troublesome symbolic links.
      rm -r simulation/test/data
      cp -r data simulation/test/
    '';
    buildPhase = ''
      # Copy the source for the trace verifier.
      mkdir -p $out/leios-trace-verifier/dist/haskell
      cp -r ${agda.hsTraceParser.out}/hs-src/* $out/leios-trace-verifier/dist/haskell/
      # Copy the original source.
      cp -r . $out
      # Copy the test data.
      mkdir -p $out/leios-trace-verifier/dist/haskell/data
      cp -r leios-trace-verifier/conformance-traces/{config.yaml,topology.yaml,valid,invalid} $out/leios-trace-verifier/dist/haskell/data/
    '';
    installPhase = ''
      # Add the MAlonzo modules to the cabal file.
      chmod +w $out/leios-trace-verifier/dist/haskell/trace-parser.cabal
      find $out/leios-trace-verifier/dist/haskell/src/MAlonzo -name "*.hs" -print\
      | sed "s#^.*/src/#        #;s#\.hs##;s#/#.#g" \
      >> $out/leios-trace-verifier/dist/haskell/trace-parser.cabal
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
