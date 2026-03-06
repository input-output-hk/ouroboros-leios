{
  repoRoot,
  inputs,
  pkgs,
  lib,
  ...
}:

let

  inherit (repoRoot.nix) agda;

  trace-parser-src = pkgs.runCommand "trace-parser-src" { } ''
    # Copy the source for the trace verifier.
    mkdir -p $out
    cp -r ${agda.hsTraceParser.out}/hs-src/* $out/
    # Copy the test data.
    mkdir -p $out/data
    cp -r ${../leios-trace-verifier/conformance-traces}/{config.yaml,topology.yaml,valid,invalid} $out/data/
    # Add the MAlonzo modules to the cabal file.
    chmod +w $out/trace-parser.cabal
    find $out/src/MAlonzo -name "*.hs" -print\
    | sed "s#^.*/src/#        #;s#\.hs##;s#/#.#g" \
    >> $out/trace-parser.cabal
    echo $out
  '';

  ouroboros-leios-sim-src = pkgs.runCommand "ouroboros-leios-sim-src" { } ''
    # Copy the original source.
    cp -r ${../simulation} $out
    # Clean up troublesome symbolic links.
    rm -r $out/test/data
    cp -r ${../data} $out/test/
  '';

  cabalProject' = pkgs.haskell-nix.cabalProject' {
    src = ./..;
    shell.withHoogle = false;
    inputMap = {
      "https://chap.intersectmbo.org/" = inputs.iogx.inputs.CHaP;
    };
    name = "ouroboros-leios";
    compiler-nix-name = lib.mkDefault "ghc9103";
    # Add trace-parser in the cabalProjectLocal as we need the generated
    # `.cabal` file for the cabal planner to work.
    cabalProjectLocal = ''
      packages: ${trace-parser-src}
    '';
    modules = [
      {
        # We can wait and replace the `ouroboros-leios-sim` source here
        # because we do not need to change the `.cabal` file.
        packages.ouroboros-leios-sim.src = lib.mkForce ouroboros-leios-sim-src;
      }
    ];
  };

  cabalProject = cabalProject'.appendOverlays [ ];

  # Docs for mkHaskellProject: https://github.com/input-output-hk/iogx/blob/main/doc/api.md#mkhaskellproject
  project = lib.iogx.mkHaskellProject {
    inherit cabalProject;

    shellArgs = repoRoot.nix.shell;
  };

in

project
