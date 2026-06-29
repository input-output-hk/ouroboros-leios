{
  repoRoot,
  inputs,
  pkgs,
  lib,
  ...
}:

let

  inherit (repoRoot.nix) agda;

  # Tools for the development shell (previously provided via iogx's shellArgs in
  # ./shell.nix). They are attached to the haskell.nix project shell below.
  emacsWithPackages = pkgs.emacs.pkgs.withPackages (epkgs: [
    epkgs.agda2-mode
    pkgs.mononoki
  ]);

  sources = pkgs.stdenv.mkDerivation {
    name = "leios-hs-sources";
    src = ./..;
    patchPhase = ''
      # The trace verifier package (leios-trace-verifier/dist/haskell) is now
      # listed directly in cabal.project, so no patching is needed here.
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
    inputMap = {
      "https://chap.intersectmbo.org/" = inputs.iogx.inputs.CHaP;
    };
    name = "ouroboros-leios";
    compiler-nix-name = lib.mkDefault "ghc9101";
    # Development shell. Replaces iogx's mkHaskellProject + shellArgs: the modern
    # haskell.nix flake API ('flake'' / devShells) is incompatible with the iogx
    # version pinned here (it calls haskell.nix's mkFlake with the obsolete
    # 'devShell' argument), so we drive haskell.nix directly.
    shell = {
      withHoogle = false;
      # haskell.nix builds cabal-install against the project's GHC (iogx used to
      # provide this; the bypassed mkHaskellProject did too).
      tools = {
        cabal = "latest";
      };
      nativeBuildInputs = [
        agda.agdaWithDeps
        emacsWithPackages
        pkgs.nodePackages_latest.prettier
        pkgs.gnuplot
        pkgs.texliveFull
        pkgs.python3Packages.pygments
        pkgs.entr
      ];
      shellHook = ''
        echo "Welcome to Ouroboros Leios!"
      '';
    };
  };

  cabalProject = cabalProject'.appendOverlays [ ];

  project = {
    flake = cabalProject.flake';
  };

in

project
