{
  repoRoot,
  inputs,
  pkgs,
  lib,
  ...
}:

let

  inherit (repoRoot.nix) agda;

  # The trace verifier links cardano-api against the Leios prototype node's
  # pins (cabal.project.trace-verifier), which need newer CHaP/hackage
  # snapshots than main's iogx pins provide. To keep the rest of the flake
  # identical to main, the verifier is built by its OWN haskell.nix instance
  # (flake inputs haskell-nix-tv / CHaP-tv) rather than iogx's.
  # iogx's nixpkgs plus iohk-nix's crypto overlays, mirroring iogx's own
  # overlay stack (iogx src/mkFlake.nix): haskell-nix-crypto registers the
  # libblst/libsodium-vrf/libsecp256k1 pkg-config mappings that the cabal
  # solver needs for cardano-crypto-class, and it must come after both the
  # crypto and haskell.nix overlays.
  iogxInputs = inputs.iogx.inputs;
  pkgsTv = import iogxInputs.nixpkgs {
    inherit (pkgs.stdenv.hostPlatform) system;
    config = inputs.haskell-nix-tv.config or { };
    overlays = [
      iogxInputs.iohk-nix.overlays.crypto
      inputs.haskell-nix-tv.overlay
      iogxInputs.iohk-nix.overlays.haskell-nix-crypto
    ];
  };

  # Tools for the trace-verifier development shell.
  emacsWithPackages = pkgs.emacs.pkgs.withPackages (epkgs: [
    epkgs.agda2-mode
    pkgs.mononoki
  ]);

  sources = pkgs.stdenv.mkDerivation {
    name = "leios-trace-verifier-sources";
    src = ./..;
    patchPhase = ''
      # Add the trace verifier package. It's deliberately not listed in the
      # checked-in cabal.project.trace-verifier: the generated
      # leios-trace-verifier/dist/haskell doesn't exist in a plain checkout.
      sed -i '/^packages:/a\ \ leios-trace-verifier/dist/haskell' cabal.project.trace-verifier
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

  cabalProject' = pkgsTv.haskell-nix.cabalProject' {
    src = sources.out;
    # The default cabal.project is the plain-cabal simulation project; the
    # verifier's cardano-stack project lives in its own file.
    cabalProjectFileName = "cabal.project.trace-verifier";
    inputMap = {
      "https://chap.intersectmbo.org/" = inputs.CHaP-tv;
    };
    name = "leios-trace-verifier";
    compiler-nix-name = lib.mkDefault "ghc9101";
    modules = [
      {
        # cardano-rpc (a subdir of the cardano-api pin) depends on
        # proto-lens-protobuf-types, whose Setup.hs runs protoc at build time.
        packages.proto-lens-protobuf-types.components.library.build-tools = [
          pkgsTv.buildPackages.protobuf
        ];
      }
    ];
    shell = {
      withHoogle = false;
      tools = {
        cabal = "latest";
      };
      nativeBuildInputs = [
        agda.agdaWithDeps
        emacsWithPackages
        pkgs.nodePackages_latest.prettier
        pkgs.gnuplot
        pkgs.entr
      ];
      shellHook = ''
        echo "Ouroboros Leios trace-verifier shell (cabal.project.trace-verifier)"
      '';
    };
  };

  cabalProject = cabalProject'.appendOverlays [ ];

  tvFlake = cabalProject.flake';

in

{
  inherit cabalProject;

  # Flat names used by scripts (e.g. run.sh), plus the raw cabal-component
  # names (trace-parser:exe:...) from the project flake.
  packages = tvFlake.packages // {
    linear-leios-trace-verifier = tvFlake.packages."trace-parser:exe:linear-leios-trace-verifier";
    linear-leios-trace-verifier-chain =
      tvFlake.packages."trace-parser:exe:linear-leios-trace-verifier-chain";
    test-trace-verifier = tvFlake.packages."trace-parser:test:test-trace-verifier";
  };

  devShell = cabalProject.shell;
}
