{
  pkgs,
  inputs,
  system,
  lib,
  ...
}:

let

  locales = {
    LANG = "en_US.UTF-8";
    LC_ALL = "en_US.UTF-8";
    LOCALE_ARCHIVE =
      if system == "x86_64-linux" then "${pkgs.glibcLocales}/lib/locale/locale-archive" else "";
  };

  inherit (inputs.leios-spec.packages.${system})
    agdaWithPkgs
    leiosSpec
    leiosDocs
    ;

  agda-web-docs-lib = import ./agda-web-docs-lib.nix { inherit pkgs lib; };

  enhancedLeiosDocs = pkgs.stdenv.mkDerivation {
    name = "enhanced-leios-docs";
    src = leiosDocs;
    nativeBuildInputs = [ agda-web-docs-lib ];

    configFile = pkgs.writeText "agda-docs.config.json" (
      builtins.toJSON {
        backButtonUrl = "/formal-spec/";
        modules = [
          "Leios"
          "Cardano"
          "Network"
          "Ouroboros"
        ];
        githubUrl = "https://github.com/input-output-hk/ouroboros-leios-formal-spec";
      }
    );

    buildPhase = ''
      mkdir -p build
      cp -r html/* build/
      chmod -R u+w build/

      agda-docs process -i build -c $configFile
    '';

    installPhase = ''
      mkdir -p $out
      cp -r build/* $out/
    '';
  };

  # The Praos formal spec as an Agda library, built with the same toolchain
  # as the Leios spec (mirrors ouroboros-leios-formal-spec's own praosSpec
  # derivation, since this repo doesn't carry the Praos wrapper's build). agda
  # --build-library checks every module in the library, so the parts
  # leios-trace-verifier doesn't consume (yet) are dropped: the empty
  # Everything (module name clashes with iog-prelude's), the Examples
  # (unsolved holes), Protocol.TraceVerifier (sole user of the
  # agda-irrelevance dependency) and the Properties theorems (to be
  # re-included for the safety/liveness transfer work).
  praosSpec = pkgs.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "praos-spec";
    version = "0.1";
    src = inputs.praos-spec-src;
    meta = { };
    libraryFile = "praos-spec.agda-lib";
    everythingFile = "src/EverythingLeios.agda";
    postPatch = ''
      sed -i '/agda-irrelevance/d' praos-spec.agda-lib
      rm -r src/Everything.agda src/Examples \
            src/Protocol/TraceVerifier.agda src/Protocol/TraceVerifier \
            src/Properties
      {
        echo "module EverythingLeios where"
        echo "import Protocol.Semantics"
        echo "import Protocol.Assumptions"
      } > src/EverythingLeios.agda
    '';
    buildInputs = [
      (agdaWithPkgs.withPackages (p: [
        p.standard-library
        p.standard-library-classes
        p.standard-library-meta
        p.iog-prelude
      ]))
    ];
    # Without an explicit buildPhase, agdaPackages.mkDerivation's default
    # build+cleanup hooks assume plain nixpkgs' own Agda version, which
    # doesn't match the toolchain supplied via buildInputs (leios-spec's
    # agda-nix pin) — it fails removing a stale .agdai under the wrong
    # _build/<version> path. agdaTraceParser/hsTraceParser below sidestep the
    # same mismatch by overriding buildPhase too.
    buildPhase = ''
      agda src/EverythingLeios.agda
    '';
  };

  agdaWithDeps = agdaWithPkgs.withPackages (p: [
    p.standard-library
    p.standard-library-classes
    p.standard-library-meta
    p.abstract-set-theory
    p.agda-categories
    p.iog-prelude
    p.categorical-crypto
    leiosSpec
    praosSpec
  ]);

  agdaTraceParser = pkgs.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "trace-parser";
    name = "trace-parser"; # In principle, this should have a version number.
    src = ../leios-trace-verifier;
    meta = { };
    libraryFile = "trace-parser.agda-lib";
    everythingFile = "src/trace-parser.agda";
    buildInputs = [ agdaWithDeps ];
    buildPhase = ''
      agda src/trace-parser.agda
    '';
  };

  hsTraceParser = pkgs.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "trace-parser-hs";
    name = "trace-parser-hs"; # In principle, this should have a version number.
    src = ../leios-trace-verifier;
    meta = { };
    libraryFile = "trace-parser.agda-lib";
    everythingFile = "src/trace-parser.agda";
    buildInputs = [ agdaWithDeps ];
    buildPhase = ''
      agda --transliterate src/trace-parser.agda -c --ghc-dont-call-ghc --compile-dir hs-src/src
    '';
    installPhase = ''
      mkdir -p $out
      cp -r hs-src $out
    '';
  };
in
{
  inherit
    leiosSpec
    praosSpec
    agdaWithDeps
    agdaTraceParser
    hsTraceParser
    ;
}
// lib.optionalAttrs (system != "aarch64-linux") {
  inherit leiosDocs enhancedLeiosDocs;
}
