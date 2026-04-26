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

  agdaWithDeps = agdaWithPkgs.withPackages (p: [
    p.standard-library
    p.standard-library-classes
    p.standard-library-meta
    p.abstract-set-theory
    p.agda-categories
    p.iog-prelude
    leiosSpec
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
    agdaWithDeps
    agdaTraceParser
    hsTraceParser
    ;
}
// lib.optionalAttrs (system != "aarch64-linux") {
  inherit leiosDocs enhancedLeiosDocs;
}
