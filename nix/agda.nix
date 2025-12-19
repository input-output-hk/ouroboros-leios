{
  pkgs,
  inputs,
  ...
}:

with pkgs;
let

  locales = {
    LANG = "en_US.UTF-8";
    LC_ALL = "en_US.UTF-8";
    LOCALE_ARCHIVE =
      if pkgs.system == "x86_64-linux" then "${pkgs.glibcLocales}/lib/locale/locale-archive" else "";
  };

  inherit (inputs.leios-spec.packages)
    agdaWithPkgs
    leiosSpec
    ;

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

  standard-library = agdaWithPkgs.withPackages (p: [ p.standard-library ]);
  standard-library-classes = agdaWithPkgs.withPackages (p: [ p.standard-library-classes ]);
  standard-library-meta = agdaWithPkgs.withPackages (p: [ p.standard-library-meta ]);
  abstract-set-theory = agdaWithPkgs.withPackages (p: [ p.abstract-set-theory ]);
  agda-categories = agdaWithPkgs.withPackages (p: [ p.agda-categories ]);
  iog-prelude = agdaWithPkgs.withPackages (p: [ p.iog-prelude ]);
}
