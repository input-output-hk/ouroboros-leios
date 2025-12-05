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

  leiosSpec = inputs.leios-spec;

  inherit (leiosSpec.packages)
    agdaIOGPrelude
    agdaSets
    agdaStdlib
    agdaStdlibMeta
    agdaStdlibClasses
    agdaWithDeps
    ;
  agdaLeiosSpec = leiosSpec.packages.leiosSpec;

  deps = [
    agdaStdlib
    agdaStdlibMeta
    agdaStdlibClasses
    agdaSets
    agdaIOGPrelude
    agdaLeiosSpec
  ];

  agdaTraceParser = pkgs.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "trace-parser";
    name = "trace-parser"; # In principle, this should have a version number.
    src = ../leios-trace-verifier;
    meta = { };
    libraryFile = "trace-parser.agda-lib";
    everythingFile = "src/trace-parser.agda";
    buildInputs = deps;
  };
  hsTraceParser = pkgs.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "trace-parser";
    name = "trace-parser"; # In principle, this should have a version number.
    src = ../leios-trace-verifier;
    meta = { };
    libraryFile = "trace-parser.agda-lib";
    everythingFile = "src/trace-parser.agda";
    buildInputs = deps;
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
    agdaStdlib
    agdaStdlibMeta
    agdaStdlibClasses
    agdaSets
    agdaIOGPrelude
    agdaLeiosSpec
    agdaTraceParser
    hsTraceParser
    ;
  agdaWithDeps = agdaWithDeps.withPackages { pkgs = deps; };
}
