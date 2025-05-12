{ pkgs, lib, inputs, ... }:

with pkgs;
let

  locales = {
    LANG = "en_US.UTF-8";
    LC_ALL = "en_US.UTF-8";
    LOCALE_ARCHIVE = if pkgs.system == "x86_64-linux"
                     then "${pkgs.glibcLocales}/lib/locale/locale-archive"
                     else "";
  };

  leiosSpec = inputs.leios-spec;

  agdaIOGPrelude = leiosSpec.packages.agdaIOGPrelude;
  agdaSets = leiosSpec.packages.agdaSets;
  agdaStdlib = leiosSpec.packages.agdaStdlib;
  agdaStdlibMeta = leiosSpec.packages.agdaStdlibMeta;
  agdaStdlibClasses = leiosSpec.packages.agdaStdlibClasses;
  agdaLeiosSpec = leiosSpec.packages.leiosSpec;
  agdaWithDeps = leiosSpec.packages.agdaWithDeps;

  deps = [ agdaStdlib agdaStdlibMeta agdaStdlibClasses agdaSets agdaIOGPrelude agdaLeiosSpec ];

  agdaTraceParser = pkgs.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "trace-parser";
    name = "trace-parser"; # In principle, this should have a version number.
    src = ../leios-trace-verifier;
    meta = { };
    libraryFile = "trace-parser.agda-lib";
    everythingFile = "trace-parser.agda";
    buildInputs = deps;
  };
  hsTraceParser = pkgs.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "trace-parser";
    name = "trace-parser"; # In principle, this should have a version number.
    src = ../leios-trace-verifier;
    meta = { };
    libraryFile = "trace-parser.agda-lib";
    everythingFile = "trace-parser.agda";
    buildInputs = deps;
    buildPhase = ''
      agda --transliterate trace-parser.agda -c --ghc-dont-call-ghc --compile-dir hs-src/src
    '';
    installPhase = ''
      mkdir -p $out
      cp -r hs-src $out
    '';
  };
in
{
  inherit agdaStdlib agdaStdlibMeta agdaStdlibClasses agdaSets agdaIOGPrelude agdaLeiosSpec agdaTraceParser hsTraceParser;
  agdaWithDeps = agdaWithDeps.withPackages { pkgs = deps; };
}
