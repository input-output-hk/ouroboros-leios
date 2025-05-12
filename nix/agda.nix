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

  traceParser = pkgs.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "trace-parser";
    name = "trace-parser";  # FIXME: Why is this entry needed?
    src = ../leios-trace-verifier;
    meta = { };
    libraryFile = "trace-parser.agda-lib";
    everythingFile = "trace-parser.agda";
    buildInputs = deps;
  };
in
{
  inherit agdaStdlib agdaStdlibMeta agdaStdlibClasses agdaSets agdaIOGPrelude agdaLeiosSpec;
  agdaWithDeps = agdaWithDeps.withPackages { pkgs = deps; };
  traceParser = traceParser;
}
