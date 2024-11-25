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

  customAgda = inputs.agda-nixpkgs.legacyPackages;

  agdaStdlib = customAgda.agdaPackages.standard-library;

  agdaStdlibClasses = customAgda.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-stdlib-classes";
    version = "2.0";
    src = fetchFromGitHub {
      repo = "agda-stdlib-classes";
      owner = "omelkonian";
      rev = "2b42a6043296b4601134b8ab9371b37bda5d4424";
      sha256 = "sha256-kTqS9p+jjv34d4JIWV9eWAI8cw9frX/K9DHuwv56AHo=";
    };
    meta = { };
    libraryFile = "agda-stdlib-classes.agda-lib";
    everythingFile = "standard-library-classes.agda";
    buildInputs = [ agdaStdlib ];
  };

  agdaStdlibMeta = customAgda.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-stdlib-meta";
    version = "2.1.1";
    src = fetchFromGitHub {
      repo = "stdlib-meta";
      owner = "omelkonian";
      rev = "v2.1.1";
      sha256 = "qOoThYMG0dzjKvwmzzVZmGcerfb++MApbaGRzLEq3/4=";
    };
    meta = { };
    libraryFile = "agda-stdlib-meta.agda-lib";
    everythingFile = "Main.agda";
    buildInputs = [ agdaStdlib agdaStdlibClasses ];
  };

  agdaSets = customAgda.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-sets";
    version = "2.1.1";
    src = pkgs.fetchFromGitHub {
      repo = "agda-sets";
      owner = "input-output-hk";
      rev = "f517d0d0c1ff1fd6dbac8b34309dea0e1aea6fc6";
      sha256 = "sha256-OsdDNNJp9NWDgDM0pDOGv98Z+vAS1U8mORWF7/B1D7k=";
    };
    meta = { };
    libraryFile = "abstract-set-theory.agda-lib";
    everythingFile = "src/abstract-set-theory.agda";
    buildInputs = [ agdaStdlib agdaStdlibClasses agdaStdlibMeta ];
  };

  agdaIOGPrelude = customAgda.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-prelude";
    version = "2.0";
    src = pkgs.fetchFromGitHub {
      repo = "iog-agda-prelude";
      owner = "input-output-hk";
      rev = "ee289f9a0b2ec0a3bfc43c3f678a17c174b397e6";
      sha256 = "sha256-noLUBl9d/vDNbAzWfnBrWoATlBrVG1DwzRV7/2uRHoE=";
    };
    meta = { };
    libraryFile = "iog-prelude.agda-lib";
    everythingFile = "src/Everything.agda";
    buildInputs = [ agdaStdlib agdaStdlibClasses ];
  };

  deps = [ agdaStdlib agdaStdlibClasses agdaStdlibMeta agdaSets agdaIOGPrelude ];

  leiosSpec = customAgda.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "leios-spec";
    name = "leios-spec";  # FIXME: Why is this entry needed?
    src = ../formal-spec;
    meta = { };
    libraryFile = "formal-spec/leios-spec.agda-lib";
    everythingFile = "Everything.agda";
    buildInputs = deps;
  };

  agdaWithPkgs = p: customAgda.agda.withPackages { pkgs = p; ghc = pkgs.ghc; };

in
{
  inherit agdaStdlib agdaStdlibClasses agdaStdlibMeta agdaSets agdaIOGPrelude ;
  agdaWithDeps = agdaWithPkgs deps;
  leiosSpec = leiosSpec;
}
