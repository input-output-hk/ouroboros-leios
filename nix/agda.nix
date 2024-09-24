{ pkgs, lib, inputs, ... }:

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
    src = pkgs.fetchFromGitHub {
      repo = "agda-stdlib-classes";
      owner = "omelkonian";
      rev = "v2.0";
      sha256 = "sha256-PcieRRnctjCzFCi+gUYAgyIAicMOAZPl8Sw35fZdt0E=";
    };
    meta = { };
    libraryFile = "agda-stdlib-classes.agda-lib";
    everythingFile = "Classes.agda";
    buildInputs = [ agdaStdlib ];
  };

  agdaStdlibMeta = customAgda.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-stdlib-meta";
    version = "2.0";
    src = pkgs.fetchFromGitHub {
      repo = "stdlib-meta";
      owner = "input-output-hk";
      rev = "4fc4b1ed6e47d180516917d04be87cbacbf7d314";
      sha256 = "T+9vwccbDO1IGBcGLjgV/fOt+IN14KEV9ct/J6nQCsM=";
    };
    meta = { };
    libraryFile = "agda-stdlib-meta.agda-lib";
    everythingFile = "Main.agda";
    buildInputs = [ agdaStdlib agdaStdlibClasses ];
  };

  formalLedger = customAgda.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "formal-ledger";
    version = "1d77a35a";
    src = pkgs.fetchFromGitHub {
      repo = "formal-ledger-specifications";
      owner = "IntersectMBO";
      rev = "1d77a35ab1820c123790e5138d85325d33787e86";
      sha256 = "0d15aysxdmn31aj982gr63d40q606dqvq0k4y4rwa9kpmjgadjaq";
    };
    meta = { };
    preConfigure = ''
      cat << EOI > formal-ledger.agda-lib
      name: formal-ledger
      depend:
        standard-library
        standard-library-classes
        standard-library-meta
      include: src
      EOI
      mv src/Everything.agda .
    '';
    libraryFile = "formal-ledger.agda-lib";
    everythingFile = "Everything.agda";
    buildInputs = [ agdaStdlib agdaStdlibClasses agdaStdlibMeta ];
  };

  leiosSpec = customAgda.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "leios-spec";
    name = "leios-spec";  # FIXME: Why is this entry needed?
    src = ../formal-spec;
    meta = { };
    preConfigure = ''
      cat << EOI > Everything.agda
      module Everything where
        import CategoricalCrypto
        import Leios.Network
        import Leios.SimpleSpec
      EOI
      ls
    '';
    libraryFile = "formal-spec/leios-spec.agda-lib";
    everythingFile = "Everything.agda";
    buildInputs = [ agdaStdlib agdaStdlibClasses agdaStdlibMeta formalLedger ];
  };

  agdaWithPkgs = p: customAgda.agda.withPackages { pkgs = p; ghc = pkgs.ghc; };

in
{
  inherit agdaStdlib agdaStdlibClasses agdaStdlibMeta formalLedger ;
  agdaWithDeps = agdaWithPkgs [
    agdaStdlib
    agdaStdlibClasses
    agdaStdlibMeta
    formalLedger
  ];
  leiosSpec = leiosSpec;
}
