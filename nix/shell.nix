# Docs for this file: https://github.com/input-output-hk/iogx/blob/main/doc/api.md#mkhaskellprojectinshellargs
# See `shellArgs` in `mkHaskellProject` in ./project.nix for more details.

{ repoRoot, inputs, pkgs, lib, system }:

# Each flake variant defined in your project.nix project will yield a separate
# shell. If no flake variants are defined, then cabalProject is the original 
# project.
cabalProject:

let

  agda = import ./agda.nix {inherit pkgs lib inputs;};
  emacsWithPackages = pkgs.emacs.pkgs.withPackages (epkgs: [ epkgs.agda2-mode pkgs.mononoki ]);

in 

{
  name = "nix-shell";

  packages = [
    agda.agdaWithDeps
    emacsWithPackages
  ];

  # Agda environment variables.
  env.AGDA_STDLIB = "${agda.agdaStdlib}/standard-library.agda-lib";
  env.AGDA_STDLIB_CLASSES = "${agda.agdaStdlibClasses}/standard-library-classes.agda-lib";
  env.AGDA_STDLIB_META = "${agda.agdaStdlibMeta}/standard-library-meta.agda-lib";
  env.FORMAL_LEDGER_LIB = "${agda.formalLedger}/formal-ledger.agda-lib";

# prompt = "[ouroboros-leios]$ ";

  welcomeMessage = ''
  Welcome to Ouroboros Leios!

  Locations of Agda libraries:
    ${agda.agdaStdlib}/standard-library.agda-lib
    ${agda.agdaStdlibClasses}/standard-library-classes.agda-lib
    ${agda.agdaStdlibMeta}/standard-library-meta.agda-lib
    ${agda.formalLedger}/formal-ledger.agda-lib

  Run 'emacs' to edit .agda files.
  '';

  # shellHook = "";

  tools = {
    # haskellCompilerVersion = cabalProject.args.compiler-nix-name;
    # cabal-fmt = null;
    # cabal-install = null;
    # haskell-language-server = null;
    # haskell-language-server-wrapper = null;
    # fourmolu = null;
    # hlint = null;
    # stylish-haskell = null;
    # ghcid = null;
    # shellcheck = null;
    # prettier = null;
    # editorconfig-checker = null;
    # nixpkgs-fmt = null;
    # optipng = null;
    # purs-tidy = null;
  };

  # scripts = {
  #   foo = {
  #      description = "";
  #      group = "general";
  #      enabled = true;
  #      exec = ''
  #        echo "Hello, World!"
  #      '';
  #    };
  # };

  # preCommit = {
  #   cabal-fmt.enable = false;
  #   cabal-fmt.extraOptions = "";
  #   stylish-haskell.enable = false;
  #   stylish-haskell.extraOptions = "";
  #   fourmolu.enable = false;
  #   fourmolu.extraOptions = "";
  #   hlint.enable = false;
  #   hlint.extraOptions = "";
  #   shellcheck.enable = false;
  #   shellcheck.extraOptions = "";
  #   prettier.enable = false;
  #   prettier.extraOptions = "";
  #   editorconfig-checker.enable = false;
  #   editorconfig-checker.extraOptions = "";
  #   nixpkgs-fmt.enable = false;
  #   nixpkgs-fmt.extraOptions = "";
  #   optipng.enable = false;
  #   optipng.extraOptions = "";
  #   purs-tidy.enable = false;
  #   purs-tidy.extraOptions = "";
  # };

}
 
