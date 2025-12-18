# Docs for this file: https://github.com/input-output-hk/iogx/blob/main/doc/api.md#mkhaskellprojectinshellargs
# See `shellArgs` in `mkHaskellProject` in ./project.nix for more details.

{
  inputs,
  pkgs,
  lib,
  ...
}:

# Each flake variant defined in your project.nix project will yield a separate
# shell. If no flake variants are defined, then cabalProject is the original
# project.
_cabalProject:

let

  agda = import ./agda.nix { inherit pkgs lib inputs; };
  emacsWithPackages = pkgs.emacs.pkgs.withPackages (epkgs: [
    epkgs.agda2-mode
    pkgs.mononoki
  ]);

in

{
  name = "nix-shell";

  packages = [
    agda.agdaWithDeps
    emacsWithPackages
    pkgs.nodePackages_latest.prettier
    pkgs.gnuplot
    pkgs.texliveFull
    pkgs.python3Packages.pygments
    pkgs.entr
  ];

#  # Agda environment variables.
#  env = {
#    AGDA_STDLIB = "${agda.standard-library}/standard-library.agda-lib";
#    AGDA_STDLIB_CLASSES = "${agda.standard-library-classes}/standard-library-classes.agda-lib";
#    AGDA_STDLIB_META = "${agda.standard-library-meta}/standard-library-meta.agda-lib";
#    AGDA_SETS = "${agda.abstract-set-theory}/abstract-set-theory.agda-lib";
#    AGDA_IOG_PRELUDE = "${agda.iog-prelude}/iog-prelude.agda-lib";
#  };
#      ${agda.standard-library}/standard-library.agda-lib
#      ${agda.standard-library-classes}/standard-library-classes.agda-lib
#      ${agda.standard-library-meta}/standard-library-meta.agda-lib
#      ${agda.abstract-set-theory}/abstract-set-theory.agda-lib
#      ${agda.iog-prelude}/iog-prelude.agda-lib
#
  welcomeMessage = ''
    Welcome to Ouroboros Leios!

    Locations of Agda libraries:

    Run 'emacs' to edit .agda files.
  '';

  tools = {
  };
}
