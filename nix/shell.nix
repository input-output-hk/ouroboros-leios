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
  welcomeMessage = ''
    Welcome to Ouroboros Leios!
  '';

  tools = {
  };
}
