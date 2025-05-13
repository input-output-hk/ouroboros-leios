{ pkgs, ... }:

with pkgs;
let

  simRealism = pkgs.stdenv.mkDerivation {
    name = "sim-realism";
    src = ../simulation/docs;
    buildInputs = [
      pkgs.texliveFull
      pkgs.gnuplot
      pkgs.python3Packages.pygments
      pkgs.cabal-install
    ];
    installPhase = ''
      mkdir $out
      cp sim-realism.pdf $out/
    '';
  };

in
{
  inherit networkSpec;
}
