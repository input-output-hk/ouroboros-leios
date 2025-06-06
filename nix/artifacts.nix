{ pkgs, ... }:

with pkgs;
let

  simRealism = pkgs.stdenv.mkDerivation {
    name = "sim-realism";
    src = ../simulation;
    buildInputs = [
      pkgs.texliveFull
      pkgs.gnuplot
      pkgs.python3Packages.pygments
    ];
    buildPhase = ''
      cd docs
      make
    '';
    installPhase = ''
      mkdir $out
      cp sim-realism.pdf $out/
    '';
  };

  networkSpec = pkgs.stdenv.mkDerivation {
    name = "network-spec";
    src = ../simulation/docs/network-spec;
    buildInputs = [
      pkgs.texliveFull
    ];
    installPhase = ''
      mkdir $out
      cp network-spec.pdf $out/
    '';
  };

in
{
  inherit simRealism networkSpec;
}
