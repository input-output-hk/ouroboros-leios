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

  leiosDesignPdf = pkgs.stdenv.mkDerivation {
    name = "leios-design-pdf";
    src = ../docs/leios-design;
    buildInputs = [
      pkgs.pandoc
      pkgs.texliveFull
      pkgs.librsvg
      pkgs.typst
    ];
    buildPhase = ''
      # Work directly in the source directory where all assets are available
      cd $src
      mkdir -p $out

      # Convert markdown to PDF using pandoc with XeLaTeX
      pandoc README.md \
        --pdf-engine=xelatex \
        --from=markdown \
        --to=pdf \
        --output=$out/leios-design.pdf \
        --table-of-contents \
        --number-sections \
        --highlight-style=tango \
        --variable fontsize=11pt \
        --variable documentclass=article \
        --variable geometry:margin=2.5cm \
        --variable colorlinks=true \
        --variable linkcolor=blue \
        --variable urlcolor=blue \
        --variable toccolor=black
    '';
  };

in
{
  inherit simRealism networkSpec leiosDesignPdf;
}
