#!/usr/bin/env nix-shell
#!nix-shell -i bash -p imagemagick poppler

set -e

for d in plots/stracciatella/*.png
do
  FILE=$(basename $d)
  if [[ -f "plots/notxs/$FILE" ]]
  then
    magick montage plots/{txrefs,stracciatella,linear,notxs}/$FILE -tile 2x2 -geometry +0+0 plots/$FILE
  else
    magick montage plots/{txrefs,stracciatella,linear}/$FILE -tile 2x2 -geometry +0+0 plots/$FILE
  fi
done

magick plots/{sizes,spatial-efficiency,reach-eb-tx,reach-rb-tx,temporal-efficiency-bar,elapsed-EB,elapsed-RB,elapsed-TX,elapsed-VT,ingress-average-area,ingress-peak-point,cpu-peak-histogram,cpu-mean-histogram}.png content.pdf

pdfunite front-matter.pdf content.pdf plots.pdf
