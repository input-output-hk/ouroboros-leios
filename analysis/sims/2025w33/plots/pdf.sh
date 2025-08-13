#!/usr/bin/env nix-shell
#!nix-shell -I nixpkgs=https://github.com/NixOS/nixpkgs/archive/nixos-25.05.tar.gz
#!nix-shell -i bash -p imagemagick poppler-utils

magick -verbose \
  temporal-efficiency-bar.png \
  reach-eb-tx.png \
  reach-rb-tx.png \
  spatial-efficiency.png \
  sizes.png \
  references-tx.png \
  network.png \
  cpu-peak.png \
  cpu-mean.png \
  elapsed-EB.png \
  elapsed-RB.png \
  elapsed-TX.png \
  elapsed-VT.png \
  ingress-total-area.png \
  ingress-average-area.png \
  ingress-peak-point.png \
  cpu-peak-histogram.png \
  cpu-peak-timeseries.png \
  cpu-mean-histogram.png \
  cpu-mean-timeseries.png \
  contents-ebs-txs.png \
  contents-ebs-size.png \
  contents-rbs-txs.png \
  contents-rbs-size.png \
  disposition-txs-timeseries.png \
  disposition-txs-histogram.png \
  disposition-size-timeseries.png \
  disposition-size-histogram.png \
  -density 240 \
  -units PixelsPerInch \
  -gravity center \
  plots.pdf

pdfunite front.pdf plots.pdf ../ReadMe.pdf
