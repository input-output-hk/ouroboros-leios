#!/usr/bin/env nix-shell
#!nix-shell -I nixpkgs=https://github.com/NixOS/nixpkgs/archive/nixos-25.05.tar.gz
#!nix-shell -i bash -p imagemagick poppler-utils

magick -verbose \
  sizes.png \
  spatial-efficiency.png \
  reach-eb-tx.png \
  reach-rb-tx.png \
  references-tx.png \
  temporal-efficiency-bar.png \
  network.png \
  cpu-peak.png \
  cpu-mean.png \
  elapsed-EB.png \
  elapsed-RB.png \
  elapsed-TX.png \
  elapsed-VT.png \
  ingress-average-area.png \
  ingress-peak-point.png \
  cpu-peak-histogram.png \
  cpu-mean-histogram.png \
  contents-ebs-size.png \
  contents-rbs-size.png \
  disposition-size-histogram.png \
  -density 240 \
  -units PixelsPerInch \
  -gravity center \
  ../ReadMe.pdf
