#!/usr/bin/env bash

mkdir -p results

for f in rbgen ebgen ibgen cpus receipts
do
  DIR=$(find runs -type f -name $f.csv.gz -printf %h\\n -quit)
  HL=$(sed -n -e '1p' "$DIR/case.csv")
  HR=$(zcat "$DIR/$f.csv.gz" | sed -n -e '1p')
  echo "$HL,$HR" > results/$f.csv
  for g in $(find runs -type f -name $f.csv.gz -printf %h\\n)
  do
  BL=$(sed -n -e '2p' "$g/case.csv")
    zcat "$g/$f.csv.gz" | sed -e "1d;s/^/$BL,/" >> results/$f.csv
  done
  gzip -9 results/$f.csv
done
