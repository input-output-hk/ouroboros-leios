#!/usr/bin/env nix-shell
#!nix-shell -i bash -p gzip

set -e

mkdir -p results

for f in rbgen ebgen ibgen cpus receipts
do
  echo "----- $f -----"
  DIR=$(find runs -type f -name $f.csv.gz -printf %h\\n -quit)
  HL=$(sed -n -e '1p' "$DIR/case.csv")
  HR=$(zcat "$DIR/$f.csv.gz" | sed -n -e '1p')
  echo "$HL,$HR" > results/$f.csv
  for g in $(find runs -type f -name $f.csv.gz -printf %h\\n)
  do
    if [ ! -e "$g/stderr" ]
    then
      echo "Skipping $g because it has no stderr."
    elif [ -s "$g/stderr" ]
    then
      echo "Skipping $g because its stderr is not empty."
    else
      BL=$(sed -n -e '2p' "$g/case.csv")
      zcat "$g/$f.csv.gz" | sed -e "1d;s/^/$BL,/;s/null/NA/g" >> results/$f.csv
    fi
  done
  gzip -9f results/$f.csv
done
