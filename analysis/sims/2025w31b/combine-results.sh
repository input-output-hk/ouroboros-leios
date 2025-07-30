#!/usr/bin/env nix-shell
#!nix-shell -i bash -p gnused gzip pigz "rWrapper.override { packages = with rPackages; [ data_table R_utils bit64 ggplot2 magrittr stringr ]; }"

set -e

mkdir -p results/$d
for f in lifecycle resources receipts cpus sizes
do
  DIR=$(find experiments -type f -name $f.csv.gz \( -not -empty \) -printf %h\\n -quit)
  HL=$(sed -n -e '1p' "$DIR/case.csv")
  HR=$(zcat "$DIR/$f.csv.gz" | sed -n -e '1p')
  if [[ "$f" == "lifecycle" || "$f" == "resources" || "$f" == "sizes" ]]
  then
    FRACT=1.00
  else
    FRACT=1.00
  fi
  (
    echo "$HL,$HR"
    for g in $(find experiments -type f -name $f.csv.gz \( -not -empty \) -printf %h\\n)
    do
      if [ ! -e "$g/stderr" ]
      then
        echo "Skipping $g because it has no stderr." >> /dev/stderr
      elif [ -s "$g/stderr" ]
      then
        echo "Skipping $g because its stderr is not empty." >> /dev/stderr
      else
        BL=$(sed -n -e '2p' "$g/case.csv")
        zcat "$g/$f.csv.gz" | gawk 'FNR > 1 && rand() <= '"$FRACT"' { print "'"$BL"'" "," $0}'
      fi
    done
  ) | pigz -p 3 -9c > results/$f.csv.gz
R --vanilla << EOI > /dev/null
require(data.table)
sampleSize <- $FRACT
print(sampleSize)
$f <- fread("results/$f.csv.gz", stringsAsFactors=TRUE)
save($f, sampleSize, file="results/$f.Rdata", compression_level=9)
EOI
done
