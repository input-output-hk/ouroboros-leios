#!/usr/bin/env nix-shell
#!nix-shell -i bash -p gzip

set -e

mkdir -p results/{tps,ibs}

for d in ibs tps
do
  for f in cpus lifecycle resources receipts
  do
    echo "----- $d ----- $f -----"
    DIR=$(find $d -type f -name $f.csv.gz \( -not -empty \) -printf %h\\n -quit)
    HL=$(sed -n -e '1p' "$DIR/case.csv")
    HR=$(zcat "$DIR/$f.csv.gz" | sed -n -e '1p')
    echo "$HL,$HR" > results/$d/$f.csv
    for g in $(find $d -type f -name $f.csv.gz \( -not -empty \) -printf %h\\n)
    do
      if [ ! -e "$g/stderr" ]
      then
        echo "Skipping $g because it has no stderr."
      elif [ -s "$g/stderr" ]
      then
        echo "Skipping $g because its stderr is not empty."
      else
        BL=$(sed -n -e '2p' "$g/case.csv")
        zcat "$g/$f.csv.gz" | sed -e "1d;s/^/$BL,/;s/null/NA/g" >> results/$d/$f.csv
      fi
    done
    gawk 'BEGIN {FS=","} {print NF}' results/$d/$f.csv | uniq | sort -u
    pigz -9f results/$d/$f.csv &
  done
  echo "-----  -------"
  wait
done
