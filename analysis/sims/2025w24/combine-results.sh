#!/usr/bin/env nix-shell
#!nix-shell -i bash -p gzip

set -e

mkdir -p results/{tps,ibs}

for d in ibs tps
do
  for f in cpus lifecycle resources receipts
  do
    DIR=$(find $d -type f -name $f.csv.gz \( -not -empty \) -printf %h\\n -quit)
    HL=$(sed -n -e '1p' "$DIR/case.csv")
    HR=$(zcat "$DIR/$f.csv.gz" | sed -n -e '1p')
    (
      echo "$HL,$HR"
      for g in $(find $d -type f -name $f.csv.gz \( -not -empty \) -printf %h\\n)
      do
        if [ ! -e "$g/stderr" ]
        then
          echo "Skipping $g because it has no stderr." >> /dev/stderr
        elif [ -s "$g/stderr" ]
        then
          echo "Skipping $g because its stderr is not empty." >> /dev/stderr
        else
          BL=$(sed -n -e '2p' "$g/case.csv")
          zcat "$g/$f.csv.gz" | sed -e "1d;s/^/$BL,/;s/null/NA/g"
        fi
      done
    ) | gzip -9c > results/$d/$f.csv.gz &
  done
done
wait
