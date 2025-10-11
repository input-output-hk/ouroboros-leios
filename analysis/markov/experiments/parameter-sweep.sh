#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

EXE="../.lake/build/bin/linleios"


function setDefaults {
  Label="NA"
  Lhdr=1
  Lvote=4
  Ldiff=7
  Committee=600
  Quorum=0.75
  Validates=1
  Late=0
  Adversary=0
}

function runModel {
  "$EXE" --l-header $Lhdr \
         --l-vote $Lvote \
         --l-diff $Ldiff \
         --committee-size $Committee \
         --quorum-fraction $Quorum \
         --p-rb-header-arrives 1 \
         --p-eb-validates $Validates \
         --p-late-diffusion $Late \
         --adversary-fraction $Adversary \
         2> /dev/null \
  | yaml2json \
  | jq -r '"'"$Label,$Lhdr,$Lvote,$Ldiff,$Committee,$Quorum,$Validates,$Late,$Adversary,"'" + (."EB efficiency" | tostring)'
}


(

echo $'Label,L_hdr,L_vote,L_diff,Committee size,Quorum fraction,Probability of EB validation,Probability of late diffusion,Adversary fraction,EB efficiency'

setDefaults
Label="Ideal conditions with adversary"
for Adversary in $(seq 0.00 0.01 0.35)
do
  runModel
done

setDefaults
Label="Non-ideal network without adversary"
for Validates in $(seq 0.60 0.02 1.00)
do
  for Late in $(seq 0.00 0.02 1.00)
  do
    runModel
  done
done

setDefaults
Label="Committee and quorum without adversary"
for Committee in $(seq 500 50 1000)
do
  for Quorum in $(seq 0.50 0.02 1.00)
  do
    runModel
  done
done

setDefaults
Label="Protocol parameters without adversary"
for Lhdr in 1 2
do
  for Lvote in 3 4 5
  do
    for Ldiff in 4 5 6 7 8
    do
      runModel
    done
  done
done

) | gzip -9c > parameter-sweep.csv.gz
