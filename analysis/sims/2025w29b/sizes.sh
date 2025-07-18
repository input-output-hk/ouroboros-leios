#!/usr/bin/env bash

echo 'Simulator,Variant,Stage length,Max EB size,Kind,Item,Generated [s],Transactions,Endorses' > sizes.csv

for d in {linear,linear-with-tx-references}/*
do
  PREFIX=$(tail -n 1 $d/case.csv)
  zcat $d/sim.log.gz \
  | grep -E '(EB|RB)Generated' \
  | jq -r '
    "'"$PREFIX"'"
    + "," + .message.type[0:2]
    + "," + .message.id
    + "," + (.time_s | tostring)
    + "," + (.message.transactions | length | tostring)
    + "," + (if .message.endorsement then .message.endorsement.eb.id else "NA" end)
  ' \
  >> sizes.csv
done
