#!/usr/bin/env bash

HOST=thelio
DB=leios2025w08

if [[ ! -p sim.log ]]
then
  mkfifo sim.log
fi

mongo --host "$HOST" "$DB" reset.js

for ibRate in 0.05 0.10 0.20 0.30 0.50 1.00 2.00 3.00 5.00 10.00 20.00 30.00 50.00 100.00
do
  yaml2json config.default.yaml \
  | jq '."ib-generation-probability" = '"$ibRate" \
  > tmp.config.json
  echo 'const s = {"ib-generation-probability" : '"$ibRate"'}' > tmp.scenario.js
  mongoimport --host "$HOST" --db "$DB" --collection raw --drop sim.log &
  cabal run exe:ols -- sim short-leios \
                    --leios-config-file tmp.config.json \
                    --topology-file topo-default-100.yaml \
                    --output-file sim.json \
                    --output-seconds 150
  mongo --host "$HOST" "$DB" tmp.scenario.js ingest.js
done

