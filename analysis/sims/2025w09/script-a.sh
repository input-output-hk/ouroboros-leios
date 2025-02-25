#!/usr/bin/env bash

HOST=thelio
DB=leios2025w09a
HS_EXE=../../../dist-newstyle/build/x86_64-linux/ghc-9.8.3/ouroboros-leios-sim-0.1.0.0/x/ols/build/ols/ols
RS_EXE=../../../sim-rs/target/release/sim-cli

IB_RATES="0.05 0.10 0.20 0.30 0.50 1.00 2.00 3.00 5.00 10.00 20.00 30.00 50.00 100.00"

if [[ ! -p sim.log ]]
then
  mkfifo sim.log
fi

mongo --host "$HOST" "$DB" reset.js

mongo --host "$HOST" "$DB" clear-hs.js

for ibRate in $IB_RATES
do
  yaml2json config.default.yaml \
  | jq '."ib-generation-probability" = '"$ibRate" \
  > tmp.config.json
  cat << EOI > tmp.scenario.js
const scenario = {"ib-generation-probability" : $ibRate};
const simulator = "haskell";
EOI
  mongoimport --host "$HOST" --db "$DB" --collection raw --drop sim.log &
  "$HS_EXE" sim short-leios \
            --leios-config-file tmp.config.json \
            --topology-file topo-default-100.yaml \
            --output-file sim.json \
            --output-seconds 150
  mongo --host "$HOST" "$DB" tmp.scenario.js transform-hs.js ingest.js
done

mongo --host "$HOST" "$DB" clear-rs.js

for ibRate in $IB_RATES
do
  yaml2json config.default.yaml \
  | jq '."ib-generation-probability" = '"$ibRate" \
  | jq '."tx-generation-distribution" = {distribution: "constant", value: 1000000}' \
  | jq '."ib-head-size-bytes" = 102704' \
  > tmp.config.json
  cat << EOI > tmp.scenario.js
const scenario = {"ib-generation-probability" : $ibRate};
const simulator = "rust";
EOI
  mongoimport --host "$HOST" --db "$DB" --collection raw --drop sim.log &
  "$RS_EXE" --parameters tmp.config.json \
            topo-default-100.yaml \
            --slots 150 \
            sim.log
  mongo --host "$HOST" "$DB" tmp.scenario.js transform-rs.js ingest.js
done

