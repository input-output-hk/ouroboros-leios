#!/usr/bin/env bash

HOST=thelio
DB=leios2025w09b
HS_EXE=../../../dist-newstyle/build/x86_64-linux/ghc-9.8.3/ouroboros-leios-sim-0.1.0.0/x/ols/build/ols/ols
RS_EXE=../../../sim-rs/target/release/sim-cli

IB_RATES="0.5 1.0 2.0 5.0 10.0 15.0 30.0 60.0"
IB_SIZES="2500 50000 100000 200000"

if [[ ! -p sim.log ]]
then
  mkfifo sim.log
fi

mongo --host "$HOST" "$DB" << EOI
db.haskell.deleteMany({})
EOI

for ibRate in $IB_RATES
do
  for ibSize in $IB_SIZES
  do
    yaml2json config.default.yaml \
    | jq '."ib-generation-probability" = '"$ibRate" \
    | jq '."ib-body-avg-size-bytes" = '"$ibSize" \
    | jq '."ib-body-max-size-bytes" = '"$ibSize" \
    > tmp.config.json
    cat << EOI > tmp.scenario.js
const scenario = {"ib-generation-probability" : $ibRate, "ib-body-avg-size-bytes" : $ibSize};
const simulator = "haskell";
EOI
    mongoimport --host "$HOST" --db "$DB" --collection raw --drop sim.log &
    "$HS_EXE" sim short-leios \
              --leios-config-file tmp.config.json \
              --topology-file topo-default-100.yaml \
              --output-file sim.json \
              --output-seconds 150
    mongo --host "$HOST" "$DB" tmp.scenario.js import.js
  done
done

mongo --host "$HOST" "$DB" << EOI
db.rust.deleteMany({})
EOI

for ibRate in $IB_RATES
do
  for ibSize in $IB_SIZES
  do
    yaml2json config.default.yaml \
    | jq '."ib-generation-probability" = '"$ibRate" \
    | jq '."tx-generation-distribution" = {distribution: "constant", value: 1000000}' \
    | jq '."ib-head-size-bytes" = '"$((ibSize + 304))" \
    > tmp.config.json
      cat << EOI > tmp.scenario.js
const scenario = {"ib-generation-probability" : $ibRate, "ib-body-avg-size-bytes" : $ibSize};
const simulator = "rust";
EOI
    mongoimport --host "$HOST" --db "$DB" --collection raw --drop sim.log &
    "$RS_EXE" --parameters tmp.config.json \
              topo-default-100.yaml \
              --slots 150 \
              sim.log
      mongo --host "$HOST" "$DB" tmp.scenario.js import.js
  done
done

