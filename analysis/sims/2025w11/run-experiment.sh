#!/usr/bin/env bash

HS_EXE=./ols
RS_EXE=./sim-cli

mkdir -p tmp
if [[ ! -p sim.log ]]
then
  mkfifo sim.log
fi

function mkScenario() {
  SIMULATOR="$1"
  echo "SCENARIO: $SIMULATOR | $label | $NETWORK | $ibRate | $ibSize | $stageLength"
  yaml2json "config.$label.yaml" \
  | jq '."ib-generation-probability" = '"$ibRate" \
  | jq '."ib-body-avg-size-bytes" = '"$ibSize" \
  | jq '."ib-body-max-size-bytes" = '"$ibSize" \
  | jq '."leios-stage-length-slots" = '"$stageLength" \
  > tmp/config.json
  SCENARIO='{"label":"'"$label"'","network":"'"$NETWORK"'","ib-generation-probability":'"$ibRate"',"ib-body-avg-size-bytes":'"$ibSize"',"leios-stage-length-slots":'"$stageLength"'}'
  echo 'const scenario = '"$SCENARIO"';' > tmp/scenario.js
  echo 'const simulator = "'"$SIMULATOR"'";' >> tmp/scenario.js
  echo 'db.'"$SIMULATOR"'.deleteMany({scenario: '"$SCENARIO"'})' | mongo --quiet --host "$HOST" "$DB"
}

source env.sh

NETWORK=100
MAX_SLOT=600


#### CPU vs no CPU

IB_RATES="5.0 50.0"
IB_SIZES="98304"

for label in with-cpu without-cpu
do
  for ibRate in $IB_RATES
  do
    for ibSize in $IB_SIZES
    do
      stageLength=20 mkScenario haskell
      mongoimport --host "$HOST" --db "$DB" --collection raw --drop sim.log &
      "$HS_EXE" sim short-leios \
                --leios-config-file tmp/config.json \
                --topology-file topo-default-100.yaml \
                --output-file sim.log \
                --output-seconds "$MAX_SLOT"
      echo "SCENARIO: $SIMULATOR | $label | $NETWORK | $ibRate | $ibSize | $stageLength"
      mongo --host "$HOST" "$DB" tmp/scenario.js queries/import.js
    done
  done
done

for label in with-cpu without-cpu
do
  for ibRate in $IB_RATES
  do
    for ibSize in $IB_SIZES
    do
      stageLength=20 mkScenario rust
      mongoimport --host "$HOST" --db "$DB" --collection raw --drop sim.log &
      "$RS_EXE" --parameters tmp/config.json \
                topo-default-100.yaml \
                --slots "$MAX_SLOT" \
                sim.log
      echo "SCENARIO: $SIMULATOR | $label | $NETWORK | $ibRate | $ibSize | $stageLength"
      mongo --host "$HOST" "$DB" tmp/scenario.js queries/import.js
    done
  done
done


#### Full factorial on defaults

STAGE_LENGTHS="20 40 60"
IB_RATES="0.1 0.3 1.0 3.0 10.0 30.0"
IB_SIZES="32768 65536 98304 131072 163840"

for label in default
do
  for stageLength in $STAGE_LENGTHS
  do
    for ibRate in $IB_RATES
    do
      for ibSize in $IB_SIZES
      do
        mkScenario haskell
        mongoimport --host "$HOST" --db "$DB" --collection raw --drop sim.log &
        "$HS_EXE" sim short-leios \
                  --leios-config-file tmp/config.json \
                  --topology-file topo-default-100.yaml \
                  --output-file sim.log \
                  --output-seconds "$MAX_SLOT"
        echo "SCENARIO: $SIMULATOR | $label | $NETWORK | $ibRate | $ibSize | $stageLength"
        mongo --quiet --host "$HOST" "$DB" tmp/scenario.js queries/import.js
      done
    done
  done
done

for label in default
do
  for stageLength in $STAGE_LENGTHS
  do
    for ibRate in $IB_RATES
    do
      for ibSize in $IB_SIZES
      do
        mkScenario rust
        mongoimport --host "$HOST" --db "$DB" --collection raw --drop sim.log &
        "$RS_EXE" --parameters tmp/config.json \
                  topo-default-100.yaml \
                  --slots "$MAX_SLOT" \
                  sim.log
        echo "SCENARIO: $SIMULATOR | $label | $NETWORK | $ibRate | $ibSize | $stageLength"
        mongo --quiet --host "$HOST" "$DB" tmp/scenario.js queries/import.js
      done
    done
  done
done

