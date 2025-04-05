#!/usr/bin/env bash

set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

echo "SCENARIO: rust | 600 | oldest-first | 100-nodes | 10.0 | 98304 | 1.5 | 20"

if [[ ! -p sim.log ]]
then
  mkfifo sim.log
fi

cleanup() {
  if [[ -p sim.log ]]
  then
    rm sim.log
  fi
}

trap cleanup EXIT

mongoimport --quiet --host "$HOST" --db "$DB" --collection "RAW_f2117979" --drop sim.log &

../../sim-cli --parameters config.json network.yaml --slots 600 sim.log > stdout 2> stderr

echo "SCENARIO: rust | 600 | oldest-first | 100-nodes | 10.0 | 98304 | 1.5 | 20"

mongo --quiet --host "$HOST" "$DB" scenario.js "../../queries/import.js"
