#!/usr/bin/env bash

set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

echo "SCENARIO: haskell | 600 | default | 100-nodes | 15.0 | 98304 | 2.0 | 20"

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

mongoimport --quiet --host "$HOST" --db "$DB" --collection "RAW_41a54bfc" --drop sim.log &

../../ols sim short-leios --leios-config-file config.json --topology-file network.yaml --output-file sim.log --output-seconds 600 > stdout 2> stderr

echo "SCENARIO: haskell | 600 | default | 100-nodes | 15.0 | 98304 | 2.0 | 20"

mongo --quiet --host "$HOST" "$DB" scenario.js "../../queries/import.js"
