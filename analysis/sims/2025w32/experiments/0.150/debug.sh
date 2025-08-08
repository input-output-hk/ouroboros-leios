#!/usr/bin/env nix-shell
#!nix-shell -i bash -p ansifilter gnugrep gnused gzip pigz bc remarshal jq

set -eo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")"

TX_SIZE=1500
TX_START=60
TX_STOP=960
SIM_STOP=1500
BW=10
CPU_COUNT=4
EB_RATE=2.5
NETWORK=topology-v2
LABEL=$(basename "$PWD")
VARIANT=linear-with-tx-references
STAGE_LENGTH=10
BLOCK_SIZE=15
THROUGHPUT="$LABEL"

ulimit -S -m 48000000 -v 48000000

if [[ -e sim.log ]]
then
  rm sim.log
fi

mkfifo sim.log

sed -e 's/"bandwidth-bytes-per-second":125000000,/"bandwidth-bytes-per-second":'"$((125000 * BW))"',/g' \
    -e 's/"cpu-core-count":6,/"cpu-core-count":'"$CPU_COUNT"',/g' \
  "../../../../../data/simulation/pseudo-mainnet/$NETWORK.yaml" \
  > network.yaml

function cleanup() {
  rm sim.log
}
trap cleanup EXIT

grep -E -v '(Slot|No.*Generated|CpuTask|Lottery)' sim.log | pigz -p 3 -9c > sim.log.gz &

../../../../../sim-rs/target/release/sim-cli --parameters config.yaml network.yaml --slots "$SIM_STOP" --conformance-events sim.log > stdout 2> stderr

wait

