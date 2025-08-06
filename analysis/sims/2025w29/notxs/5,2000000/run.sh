#!/usr/bin/env nix-shell
#!nix-shell -i bash -p ansifilter gnugrep gnused gzip pigz

set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

BW=50
LABEL=$(basename "$PWD")
STAGE_LENGTH=$(echo $LABEL | sed -e 's/,.*$//')
BLOCK_SIZE=$(echo $LABEL | sed -e 's/^.*,//')

ulimit -S -m 128000000 -v 128000000

mkfifo sim.log

sed -e 's/"bandwidth-bytes-per-second":125000000/"bandwidth-bytes-per-second":'"$((125000 * BW))"'/g' \
  ../../../../../data/simulation/pseudo-mainnet/topology-v2.yaml \
  > network.yaml

function cleanup() {
  rm sim.log
  rm network.yaml
}
trap cleanup EXIT

grep -E -v '(Slot|No.*Generated|CpuTask|Lottery)' sim.log | pigz -p 3 -9c > sim.log.gz &

../../sim-cli --parameters config.yaml network.yaml --slots 1200 --conformance-events sim.log > stdout 2> stderr

wait

cat << EOI > case.csv
Simulator,Stage length,Max EB size
Rust,$STAGE_LENGTH slot/stage,$(echo "scale=1 ; $BLOCK_SIZE / 1000000" | bc | sed -e 's/^\./0./') MB/EB
EOI

zcat sim.log.gz \
| ../../leios-trace-processor \
  +RTS -N5 -RTS \
  --trace-file /dev/stdin \
  --lifecycle-file lifecycle.csv \
  --cpu-file cpus.csv \
  --resource-file resources.csv \
  --receipt-file receipts.csv
  
pigz -p 3 -9f {lifecycle,cpus,resources,receipts}.csv

cat case.csv

ansifilter stdout | grep -E '^ INFO (praos|leios|network): ' > summary.txt
