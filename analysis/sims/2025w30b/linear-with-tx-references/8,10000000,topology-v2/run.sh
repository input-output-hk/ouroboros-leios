#!/usr/bin/env nix-shell
#!nix-shell -i bash -p ansifilter gnugrep gnused gzip pigz bc

set -eo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")"

BW=50
VARIANT=$(basename "$(dirname "$PWD")")
LABEL=$(basename "$PWD")
STAGE_LENGTH=$(echo $LABEL | sed -e 's/^\(.*\),\(.*\),\(.*\)$/\1/')
BLOCK_SIZE=$(echo $LABEL | sed -e 's/^\(.*\),\(.*\),\(.*\)$/\2/')
NETWORK=$(echo $LABEL | sed -e 's/^\(.*\),\(.*\),\(.*\)$/\3/')

ulimit -S -m 144000000 -v 144000000

mkfifo sim.log

sed -e 's/"bandwidth-bytes-per-second":125000000/"bandwidth-bytes-per-second":'"$((125000 * BW))"'/g' \
  "../../../../../data/simulation/pseudo-mainnet/$NETWORK.yaml" \
  > network.yaml

sed -e '/^leios-variant:/s/:.*$/: '"$VARIANT"'/' \
    -e '/^linear-vote-stage-length-slots:/s/:.*$/: '"$STAGE_LENGTH"'/' \
    -e '/^linear-diffuse-stage-length-slots:/s/:.*$/: '"$STAGE_LENGTH"'/' \
    -e '/^leios-stage-length-slots:/s/:.*$/: '"$STAGE_LENGTH"'/' \
    -e '/^eb-referenced-txs-max-size-bytes:/s/:.*$/: '"$BLOCK_SIZE"'/' \
    -e '/^eb-body-avg-size-bytes:/s/:.*$/: '"$BLOCK_SIZE"'/' \
    ../../linear/8,10000000,topology-v2/config.template.yaml \
> config.yaml

function cleanup() {
  rm sim.log
  rm network.yaml
}
trap cleanup EXIT

grep -E -v '(Slot|No.*Generated|CpuTask|Lottery)' sim.log | pigz -p 3 -9c > sim.log.gz &

../../sim-cli --parameters config.yaml network.yaml --slots 750 --conformance-events sim.log > stdout 2> stderr

wait

cat << EOI > case.csv
Simulator,Variant,Stage length,Max EB size,Network
Rust,$VARIANT,$STAGE_LENGTH slot/stage,$(echo "scale=1 ; $BLOCK_SIZE / 1000000" | bc | sed -e 's/^\./0./') MB/EB,$NETWORK
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
