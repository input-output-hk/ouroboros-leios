#!/usr/bin/env bash
set -euo pipefail

TOPO="${1:?Usage: $0 <topo.json> <schedule.json> <results-dir> [--duration N] ...}"
SCHEDULE="${2:?Usage: $0 <topo.json> <schedule.json> <results-dir> [--duration N] ...}"
RESULTS="${3:?Usage: $0 <topo.json> <schedule.json> <results-dir> [--duration N] ...}"
shift 3

docker build -f Dockerfile.mininet -t mininet-p2p-sim .

rm -rf "$RESULTS"
mkdir -p "$RESULTS"

# Merge topology + schedule into a single input.json and pipe to container.
nix-shell -p jq --run "jq -s '.[0] + {schedule: .[1]}' '$TOPO' '$SCHEDULE'" \
| docker run --rm --privileged -i \
    -v "$(pwd)/$RESULTS:/sim/mininet-results" \
    ${SCHEDULER:+-e SCHEDULER_MODULE=$SCHEDULER} \
    ${FULLHEDGE_SHUFFLE:+-e FULLHEDGE_SHUFFLE=$FULLHEDGE_SHUFFLE} \
    ${USE_BBR:+-e USE_BBR=$USE_BBR} \
    mininet-p2p-sim "$@"

export RESULTS_DIR="$RESULTS"

nix-shell -p python3 python3Packages.scapy python3Packages.matplotlib \
    --run 'python3 plot_mininet.py'

nix-shell -p graphviz python3 \
    --run 'python3 plot_topology.py'
