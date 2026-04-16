#!/usr/bin/env bash
set -euo pipefail

# Benchmark different committee selection algorithms across engines.
#
# Usage:
#   ./scripts/cip-voting-options.sh [options]
#
# Options:
#   -t, --topology PATH          Topology file (leafname, rel or abs path). Default: topology-v2-cip.yaml
#   -T, --throughput LIST        Comma-separated throughputs. Default: all
#   -m, --mode LIST              Comma-separated committee modes. Default: all
#   -e, --engine ENGINE          Engine: actor | sequential | turbo. Default: turbo
#   -s, --slots N                Number of slots. Default: 1500
#       --quorum-fraction FRAC   Default: 0.60
#       --stake-fraction FRAC    Default: 0.95
#   -h, --help                   Show this help
#
# Engine choices:
#   actor       — tokio async actor system (single-shard, non-deterministic by design)
#   sequential  — single-shard sequential DES (deterministic)
#   turbo       — sequential DES with 6 shards and zero-latency clusters (non-deterministic, fast)
#
# Examples:
#   ./scripts/cip-voting-options.sh                                     # all defaults (turbo)
#   ./scripts/cip-voting-options.sh -t topology-v1.yaml                 # mainnet-scale
#   ./scripts/cip-voting-options.sh -T 0.250 -m everyone                # single run
#   ./scripts/cip-voting-options.sh -T 0.250,0.300 -m wfa-ls,everyone
#   ./scripts/cip-voting-options.sh -e sequential -T 0.200 -m wfa-ls    # determinism check
#   ./scripts/cip-voting-options.sh --slots 500 -m top-stake-fraction
#
# Vote thresholds are auto-computed at QUORUM_FRACTION of expected committee size.

usage() {
    sed -n '3,/^$/p' "$0" | sed 's/^# \?//'
    exit "${1:-0}"
}

# Defaults
TOPO_ARG="-"
THROUGHPUT_ARG="-"
MODE_ARG="-"
ENGINE="turbo"
SLOTS="${SLOTS:-1500}"
QUORUM_FRACTION="${QUORUM_FRACTION:-0.60}"
STAKE_FRACTION="${STAKE_FRACTION:-0.95}"

ALL_THROUGHPUTS=(0.150 0.200 0.250 0.300 0.350)
ALL_MODES=("wfa-ls" "everyone" "top-stake-fraction")

while [[ $# -gt 0 ]]; do
    case "$1" in
        -t|--topology)      TOPO_ARG="$2"; shift 2 ;;
        -T|--throughput)    THROUGHPUT_ARG="$2"; shift 2 ;;
        -m|--mode)          MODE_ARG="$2"; shift 2 ;;
        -e|--engine)        ENGINE="$2"; shift 2 ;;
        -s|--slots)         SLOTS="$2"; shift 2 ;;
        --quorum-fraction)  QUORUM_FRACTION="$2"; shift 2 ;;
        --stake-fraction)   STAKE_FRACTION="$2"; shift 2 ;;
        -h|--help)          usage 0 ;;
        *)                  echo "ERROR: unknown option '$1'" >&2; usage 1 ;;
    esac
done

case "$ENGINE" in
    actor|sequential|turbo) ;;
    *) echo "ERROR: --engine must be one of: actor, sequential, turbo (got '$ENGINE')" >&2; exit 1 ;;
esac

# Paths (relative to sim-rs/)
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SIM_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
TOPO_DATA="$SIM_DIR/../data/simulation/pseudo-mainnet"
if [[ "$TOPO_ARG" == "-" ]]; then
    TOPOLOGY="$TOPO_DATA/topology-v2-cip.yaml"
elif [[ "$TOPO_ARG" == /* ]]; then
    TOPOLOGY="$TOPO_ARG"
elif [[ -f "$TOPO_ARG" ]]; then
    TOPOLOGY="$TOPO_ARG"
elif [[ -f "$TOPO_DATA/$TOPO_ARG" ]]; then
    TOPOLOGY="$TOPO_DATA/$TOPO_ARG"
else
    echo "ERROR: cannot find topology '$TOPO_ARG'" >&2
    echo "  Looked in: ./ and $TOPO_DATA/" >&2
    exit 1
fi

if [[ "$THROUGHPUT_ARG" == "-" ]]; then
    THROUGHPUTS=("${ALL_THROUGHPUTS[@]}")
else
    IFS=',' read -ra THROUGHPUTS <<< "$THROUGHPUT_ARG"
fi
if [[ "$MODE_ARG" == "-" ]]; then
    MODES_FILTER=("${ALL_MODES[@]}")
else
    IFS=',' read -ra MODES_FILTER <<< "$MODE_ARG"
fi

EXPERIMENTS="$SIM_DIR/../analysis/sims/cip/experiments"
MEMORY_LIMIT="$SIM_DIR/parameters/memory-limit.yaml"
TURBO="$SIM_DIR/parameters/turbo.yaml"
RESULTS="$SIM_DIR/voting_results.csv"

cd "$SIM_DIR"

# Auto-compute committee sizes and vote thresholds from topology
read -r TOTAL_NODES STAKING_NODES TOP_STAKE_NODES < <(python3 -c "
import json, yaml, sys
with open('$TOPOLOGY') as f:
    first = f.read(1); f.seek(0)
    d = json.load(f) if first == '{' else yaml.safe_load(f)
nodes = d['nodes']
if isinstance(nodes, dict):
    stakes = [n.get('stake', 0) for n in nodes.values()]
else:
    stakes = [n.get('stake', 0) for n in nodes]
total_nodes = len(stakes)
staking = sorted([s for s in stakes if s > 0], reverse=True)
total_stake = sum(staking)
threshold = total_stake * $STAKE_FRACTION
cum = 0
top_n = 0
for s in staking:
    if cum >= threshold: break
    cum += s
    top_n += 1
print(total_nodes, len(staking), top_n)
")

# committee-selection-algorithm values and corresponding vote thresholds.
# wfa-ls: VRF lottery with 600 total trials (480 persistent + 120 non-persistent), 75% quorum
# everyone: all nodes vote (1 each)
# top-stake-fraction: top ${STAKE_FRACTION} of cumulative stake
declare -A VOTE_THRESHOLDS=(
    ["wfa-ls"]=450
    ["everyone"]=$(python3 -c "import math; print(math.ceil($TOTAL_NODES * $QUORUM_FRACTION))")
    ["top-stake-fraction"]=$(python3 -c "import math; print(math.ceil($TOP_STAKE_NODES * $QUORUM_FRACTION))")
)

# Build the engine-specific parameter file.
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

ENGINE_PARAMS=()
case "$ENGINE" in
    actor)
        # Default engine is actor; shard-count defaults to 1. Nothing to add.
        ;;
    sequential)
        engine_override="$WORK/engine-sequential.yaml"
        {
            echo "engine: sequential"
            echo "shard-count: 1"
        } > "$engine_override"
        ENGINE_PARAMS=(-p "$engine_override")
        ;;
    turbo)
        ENGINE_PARAMS=(-p "$TURBO")
        ;;
esac

echo "Topology: $TOPOLOGY" >&2
echo "  Total nodes: $TOTAL_NODES, Staking: $STAKING_NODES" >&2
echo "  Top ${STAKE_FRACTION} stake: $TOP_STAKE_NODES nodes" >&2
echo "  Vote thresholds: wfa-ls=${VOTE_THRESHOLDS[wfa-ls]}, everyone=${VOTE_THRESHOLDS[everyone]}, top-stake-fraction=${VOTE_THRESHOLDS[top-stake-fraction]}" >&2
echo "Engine: $ENGINE" >&2
echo "Slots: $SLOTS" >&2
echo "" >&2

echo "Building release binary..."
cargo build --release

HEADER="throughput,committee,engine,time_seconds,total_ebs,uncertified_ebs,ebs_with_endorsement,total_votes,votes_per_eb_mean,votes_per_eb_stddev"
echo ""
if [[ ! -f "$RESULTS" ]]; then
    echo "$HEADER" | tee "$RESULTS"
else
    echo "$HEADER"
fi

for throughput in "${THROUGHPUTS[@]}"; do
    config="$EXPERIMENTS/NA,$throughput/config.yaml"
    if [[ ! -f "$config" ]]; then
        echo "WARNING: $config not found, skipping" >&2
        continue
    fi

    for mode in "${MODES_FILTER[@]}"; do
        # Build a mode-specific override file
        override="$WORK/override-$mode.yaml"
        {
            echo "committee-selection-algorithm: \"$mode\""
            echo "vote-threshold: ${VOTE_THRESHOLDS[$mode]}"
            if [[ "$mode" == "wfa-ls" ]]; then
                # 600 total VRF trials, 80:20 persistent/non-persistent split
                echo "persistent-vote-generation-probability: 480"
                echo "non-persistent-vote-generation-probability: 120"
            fi
            if [[ "$mode" == "top-stake-fraction" ]]; then
                echo "committee-stake-fraction-threshold: $STAKE_FRACTION"
            fi
        } > "$override"

        params=(-p "$config" -p "$MEMORY_LIMIT" "${ENGINE_PARAMS[@]}" -p "$override")

        echo -n "Running throughput=$throughput committee=$mode engine=$ENGINE ... " >&2
        start=$(date +%s.%N)
        output=$( cargo run --release -- "$TOPOLOGY" "${params[@]}" -s "$SLOTS" 2>&1 | tee /dev/stderr )
        end=$(date +%s.%N)
        elapsed=$(echo "$end - $start" | bc)

        # Parse stats from log output
        total_ebs=$(echo "$output" | grep -oP '\d+(?= EB\(s\) were generated)' | head -1)
        total_ebs=${total_ebs:-0}

        uncertified_ebs=$(echo "$output" | grep -oP '\d+(?= out of \d+ EB\(s\) did not reach the vote threshold)' | head -1)
        uncertified_ebs=${uncertified_ebs:-0}

        ebs_with_endorsement=$(echo "$output" | grep -oP '\d+(?= L1 block\(s\) had a Leios endorsement)' | head -1)
        ebs_with_endorsement=${ebs_with_endorsement:-0}

        total_votes=$(echo "$output" | grep -oP '\d+(?= total votes were generated)' | head -1)
        total_votes=${total_votes:-0}

        votes_per_eb_mean=$(echo "$output" | grep -oP 'Each EB received an average of \K[\d.]+' | head -1)
        votes_per_eb_mean=${votes_per_eb_mean:-0}

        votes_per_eb_stddev=$(echo "$output" | grep -oP 'Each EB received an average of [\d.]+ vote\(s\) \(stddev \K[\d.]+' | head -1)
        votes_per_eb_stddev=${votes_per_eb_stddev:-0}

        echo "$throughput,$mode,$ENGINE,$elapsed,$total_ebs,$uncertified_ebs,$ebs_with_endorsement,$total_votes,$votes_per_eb_mean,$votes_per_eb_stddev" | tee -a "$RESULTS"
        echo "done (${elapsed}s)" >&2
    done
done

echo "" >&2
echo "Results saved to $RESULTS" >&2
