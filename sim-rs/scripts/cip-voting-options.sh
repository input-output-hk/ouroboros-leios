#!/usr/bin/env bash
set -euo pipefail

# Benchmark different committee selection algorithms.
# Always uses turbo mode (sequential engine, sharded).
#
# Usage: ./scripts/cip-voting-options.sh [topology] [throughput,...] [mode,...]
#
# Examples:
#   ./scripts/cip-voting-options.sh                              # all defaults
#   ./scripts/cip-voting-options.sh topology-v1.yaml             # mainnet-scale
#   ./scripts/cip-voting-options.sh - 0.250 everyone             # single run, default topology
#   ./scripts/cip-voting-options.sh - 0.250,0.300 wfa-ls,everyone
#   SLOTS=500 ./scripts/cip-voting-options.sh - - top-stake-fraction
#
# Topology can be a leafname (resolved in data/simulation/pseudo-mainnet/),
# a relative path, or an absolute path. Use "-" for the default.
# Vote thresholds are auto-computed at 60% of expected committee size.

# Configuration
SLOTS="${SLOTS:-1500}"
ALL_THROUGHPUTS=(0.150 0.200 0.250 0.300 0.350)
ALL_MODES=("wfa-ls" "everyone" "top-stake-fraction")
QUORUM_FRACTION="${QUORUM_FRACTION:-0.60}"
STAKE_FRACTION="${STAKE_FRACTION:-0.95}"

# Paths (relative to sim-rs/)
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SIM_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
TOPO_ARG="${1:--}"
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

# Parse throughput and mode filters (comma-separated, "-" or omitted = all)
THROUGHPUT_ARG="${2:--}"
MODE_ARG="${3:--}"
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
# wfa-ls: VRF lottery with CIP default expected committee (~600), threshold from config
# everyone: all nodes vote (1 each)
# top-stake-fraction: top ${STAKE_FRACTION} of cumulative stake
declare -A VOTE_THRESHOLDS=(
    ["wfa-ls"]=450
    ["everyone"]=$(python3 -c "import math; print(math.ceil($TOTAL_NODES * $QUORUM_FRACTION))")
    ["top-stake-fraction"]=$(python3 -c "import math; print(math.ceil($TOP_STAKE_NODES * $QUORUM_FRACTION))")
)

echo "Topology: $TOPOLOGY" >&2
echo "  Total nodes: $TOTAL_NODES, Staking: $STAKING_NODES" >&2
echo "  Top ${STAKE_FRACTION} stake: $TOP_STAKE_NODES nodes" >&2
echo "  Vote thresholds: wfa-ls=${VOTE_THRESHOLDS[wfa-ls]}, everyone=${VOTE_THRESHOLDS[everyone]}, top-stake-fraction=${VOTE_THRESHOLDS[top-stake-fraction]}" >&2
echo "" >&2

echo "Building release binary..."
cargo build --release

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

HEADER="throughput,committee,time_seconds,total_ebs,uncertified_ebs,ebs_with_endorsement,total_votes,votes_per_eb_mean,votes_per_eb_stddev"
echo ""
if [[ ! -f "$RESULTS" ]] || ! head -1 "$RESULTS" | grep -q "^throughput,"; then
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
            if [[ "$mode" == "top-stake-fraction" ]]; then
                echo "committee-stake-fraction-threshold: $STAKE_FRACTION"
            fi
        } > "$override"

        params=(-p "$config" -p "$MEMORY_LIMIT" -p "$TURBO" -p "$override")

        echo -n "Running throughput=$throughput committee=$mode ... " >&2
        start=$(date +%s.%N)
        output=$( cargo run --release -- "$TOPOLOGY" "${params[@]}" -s "$SLOTS" 2>&1 | tee /dev/stderr || true )
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

        echo "$throughput,$mode,$elapsed,$total_ebs,$uncertified_ebs,$ebs_with_endorsement,$total_votes,$votes_per_eb_mean,$votes_per_eb_stddev" | tee -a "$RESULTS"
        echo "done (${elapsed}s)" >&2
    done
done

echo "" >&2
echo "Results saved to $RESULTS" >&2
