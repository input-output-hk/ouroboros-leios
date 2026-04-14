#!/usr/bin/env bash
set -euo pipefail

# Benchmark different committee selection algorithms under the CIP topology.
# Always uses turbo mode (sequential engine, sharded).
#
# Usage: SLOTS=1500 ./scripts/cip-voting-options.sh

# Configuration
SLOTS="${SLOTS:-1500}"
THROUGHPUTS=(0.150 0.200 0.250 0.300 0.350)
# committee-selection-algorithm values and corresponding vote thresholds.
# wfa-ls: CIP default (VRF lottery, ~600 expected committee, threshold 450)
# everyone: all 750 nodes vote (1 each), threshold 450 (60%)
# top-stake-fraction at 0.95: ~201 staking nodes vote, threshold 121 (60%)
MODES=("wfa-ls" "everyone" "top-stake-fraction")
declare -A VOTE_THRESHOLDS=(
    ["wfa-ls"]=450
    ["everyone"]=450
    ["top-stake-fraction"]=121
)
declare -A STAKE_FRACTIONS=(
    ["top-stake-fraction"]=0.95
)

# Paths (relative to sim-rs/)
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SIM_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
TOPOLOGY="$SIM_DIR/../data/simulation/pseudo-mainnet/topology-v2-cip.yaml"
EXPERIMENTS="$SIM_DIR/../analysis/sims/cip/experiments"
MEMORY_LIMIT="$SIM_DIR/parameters/memory-limit.yaml"
TURBO="$SIM_DIR/parameters/turbo.yaml"
RESULTS="$SIM_DIR/voting_results.csv"

cd "$SIM_DIR"

echo "Building release binary..."
cargo build --release

TMPDIR=$(mktemp -d)
trap 'rm -rf "$TMPDIR"' EXIT

echo ""
echo "throughput,committee,time_seconds,total_ebs,uncertified_ebs,ebs_with_endorsement,total_votes,votes_per_eb_mean,votes_per_eb_stddev" | tee "$RESULTS"

for throughput in "${THROUGHPUTS[@]}"; do
    config="$EXPERIMENTS/NA,$throughput/config.yaml"
    if [[ ! -f "$config" ]]; then
        echo "WARNING: $config not found, skipping" >&2
        continue
    fi

    for mode in "${MODES[@]}"; do
        # Build a mode-specific override file
        override="$TMPDIR/override-$mode.yaml"
        {
            echo "committee-selection-algorithm: \"$mode\""
            echo "vote-threshold: ${VOTE_THRESHOLDS[$mode]}"
            if [[ -n "${STAKE_FRACTIONS[$mode]:-}" ]]; then
                echo "committee-stake-fraction-threshold: ${STAKE_FRACTIONS[$mode]}"
            fi
        } > "$override"

        params=(-p "$config" -p "$MEMORY_LIMIT" -p "$TURBO" -p "$override")

        echo -n "Running throughput=$throughput committee=$mode ... " >&2
        start=$(date +%s.%N)
        output=$( cargo run --release -- "$TOPOLOGY" "${params[@]}" -s "$SLOTS" 2>&1 || true )
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
