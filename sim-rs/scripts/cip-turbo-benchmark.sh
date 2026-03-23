#!/usr/bin/env bash
set -euo pipefail

# Configuration
SLOTS="${SLOTS:-1500}"
THROUGHPUTS=(0.150 0.200 0.250 0.300 0.350)

# Paths (relative to sim-rs/)
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SIM_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
TOPOLOGY="$SIM_DIR/../data/simulation/pseudo-mainnet/topology-v2-cip.yaml"
EXPERIMENTS="$SIM_DIR/../analysis/sims/cip/experiments"
MEMORY_LIMIT="$SIM_DIR/parameters/memory-limit.yaml"
TURBO="$SIM_DIR/parameters/turbo.yaml"
RESULTS="$SIM_DIR/bench_results.csv"

cd "$SIM_DIR"

echo "Building release binary..."
cargo build --release

echo ""
echo "throughput,mode,time_seconds" | tee "$RESULTS"

for throughput in "${THROUGHPUTS[@]}"; do
    config="$EXPERIMENTS/NA,$throughput/config.yaml"
    if [[ ! -f "$config" ]]; then
        echo "WARNING: $config not found, skipping" >&2
        continue
    fi

    for mode in default turbo; do
        params=(-p "$config" -p "$MEMORY_LIMIT")
        if [[ "$mode" == "turbo" ]]; then
            params+=(-p "$TURBO")
        fi

        echo -n "Running throughput=$throughput mode=$mode ... " >&2
        start=$(date +%s.%N)
        # Tolerate exit code 101 (tokio JoinHandle panic during cleanup)
        cargo run --release -- "$TOPOLOGY" "${params[@]}" -s "$SLOTS" > /dev/null 2>&1 || true
        end=$(date +%s.%N)
        elapsed=$(echo "$end - $start" | bc)

        echo "$throughput,$mode,$elapsed" | tee -a "$RESULTS"
        echo "done (${elapsed}s)" >&2
    done
done

echo "" >&2
echo "Results saved to $RESULTS" >&2
