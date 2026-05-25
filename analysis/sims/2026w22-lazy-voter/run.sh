#!/usr/bin/env bash
# Sequential runner for the 2026w22 lazy-voter test:
#  1) shared-consensus baseline (no behaviours)
#  2) shared-consensus + 20%-stake lazy-voter
# Both at NA,0.200, top-stake-fraction, seed 0, 1500 slots.

set -eo pipefail

BASE_DIR="/home/prc/leios/analysis/sims/2026w22-lazy-voter/NA,0.200/top-stake-fraction/topology-v2/seed-0"
SIM_CLI="/home/prc/leios/sim-rs/target/release/sim-cli"
NETWORK="$BASE_DIR/network.yaml"
SLOTS=1500

cd "$BASE_DIR"

ulimit -S -v 256000000  # 256 GB virtual cap

for variant in baseline-shared-consensus lazy-voter-20pct; do
  OUTDIR="$BASE_DIR/$variant"
  [[ -e "$OUTDIR/done" ]] && { echo "skipping $variant (already done)"; continue; }
  echo "==[ $(date +%H:%M:%S) ] starting $variant"
  /usr/bin/time -v -o "$OUTDIR/time.txt" "$SIM_CLI" "$NETWORK" \
    -p "$OUTDIR/config.yaml" --slots "$SLOTS" \
    > "$OUTDIR/stdout" 2> "$OUTDIR/stderr"
  grep -E "^ INFO (praos|leios|network): " "$OUTDIR/stdout" > "$OUTDIR/summary.txt" || true
  touch "$OUTDIR/done"
  echo "==[ $(date +%H:%M:%S) ] finished $variant"
done

echo "==[ $(date +%H:%M:%S) ] all runs complete"
