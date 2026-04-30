#!/usr/bin/env bash
# Run the 0.200/wfa-ls single-shard sequential benchmark 3 times in sequence
# to verify that the connection.rs bandwidth-queue determinism fix restored
# bit-identical output across runs.
#
# Logs each run to /tmp/det-run-<N>.log and writes a marker to
# /tmp/det-run-state so determinism-check.sh can report progress.

set -uo pipefail

STATE=/tmp/det-run-state
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SIM_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
RESULTS="$SIM_DIR/voting_results.csv"

# Capture the line count of voting_results.csv before we start so the check
# script can report only rows produced by this batch.
start_lines=0
[[ -f "$RESULTS" ]] && start_lines=$(wc -l < "$RESULTS")

echo "start_lines=$start_lines" > "$STATE"
echo "status=starting" >> "$STATE"
echo "started_at=$(date -Iseconds)" >> "$STATE"

for i in 1 2 3; do
    log="/tmp/det-run-$i.log"
    {
        echo "run=$i"
        echo "status=running"
        echo "current_log=$log"
        echo "started_at=$(date -Iseconds)"
        echo "start_lines=$start_lines"
    } > "$STATE"

    cd "$SIM_DIR"
    ./scripts/cip-voting-options.sh \
        -e sequential \
        -T 0.200 \
        -m wfa-ls \
        > "$log" 2>&1
    rc=$?

    {
        echo "run=$i"
        echo "status=$( [[ $rc -eq 0 ]] && echo run_$i_ok || echo run_${i}_failed_rc_$rc )"
        echo "current_log=$log"
        echo "finished_at=$(date -Iseconds)"
        echo "start_lines=$start_lines"
    } > "$STATE"

    if [[ $rc -ne 0 ]]; then
        echo "status=failed_at_run_$i" > "$STATE"
        exit "$rc"
    fi
done

{
    echo "status=complete"
    echo "finished_at=$(date -Iseconds)"
    echo "start_lines=$start_lines"
} > "$STATE"
