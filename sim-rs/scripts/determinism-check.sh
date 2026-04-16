#!/usr/bin/env bash
# Print progress of the 3-run determinism benchmark started by
# determinism-run.sh. Idempotent and fast — safe to call repeatedly from /loop.

set -uo pipefail

STATE=/tmp/det-run-state
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SIM_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
RESULTS="$SIM_DIR/voting_results.csv"

if [[ ! -f "$STATE" ]]; then
    echo "No determinism run in progress (no $STATE)."
    exit 0
fi

echo "=== state ==="
cat "$STATE"
echo

# Show rows this batch has produced — any row with engine=sequential is ours,
# since prior benchmark runs in this file are all turbo/actor.
if [[ -f "$RESULTS" ]]; then
    batch=$(grep ',sequential,' "$RESULTS" || true)
    n_rows=$(echo -n "$batch" | grep -c '^' || true)
    echo "=== voting_results.csv: $n_rows sequential row(s) ==="
    head -1 "$RESULTS"
    echo "$batch"
    echo

    if [[ $n_rows -ge 3 ]]; then
        echo "=== determinism check ==="
        # Columns: throughput,committee,engine,time_seconds,total_ebs,uncertified_ebs,ebs_with_endorsement,total_votes,votes_per_eb_mean,votes_per_eb_stddev
        # Strip time_seconds (column 4) and compare the rest.
        canon=$(echo "$batch" | head -3 | awk -F, 'BEGIN{OFS=","} { $4=""; print }' | sort -u)
        n_unique=$(echo "$canon" | wc -l)
        if [[ $n_unique -eq 1 ]]; then
            echo "DETERMINISTIC: all 3 runs produced identical stats (time ignored)"
        else
            echo "NON-DETERMINISTIC: $n_unique distinct stat-lines across 3 runs"
            echo "$canon"
        fi
    fi
fi

# Show current log tail
current_log=$(grep '^current_log=' "$STATE" | tail -1 | cut -d= -f2)
if [[ -n "${current_log:-}" && -f "$current_log" ]]; then
    echo "=== tail of $current_log ==="
    tail -5 "$current_log"
fi
