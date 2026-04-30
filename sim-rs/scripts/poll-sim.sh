#!/usr/bin/env bash
# Print a concise status line for a currently-running sim-cli invocation.
# Takes a log-file path; if omitted, picks the most recently modified
# /tmp/sim-*.log (matching the per-seed logs written by cip-voting-options.sh).
#
# Intended for use from /loop so we don't block Claude's thread on sleep.

set -uo pipefail

if [[ $# -ge 1 ]]; then
    LOG="$1"
else
    LOG=$(ls -t /tmp/sim-*.log 2>/dev/null | head -1)
    if [[ -z "$LOG" ]]; then
        echo "No log given and no /tmp/sim-*.log found."
        exit 1
    fi
fi
echo "Log: $LOG"

if ! ps -ef | grep -v grep | grep -q 'target/release/sim-cli'; then
    echo "sim-cli not running."
    echo
    echo "=== tail of $LOG ==="
    tail -20 "$LOG" 2>/dev/null || echo "(log missing)"
    exit 0
fi

# Progress: latest 'Slot N has begun' line
latest_slot=$(grep -oE 'Slot [0-9]+ has begun' "$LOG" 2>/dev/null | tail -1)
echo "Running: $latest_slot"

# CPU time + RSS so far. ps prints RSS in KiB; reformat to MiB for readability.
proc=$(ps -o pid,etime,time,pcpu,rss,comm -p "$(pgrep -f 'target/release/sim-cli' | head -1)" 2>/dev/null | tail -1)
if [[ -n "$proc" ]]; then
    echo "$proc" | awk '{
      printf "Process: pid=%s elapsed=%s cpu_time=%s pcpu=%s%% rss=%.0fMiB (%s)\n",
             $1, $2, $3, $4, $5/1024, $6
    }'
else
    echo "Process: (not found)"
fi

# Any interesting events — EB gen, vote summary preview — in the last 30 lines
echo
echo "=== recent log ==="
tail -8 "$LOG"
