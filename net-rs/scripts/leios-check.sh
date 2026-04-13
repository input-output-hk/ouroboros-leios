#!/usr/bin/env bash
# Leios cluster diagnostics: status + EB/vote/quorum activity.
# Usage: scripts/leios-check.sh [aggregator_port]

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LOGS_DIR="$(cd "$SCRIPT_DIR/.." && pwd)/logs"
EVENTS="$(cd "$SCRIPT_DIR/.." && pwd)/cluster-events.jsonl"

# Cluster status
bash "$SCRIPT_DIR/cluster-status.sh" "$@"

echo
echo "=== Event counts ==="
if [ -f "$EVENTS" ]; then
    python3 -c "
import sys, json
counts = {}
for line in open('$EVENTS'):
    try:
        t = json.loads(line)['message']['type']
        counts[t] = counts.get(t, 0) + 1
    except: pass
for k, v in sorted(counts.items(), key=lambda x: -x[1]):
    print(f'  {v:6d}  {k}')
" 2>/dev/null
else
    echo "  (no cluster-events.jsonl)"
fi

echo
echo "=== Leios activity (across all nodes) ==="
for pattern in "eb election created" "vote produced" "quorum reached"; do
    total=0
    for log in "$LOGS_DIR"/node-*.log; do
        [ -f "$log" ] || continue
        c=$(grep -c "$pattern" "$log" 2>/dev/null || true)
        total=$((total + c))
    done
    printf "  %-25s %d\n" "$pattern" "$total"
done

echo
echo "=== Sample quorum events ==="
grep "quorum reached" "$LOGS_DIR"/node-0.log 2>/dev/null | head -5 || echo "  (none on node-0)"
