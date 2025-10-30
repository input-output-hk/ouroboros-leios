

#!/usr/bin/env bash
set -euo pipefail
# Usage: demo/scripts/20_make_registry.sh -d RUN_DIR -n N
# Example (from demo/): scripts/20_make_registry.sh -d run16 -n 16
DIR_SCRIPT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$DIR_SCRIPT/.env_cli"

RUN_DIR=""
N=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    -d) RUN_DIR="$2"; shift 2;;
    -n) N="$2"; shift 2;;
    *) echo "Usage: $0 -d RUN_DIR -n N"; exit 2;;
  esac
done

if [[ -z "$RUN_DIR" || -z "$N" ]]; then
  echo "Error: need -d RUN_DIR and -n N" >&2; exit 2
fi

RUN_DIR="$(cd "$DIR_SCRIPT/.."; cd "$RUN_DIR" && pwd)"
echo "== [20_make_registry] DIR=${RUN_DIR} N=${N} =="

pushd "$RUN_DIR" >/dev/null
"$CLI" make-registry \
  --pools-file pools.cbor \
  --voter-count "$N" \
  --registry-file registry.cbor
popd >/dev/null

# --- Pretty-print a short registry summary for the audience ---
PYTHON_EXEC="${VIRTUAL_ENV:+$VIRTUAL_ENV/bin/python}"
PYTHON_EXEC="${PYTHON_EXEC:-python3}"
pushd "$RUN_DIR" >/dev/null
"$PYTHON_EXEC" - <<'PY'
import sys, os
try:
    import cbor2
except ImportError:
    print("CBOR summary skipped (cbor2 not installed). Run: pip install cbor2", file=sys.stderr)
    raise SystemExit(0)

path = "registry.cbor"
if not os.path.exists(path):
    print("CBOR summary skipped (registry.cbor missing).", file=sys.stderr)
    raise SystemExit(0)

c = cbor2.load(open(path, "rb"))

voters = c.get("voters")
total_stake = c.get("total_stake")
persistent_pool = c.get("persistent_pool") or {}
info = c.get("info") or {}

print("Registry summary:")
print(f"  Seats requested (N): {voters}")
print(f"  Persistent seats:    {len(persistent_pool)}")
print(f"  Total stake:         {total_stake}")

# Top 3 stakepools by stake (from .info)
tops = []
for pool_id, rec in info.items():
    stake = rec.get("stake")
    if isinstance(stake, int):
        tops.append((stake, pool_id))
tops.sort(reverse=True)
tops = tops[:3]

if tops:
    print("  Top 3 stakepools by stake:")
    for i, (stake, pool) in enumerate(tops, 1):
        print(f"    {i}. pool={pool}  stake={stake}")

# Show up to first 3 persistent IDs → pools
if isinstance(persistent_pool, dict) and persistent_pool:
    items = sorted(persistent_pool.items(), key=lambda kv: kv[0])[:3]
    print("  Persistent mapping (first 3):")
    for pid, pool in items:
        print(f"    id={pid} -> pool={pool}")
PY
popd >/dev/null
# --- End summary ---