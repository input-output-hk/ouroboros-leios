

#!/usr/bin/env bash
set -euo pipefail
# Usage: demo/scripts/30_cast_votes.sh -d RUN_DIR -f FRACTION
# Example (from demo/): scripts/30_cast_votes.sh -d run16 -f 1.0
# Requires: demo/scripts/.env_cli (set via 00_set_cli.sh)

DIR_SCRIPT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$DIR_SCRIPT/.env_cli"

RUN_DIR=""
FRACTION=""

# ---- arg parsing ----
while [[ $# -gt 0 ]]; do
  case "$1" in
    -d) RUN_DIR="$2"; shift 2;;
    -f) FRACTION="$2"; shift 2;;
    *) echo "Usage: $0 -d RUN_DIR -f FRACTION"; exit 2;;
  esac
done

if [[ -z "$RUN_DIR" || -z "$FRACTION" ]]; then
  echo "Error: need -d RUN_DIR and -f FRACTION" >&2
  exit 2
fi

# Resolve run directory relative to demo/
RUN_DIR="$(cd "$DIR_SCRIPT/.."; cd "$RUN_DIR" && pwd)"
echo "== [30_cast_votes] DIR=${RUN_DIR} FRACTION=${FRACTION} =="
# Persist the voting fraction (quorum) for downstream scripts
printf '%s\n' "$FRACTION" > "${RUN_DIR}/fraction.txt"

# ---- run cast-votes ----
pushd "$RUN_DIR" >/dev/null

if [[ ! -f "registry.cbor" ]]; then
  echo "Error: ${RUN_DIR}/registry.cbor not found. Run scripts/20_make_registry.sh first." >&2
  exit 1
fi
if [[ ! -f "eid.txt" || ! -f "ebhash.txt" ]]; then
  echo "Error: eid.txt or ebhash.txt missing in ${RUN_DIR}. Run scripts/10_init_inputs.sh first." >&2
  exit 1
fi

OUT="$("$CLI" --verbose cast-votes \
  --registry-file registry.cbor \
  --eid "$(cat eid.txt)" \
  --eb-hash "$(cat ebhash.txt)" \
  --fraction-voting "$FRACTION" \
  --votes-file votes.cbor 2>&1)"

echo "$OUT"

# Extract and stash the "Voters: X" count (robust against spacing/CR/ANSI)
CLEAN_OUT="$(printf '%s\n' "$OUT" | tr -d '\r' | sed 's/\x1B\[[0-9;]*[A-Za-z]//g')"
if [[ "$CLEAN_OUT" =~ [Vv]oters:[[:space:]]*([0-9]+) ]]; then
  VOTERS="${BASH_REMATCH[1]}"
else
  VOTERS="$(printf '%s\n' "$CLEAN_OUT" | sed -n 's/.*[Vv]oters:[[:space:]]*\([0-9][0-9]*\).*/\1/p' | head -n1 || true)"
fi

# Summarize results for the audience

# File size (bytes)
if [[ -f "${RUN_DIR}/votes.cbor" ]]; then
  BYTES=$(wc -c < "${RUN_DIR}/votes.cbor" | tr -d ' ')
  echo "votes.cbor size: ${BYTES} bytes"
fi

# Show a small sample of who voted
PYTHON_EXEC="${VIRTUAL_ENV:+$VIRTUAL_ENV/bin/python}"
PYTHON_EXEC="${PYTHON_EXEC:-python3}"
"$PYTHON_EXEC" - <<'PY'
import sys, os
try:
    import cbor2
except ImportError:
    print("CBOR summary skipped (cbor2 not installed). Run: pip install cbor2", file=sys.stderr)
    raise SystemExit(0)

votes_path = "votes.cbor"
registry_path = "registry.cbor"
if not os.path.exists(votes_path):
    print("CBOR summary skipped (votes.cbor missing).", file=sys.stderr)
    raise SystemExit(0)

# Load votes
votes = cbor2.load(open(votes_path, "rb"))
# Try to load registry to resolve persistent IDs to pool hashes
persistent_pool = {}
if os.path.exists(registry_path):
    reg = cbor2.load(open(registry_path, "rb"))
    pp = reg.get("persistent_pool")
    if isinstance(pp, dict):
        # keys could be ints or stringified ints
        persistent_pool = {int(k): v for k, v in pp.items()}
    elif isinstance(pp, list):
        # Some builds might use list index mapping
        persistent_pool = {i: v for i, v in enumerate(pp)}

np_pools = []
p_pools = []  # as 'id -> pool'

for v in votes:
    if isinstance(v, dict):
        if "Nonpersistent" in v:
            pool = v["Nonpersistent"].get("pool")
            if isinstance(pool, str):
                np_pools.append(pool)
        elif "Persistent" in v:
            pid = v["Persistent"].get("persistent")
            if isinstance(pid, int):
                pool = persistent_pool.get(pid, None)
                if pool is not None:
                    p_pools.append((pid, pool))
                else:
                    p_pools.append((pid, "<unknown>"))
    if len(np_pools) >= 3 and len(p_pools) >= 3:
        break

print("Sample voters:")
if p_pools:
    print("  Persistent (first up to 3):")
    for pid, pool in p_pools[:3]:
        print(f"    id={pid} -> pool={pool}")
if np_pools:
    print("  Nonpersistent pools (first up to 3):")
    for pool in np_pools[:3]:
        print(f"    {pool}")
PY

popd >/dev/null
