#!/usr/bin/env bash
set -euo pipefail
DIR_SCRIPT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RUN_DIR=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    -d) RUN_DIR="$2"; shift 2;;
    *) echo "Usage: $0 -d RUN_DIR"; exit 2;;
  esac
done

if [[ -z "$RUN_DIR" ]]; then
  echo "need -d RUN_DIR"
  exit 2
fi

# ✅ Quote paths with spaces
RUN_DIR="$(cd "$DIR_SCRIPT/.." && cd "$RUN_DIR" && pwd)"
PY="${VIRTUAL_ENV:+$VIRTUAL_ENV/bin/python}"
PY="${PY:-python3}"

pushd "$RUN_DIR" >/dev/null
 "$PY" - <<'PY'
import os, json
try:
    import cbor2
except ImportError:
    raise SystemExit("cbor2 not installed (pip install cbor2)")

def must(path):
    if not os.path.exists(path):
        raise SystemExit(f"missing {path}")
    return path

# --- Load registry (required) ---
reg = cbor2.load(open(must("registry.cbor"), "rb"))
info = reg.get("info", {}) or {}
persistent_pool = reg.get("persistent_pool", {}) or {}
persistent_set = set(persistent_pool.values())
total_stake = reg.get("total_stake")
N = reg.get("voters", 0)

# --- Universe (all pools) ---
# Each entry now has: pool_id, stake, is_persistent (for easy coloring on UI)
universe = [
    {"pool_id": pid, "stake": rec.get("stake", 0), "is_persistent": pid in persistent_set}
    for pid, rec in info.items()
]
universe.sort(key=lambda x: x["stake"], reverse=True)

# --- Committee (top-N by stake, same as backend endpoint) ---
committee = [
    {"index": i + 1, "pool_id": universe[i]["pool_id"], "stake": universe[i]["stake"]}
    for i in range(min(N, len(universe)))
]

# --- Lookup maps for fast UI highlighting / tooltips ---
universe_index_by_pool_id = {entry["pool_id"]: idx for idx, entry in enumerate(universe)}
committee_index_by_pool_id = {entry["pool_id"]: entry["index"] for entry in committee}

# --- Voters (optional; present when votes.cbor exists) ---
voters_persistent = []
voters_nonpersistent = []
if os.path.exists("votes.cbor"):
    votes = cbor2.load(open("votes.cbor", "rb"))
    for v in votes:
        if "Persistent" in v:
            pid = v["Persistent"]["persistent"]
            if isinstance(pid, int):
                voters_persistent.append(pid)
        elif "Nonpersistent" in v:
            pool = v["Nonpersistent"]["pool"]
            if isinstance(pool, str):
                voters_nonpersistent.append(pool)

# --- Certificate summary (optional) ---
cert_summary = {}
votes_bytes = os.path.getsize("votes.cbor") if os.path.exists("votes.cbor") else None
certificate_bytes = os.path.getsize("certificate.cbor") if os.path.exists("certificate.cbor") else None

if os.path.exists("certificate.cbor"):
    cert = cbor2.load(open("certificate.cbor", "rb"))
    pv = cert.get("persistent_voters", []) or []
    npv = cert.get("nonpersistent_voters") or {}
    cert_summary = {
        "sigma_tilde_eid_prefix": cert["sigma_tilde_eid"][:8].hex(),
        "sigma_tilde_m_prefix": cert["sigma_tilde_m"][:8].hex(),
        "eid": "0x" + cert["eid"].hex(),
        "eb": "0x" + cert["eb"].hex(),
        "persistent_voters_count": len(pv),
        "nonpersistent_voters_count": len(npv.keys()),
    }

if votes_bytes is not None:
    cert_summary["votes_bytes"] = votes_bytes
if certificate_bytes is not None:
    cert_summary["certificate_bytes"] = certificate_bytes
    if votes_bytes:
        cert_summary["compression_ratio"] = round(votes_bytes / certificate_bytes, 3)

# --- Params (handy for the UI header) ---
params = {
    "N": N,
    "pool_count": len(universe),
    "total_stake": total_stake,
}

out = {
    "params": params,
    "universe": universe,
    "persistent_map": {int(k): v for k, v in persistent_pool.items()},
    "committee": committee,
    "lookup": {
        "universe_index_by_pool_id": universe_index_by_pool_id,
        "committee_index_by_pool_id": committee_index_by_pool_id,
    },
    "voters": {
        "persistent_ids": voters_persistent,
        "nonpersistent_pool_ids": voters_nonpersistent,
    },
    "certificate": cert_summary,
}

json.dump(out, open("demo.json", "w"), indent=2)
print("Wrote demo.json")
PY
popd >/dev/null