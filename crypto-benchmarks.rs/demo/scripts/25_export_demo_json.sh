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
  echo "need -d RUN_DIR" >&2
  exit 2
fi

# Resolve the run directory (handle paths with spaces)
RUN_DIR="$(cd "$DIR_SCRIPT/.." && cd "$RUN_DIR" && pwd)"
PY="${VIRTUAL_ENV:+$VIRTUAL_ENV/bin/python}"
PY="${PY:-python3}"

pushd "$RUN_DIR" >/dev/null
"$PY" - <<'PY'
import os, json, collections
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
total_stake = reg.get("total_stake")
N = int(reg.get("voters", 0) or 0)

# --- Universe (all pools from registry.info) ---
# Each entry: pool_id, stake, is_persistent
persistent_set = set(persistent_pool.values())
universe = [
    {"pool_id": pid, "stake": rec.get("stake", 0), "is_persistent": pid in persistent_set}
    for pid, rec in info.items()
]
# Sort universe by stake desc, then pool_id for stability
universe.sort(key=lambda x: (-int(x.get("stake", 0) or 0), x["pool_id"]))

# Quick lookup for stake / presence
stake_by_pid = {e["pool_id"]: int(e.get("stake", 0) or 0) for e in universe}

# --- Persistent seats (ordered by persistent id) ---
persist_entries = []
for pid_idx in sorted(persistent_pool):
    pid = persistent_pool[pid_idx]
    persist_entries.append({
        "pool_id": pid,
        "stake": stake_by_pid.get(pid, 0),
    })

# How many nonpersistent seats do we need?
np_needed = max(0, N - len(persist_entries))

# --- Non-persistent winners:
# Prefer certificate.cbor (authoritative). If absent, derive from votes.cbor.
np_winners = []
if np_needed > 0 and os.path.exists("certificate.cbor"):
    cert = cbor2.load(open("certificate.cbor", "rb"))
    # Many builds export winners under 'nonpersistent_voters' as a map {pool_id: proof/...}
    np_map = cert.get("nonpersistent_voters") or {}
    # Keep the CBOR/map iteration order (winners order). Fall back to sorted order for stability.
    if isinstance(np_map, dict):
        np_winners = list(np_map.keys())
    else:
        # Some variants serialize as list of objects
        try:
            np_winners = [x.get("pool") for x in np_map if isinstance(x, dict) and x.get("pool")]
        except Exception:
            np_winners = []
elif np_needed > 0 and os.path.exists("votes.cbor"):
    # Derive per-EB top by vote count for Nonpersistent votes
    votes = cbor2.load(open("votes.cbor", "rb"))
    ctr = collections.Counter()
    order = []  # first-appearance order (for tie-breaking)
    seen = set()
    for v in votes:
        if "Nonpersistent" in v:
            pid = v["Nonpersistent"].get("pool")
            if not isinstance(pid, str): 
                continue
            ctr[pid] += 1
            if pid not in seen:
                seen.add(pid)
                order.append(pid)
    # Rank by count desc, break ties by first appearance
    np_winners = sorted(ctr.keys(), key=lambda k: (-ctr[k], order.index(k) if k in order else 1e9))

# Deduplicate and trim to needed seats, skipping any that duplicate persistent
np_final = []
seen = set(p["pool_id"] for p in persist_entries)
for pid in np_winners:
    if not isinstance(pid, str):
        continue
    if pid in seen:
        continue
    np_final.append(pid)
    seen.add(pid)
    if len(np_final) >= np_needed:
        break

# --- Only keep NP winners that already exist in the universe (no stubs)
universe_pids = set(e["pool_id"] for e in universe)
np_final = [pid for pid in np_final if pid in universe_pids]

# Rebuild lookup maps after potential extensions
universe.sort(key=lambda x: (-int(x.get("stake", 0) or 0), x["pool_id"]))
universe_index_by_pool_id = {entry["pool_id"]: idx for idx, entry in enumerate(universe, start=1)}

# --- Build final committee list: keep committee order (position) but set
# "index" to the pool's 1-based index in the *universe* array.
committee = []
# persistent first (in persistent id order)
for pos, entry in enumerate(persist_entries, start=1):
    pid = entry["pool_id"]
    committee.append({
        "position": pos,
        "index": universe_index_by_pool_id.get(pid),  # universe index
        "pool_id": pid,
        "stake": entry["stake"],
    })
# then non-persistent winners (in certificate order or derived order)
pos = len(committee) + 1
for pid in np_final:
    committee.append({
        "position": pos,
        "index": universe_index_by_pool_id.get(pid),  # universe index
        "pool_id": pid,
        "stake": stake_by_pid.get(pid, 0),
    })
    pos += 1

# If we still don't have N seats (missing certificate/votes), fill from top-by-stake excluding already chosen
if len(committee) < N:
    chosen = set(c["pool_id"] for c in committee)
    for e in universe:
        if e["pool_id"] in chosen:
            continue
        committee.append({
            "position": len(committee) + 1,
            "index": universe_index_by_pool_id.get(e["pool_id"]),
            "pool_id": e["pool_id"],
            "stake": e.get("stake", 0),
        })
        if len(committee) >= N:
            break
    committee_source = "fa+votes+fallback"
else:
    committee_source = "fa+certificate" if os.path.exists("certificate.cbor") else ("fa+votes" if os.path.exists("votes.cbor") else "fallback_topN")

# --- Voters quick view (optional)
voters_persistent = []
voters_nonpersistent = []
if os.path.exists("votes.cbor"):
    try:
        votes = cbor2.load(open("votes.cbor", "rb"))
        for v in votes:
            if "Persistent" in v:
                pid = v["Persistent"].get("persistent")
                if isinstance(pid, int):
                    voters_persistent.append(pid)
            elif "Nonpersistent" in v:
                pool = v["Nonpersistent"].get("pool")
                if isinstance(pool, str):
                    voters_nonpersistent.append(pool)
    except Exception:
        pass

# --- Certificate summary (optional) ---
cert_summary = {}
votes_bytes = os.path.getsize("votes.cbor") if os.path.exists("votes.cbor") else None
certificate_bytes = os.path.getsize("certificate.cbor") if os.path.exists("certificate.cbor") else None

if os.path.exists("certificate.cbor"):
    cert = cbor2.load(open("certificate.cbor", "rb"))
    pv = cert.get("persistent_voters", []) or []
    npv = cert.get("nonpersistent_voters") or {}
    def hex_pref(x):
        try:
            return (x or b"")[:8].hex()
        except Exception:
            return None
    cert_summary = {
        "sigma_tilde_eid_prefix": hex_pref(cert.get("sigma_tilde_eid")),
        "sigma_tilde_m_prefix": hex_pref(cert.get("sigma_tilde_m")),
        "eid": "0x" + (cert.get("eid") or b"").hex() if cert.get("eid") is not None else None,
        "eb": "0x" + (cert.get("eb") or b"").hex() if cert.get("eb") is not None else None,
        "persistent_voters_count": len(pv) if hasattr(pv, "__len__") else None,
        "nonpersistent_voters_count": (len(npv.keys()) if isinstance(npv, dict) else (len(npv) if hasattr(npv, "__len__") else None)),
    }

if votes_bytes is not None:
    cert_summary["votes_bytes"] = votes_bytes
if certificate_bytes is not None:
    cert_summary["certificate_bytes"] = certificate_bytes
    if votes_bytes:
        try:
            cert_summary["compression_ratio"] = round(votes_bytes / certificate_bytes, 3)
        except Exception:
            pass

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
    "committee_source": committee_source,
    "lookup": {
        "universe_index_by_pool_id": universe_index_by_pool_id,
        # Back-compat: this has always meant the committee *order* (position)
        "committee_index_by_pool_id": {entry["pool_id"]: entry["position"] for entry in committee},
        # New explicit alias for clarity
        "committee_position_by_pool_id": {entry["pool_id"]: entry["position"] for entry in committee},
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