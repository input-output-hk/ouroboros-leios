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

# Normalize persistent seat IDs to integers for robust comparisons
try:
    persistent_seat_ids = {int(k) for k in persistent_pool.keys()}
except Exception:
    persistent_seat_ids = set()

# --- Quorum / voting fraction (optional, written by 30_cast_votes.sh as fraction.txt) ---
def read_quorum_fraction():
    for fname in ("fraction.txt", "quorum.txt", "quorum_fraction.txt"):
        path = os.path.join(os.getcwd(), fname)
        if os.path.exists(path):
            try:
                raw = open(path, "r", encoding="utf-8").read().strip()
            except Exception:
                continue
            if not raw:
                continue
            # Prefer numeric if possible, otherwise keep as string
            try:
                return float(raw)
            except ValueError:
                return raw
    return None

quorum_fraction = read_quorum_fraction()

# --- Universe (all pools from registry.info) ---
# Each entry: pool_id, stake (no persistent flag here; committee carries epoch membership)
# Preserve original generation order from registry.info (Python dict preserves insertion order).
universe = [
    {"pool_id": pid, "stake": rec.get("stake", 0)}
    for pid, rec in info.items()
]

# Quick lookup for stake / presence

# Build quick index: pool_id -> zero-based position in the universe array
universe_index_by_pool_id = {e["pool_id"]: i for i, e in enumerate(universe)}
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

# --- Non-persistent winners: (disabled for persistent-only committee export)
np_winners = []
np_final = []
np_final_set = set()

# --- Build final committee: persistent seats + placeholders for non-persistent slots
seats = []
for pos, entry in enumerate(persist_entries, start=1):
    pid = entry["pool_id"]
    seats.append({
        "position": pos,
        "index": universe_index_by_pool_id.get(pid),  # universe index
        "pool_id": pid,
        "stake": entry["stake"],
        "kind": "persistent",
    })
# Append placeholders for non-persistent slots (to be filled per‑election)
for i in range(np_needed):
    seats.append({
        "position": len(seats) + 1,
        "slot": "nonpersistent",
        "kind": "nonpersistent",
    })
committee = {
    "size": N,
    "persistent_count": len(persist_entries),
    "nonpersistent_slots": np_needed,
    "seats": seats,
}
committee_source = "persistent_plus_placeholders"

# --- Voters quick view (optional) + committee-based filtering ---
voters_unfiltered = {
    "persistent_ids": [],
    "nonpersistent_pool_ids": [],
}
voters_filtered = {
    "persistent_ids": [],
    "nonpersistent_pool_ids": [],
}
filtered_votes_raw = []
filtered_p_raw = []
filtered_np_raw = []
voters_filter_stats = {
    "source_total": 0,
    "kept_total": 0,
    "removed_outside_committee": 0,
    "removed_persistent": 0,
    "removed_nonpersistent": 0,
}

def _to_int(x):
    try:
        return int(x)
    except Exception:
        return None

def _is_persistent_id_in_committee(pid) -> bool:
    """Return True iff the persistent seat id is in the registry's persistent set."""
    pid_i = _to_int(pid)
    return (pid_i is not None) and (pid_i in persistent_seat_ids)

def _is_np_pool_in_committee(pool_id: str) -> bool:
    return isinstance(pool_id, str) and (pool_id in np_final_set)

votes_preview = []

if os.path.exists("votes.cbor"):
    try:
        votes_raw = cbor2.load(open("votes.cbor", "rb"))
        for v in votes_raw:
            # Unfiltered bookkeeping
            if "Persistent" in v:
                pid_raw = v["Persistent"].get("persistent")
                pid = _to_int(pid_raw)
                if pid is not None:
                    voters_unfiltered["persistent_ids"].append(pid)
                    votes_preview.append({"type": "persistent", "seat_id": pid})
            elif "Nonpersistent" in v:
                pool = v["Nonpersistent"].get("pool")
                if isinstance(pool, str):
                    voters_unfiltered["nonpersistent_pool_ids"].append(pool)
                    sigma_eid = v["Nonpersistent"].get("sigma_eid")
                    prefix = None
                    if isinstance(sigma_eid, (bytes, bytearray)):
                        prefix = "0x" + sigma_eid[:12].hex()
                    votes_preview.append({
                        "type": "nonpersistent",
                        "pool_id": pool,
                        "eligibility_sigma_eid_prefix": prefix,
                    })

            # Filtering (committee only)
            if "Persistent" in v:
                pid_raw = v["Persistent"].get("persistent")
                pid = _to_int(pid_raw)
                if pid is not None:
                    voters_filter_stats["source_total"] += 1
                    if _is_persistent_id_in_committee(pid):
                        voters_filtered["persistent_ids"].append(pid)
                        voters_filter_stats["kept_total"] += 1
                        filtered_votes_raw.append(v)
                        filtered_p_raw.append(v)
                    else:
                        voters_filter_stats["removed_outside_committee"] += 1
                        voters_filter_stats["removed_persistent"] += 1
            elif "Nonpersistent" in v:
                pool = v["Nonpersistent"].get("pool")
                if isinstance(pool, str):
                    voters_filter_stats["source_total"] += 1
                    if _is_np_pool_in_committee(pool):
                        voters_filtered["nonpersistent_pool_ids"].append(pool)
                        voters_filter_stats["kept_total"] += 1
                        filtered_votes_raw.append(v)
                        filtered_np_raw.append(v)
                    else:
                        voters_filter_stats["removed_outside_committee"] += 1
                        voters_filter_stats["removed_nonpersistent"] += 1
    except Exception:
        pass

# --- Compute filtered vote sizes (bytes) by CBOR re-encoding the kept votes only
votes_bytes_raw = os.path.getsize("votes.cbor") if os.path.exists("votes.cbor") else None
votes_bytes_filtered = None
votes_bytes_p_filtered = None
votes_bytes_np_filtered = None
try:
    if filtered_votes_raw:
        import cbor2 as _cbor2  # already imported, but keep local alias
        votes_bytes_filtered = len(_cbor2.dumps(filtered_votes_raw))
        if filtered_p_raw:
            votes_bytes_p_filtered = len(_cbor2.dumps(filtered_p_raw))
        if filtered_np_raw:
            votes_bytes_np_filtered = len(_cbor2.dumps(filtered_np_raw))
except Exception:
    # Fall back to raw file size if anything goes wrong
    votes_bytes_filtered = votes_bytes_raw

# --- Certificate summary (optional) ---
cert_summary = {}

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
    # Override certificate counts with committee‑filtered counts
    kept_p = len(set(voters_filtered["persistent_ids"]))
    kept_np = len(set(voters_filtered["nonpersistent_pool_ids"]))
    cert_summary["persistent_voters_count"] = kept_p
    cert_summary["nonpersistent_voters_count"] = kept_np

# --- Bytes & compression (use filtered votes only)
certificate_bytes = os.path.getsize("certificate.cbor") if os.path.exists("certificate.cbor") else None
if votes_bytes_filtered is not None:
    cert_summary["votes_bytes"] = votes_bytes_filtered
    # Keep a raw reference for diagnostics
    if votes_bytes_raw is not None:
        cert_summary["votes_bytes_raw"] = votes_bytes_raw
    if votes_bytes_p_filtered is not None:
        cert_summary["votes_bytes_persistent"] = votes_bytes_p_filtered
    if votes_bytes_np_filtered is not None:
        cert_summary["votes_bytes_nonpersistent"] = votes_bytes_np_filtered
if certificate_bytes is not None:
    cert_summary["certificate_bytes"] = certificate_bytes
if ("votes_bytes" in cert_summary) and ("certificate_bytes" in cert_summary):
    try:
        cert_summary["compression_ratio"] = round(
            cert_summary["votes_bytes"] / cert_summary["certificate_bytes"], 3
        )
    except Exception:
        pass

# --- Params (handy for the UI header) ---
params = {
    "N": N,
    "pool_count": len(universe),
    "total_stake": total_stake,
    "quorum_fraction": quorum_fraction,  # may be None if not recorded
}

out = {
    "params": params,
    "universe": universe,
    "committee": committee,
    "committee_source": committee_source,
    "lookup": {
        "universe_index_by_pool_id": universe_index_by_pool_id,
        "committee_position_by_pool_id": {
            seat["pool_id"]: seat["position"]
            for seat in committee["seats"]
            if "pool_id" in seat
        },
    },
    "voters_unfiltered": voters_unfiltered, # raw ids (persistent seat ids and NP pool ids)
    "voters_filter_stats": voters_filter_stats,
    "certificate": cert_summary,
    "votes_preview": votes_preview,
}

json.dump(out, open("demo.json", "w"), indent=2)
print("Wrote demo.json")
PY
popd >/dev/null