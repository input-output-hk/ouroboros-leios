#!/usr/bin/env python3
# Strict, registry-first committee extraction.
# - Source of truth: registry.cbor -> .info (pool -> {stake, ...})
# - No fallbacks to stake.cbor / pools.cbor.
# - Fail fast with a clear error when registry is missing/malformed.
# - Optionally map the persistent committee from registry.{persistent_pool|persistent_id}.
# - Optionally read certificate.pretty.json to list elected voters (persistent/non-persistent).

import os, sys, json, re
from typing import Dict, Any, List, Tuple

try:
    import cbor2
except Exception as e:
    print(json.dumps({"error": f"cbor2 import failed: {e}"}))
    sys.exit(1)

# ----------------------------- args & paths -----------------------------

if len(sys.argv) < 2:
    print("Usage: extract_committee.py RUN_DIR", file=sys.stderr)
    sys.exit(2)

RUN_DIR = sys.argv[1]
REG_PATH = os.path.join(RUN_DIR, "registry.cbor")
PRETTY_PATH = os.path.join(RUN_DIR, "certificate.pretty.json")

# Accept 20..64 bytes (40..128 hex chars), with optional 0x/x prefix
HEX_RE = re.compile(r'^(?:0x|x)?[0-9a-f]{40,128}$')

# ----------------------------- helpers -----------------------------

def norm_hex_prefix(s: str) -> str:
    s = s.lower()
    if s.startswith("0x"): return s
    if s.startswith("x"):  return "0x" + s[1:]
    return "0x" + s

def normalize_pool_id(val) -> str | None:
    """Return pool id as lowercase 0x-prefixed hex string or None."""
    if isinstance(val, (bytes, bytearray)):
        return "0x" + val.hex()
    if isinstance(val, str):
        s = val.strip().lower()
        if HEX_RE.match(s):
            return norm_hex_prefix(s)
    return None

def die(out_obj: Dict[str, Any], msg: str) -> None:
    out_obj.setdefault("notes", []).append("FATAL")
    out_obj["error"] = msg
    print(json.dumps(out_obj, indent=2))
    sys.exit(1)

def load_registry(path: str, out_obj: Dict[str, Any]) -> Dict[str, Any]:
    if not os.path.isfile(path):
        die(out_obj, "registry.cbor not found; please run scripts/20_make_registry.sh first.")
    try:
        with open(path, "rb") as f:
            reg = cbor2.load(f)
    except Exception as e:
        die(out_obj, f"Failed to parse registry.cbor: {e}")
    if not isinstance(reg, dict):
        die(out_obj, "registry.cbor has unexpected shape (expected a CBOR map/dict).")
    return reg

def build_stake_map(reg: Dict[str, Any], out_obj: Dict[str, Any]) -> Dict[str, int]:
    info = reg.get("info")
    if not isinstance(info, dict) or not info:
        die(out_obj, "registry.cbor missing non-empty 'info' map; cannot derive stakes.")
    stake_map: Dict[str, int] = {}
    for pool_key, rec in info.items():
        pid = normalize_pool_id(pool_key)
        if pid is None:
            die(out_obj, f"registry.info key not a valid pool id hex: {pool_key!r}")
        if not isinstance(rec, dict):
            die(out_obj, f"registry.info entry for {pool_key} is not a dict.")
        st = rec.get("stake")
        if not isinstance(st, int):
            die(out_obj, f"registry.info entry for {pool_key} missing integer 'stake'.")
        stake_map[pid] = int(st)
    if not stake_map:
        die(out_obj, "No stakes found in registry.info; cannot build committee.")
    return stake_map

def compute_target_seats(reg: Dict[str, Any], max_available: int) -> int:
    for k in ("voters", "voter_count", "n", "N", "seats", "committee_size", "committeeSeats"):
        v = reg.get(k)
        if isinstance(v, int) and 1 <= v <= 5000:
            return min(v, max_available)
    # fallback to env or 32, clamped to available
    try:
        env_n = int(os.environ.get("DEMO_SEATS", "32"))
        if 1 <= env_n <= 5000:
            return min(env_n, max_available)
    except Exception:
        pass
    return min(32, max_available)

def persistent_committee_from_registry(reg: Dict[str, Any],
                                       stake_map: Dict[str, int],
                                       out_obj: Dict[str, Any]) -> List[Dict[str, Any]]:
    result: List[Dict[str, Any]] = []
    pp = reg.get("persistent_pool")
    if isinstance(pp, dict) and pp:
        # Keys are indices (usually 0..n-1). Sort by numeric index if possible.
        try:
            items = sorted(pp.items(), key=lambda kv: int(kv[0]))
        except Exception:
            items = sorted(pp.items(), key=lambda kv: str(kv[0]))
        for idx, pool_val in items:
            pid_hex = normalize_pool_id(pool_val)
            if pid_hex:
                result.append({"id": int(idx), "pool_id": pid_hex, "stake": stake_map.get(pid_hex)})
        if result:
            out_obj.setdefault("notes", []).append("Persistent committee mapped from registry.cbor persistent_pool")
        else:
            out_obj.setdefault("notes", []).append("registry.persistent_pool present but contained no valid pool ids")
        return result

    # Fallback: invert persistent_id (pool -> index)
    pid_map = reg.get("persistent_id")
    if isinstance(pid_map, dict) and pid_map:
        inv: Dict[int, str] = {}
        for pool_val, id_val in pid_map.items():
            pid_hex = normalize_pool_id(pool_val)
            try:
                idx = int(id_val)
            except Exception:
                continue
            if pid_hex is not None:
                inv[idx] = pid_hex
        if inv:
            for idx, pid_hex in sorted(inv.items(), key=lambda kv: kv[0]):
                result.append({"id": int(idx), "pool_id": pid_hex, "stake": stake_map.get(pid_hex)})
            out_obj.setdefault("notes", []).append("Persistent committee inferred by inverting registry.cbor persistent_id")
            return result

    out_obj.setdefault("notes", []).append(
        "registry.cbor present but has no persistent_pool/persistent_id mappings; persistent committee unavailable"
    )
    return result

def elected_from_pretty(path: str, out_obj: Dict[str, Any]) -> List[Dict[str, Any]]:
    if not os.path.isfile(path):
        return []
    try:
        with open(path) as f:
            c = json.load(f)
    except Exception as e:
        out_obj.setdefault("notes", []).append(f"Failed to read certificate.pretty.json: {e}")
        return []
    pv = c.get("persistent_voters") or c.get("persistent_voters_sample") or []
    npv = c.get("nonpersistent_voters") or c.get("nonpersistent_voters_sample") or []
    elected: List[Dict[str, Any]] = (
        [{"voter_id": v, "type": "persistent"} for v in pv] +
        [{"voter_id": v, "type": "non-persistent"} for v in npv]
    )
    if not (c.get("persistent_voters") or c.get("persistent_voters_sample")) and (c.get("nonpersistent_voters") or c.get("nonpersistent_voters_sample")):
        out_obj.setdefault("notes", []).append("All voters are non-persistent in this run; non-persistent voter IDs are ephemeral and do not equal pool IDs.")
    return elected

# ----------------------------- main -----------------------------

def main() -> None:
    out: Dict[str, Any] = {
        "selected_pools": [],   # [{index, pool_id, stake}]
        "elected": [],          # [{voter_id, type}]
        "selected_count": 0,
        "elected_count": 0,
        "persistent_committee": [],
        "persistent_count": 0,
        "notes": []
    }

    # Load registry once
    registry = load_registry(REG_PATH, out)

    # Build stakes from registry.info
    stake_map = build_stake_map(registry, out)

    # Selection (top-N by stake, stable tiebreaker by pool id)
    target = compute_target_seats(registry, max_available=len(stake_map))
    ordered: List[Tuple[str, int]] = sorted(stake_map.items(), key=lambda kv: (-kv[1], kv[0]))
    selected_ids = [pid for pid, _ in ordered[:target]]

    for i, pid_hex in enumerate(selected_ids, 1):
        out["selected_pools"].append({"index": i, "pool_id": pid_hex, "stake": stake_map.get(pid_hex)})
    out["selected_count"] = len(out["selected_pools"])
    out["notes"].append("selected_pools derived strictly from registry.cbor info (top-N by stake)")

    # Persistent committee mapping (from the same registry)
    out["persistent_committee"] = persistent_committee_from_registry(registry, stake_map, out)
    out["persistent_count"] = len(out["persistent_committee"])

    # Elected voters (optional, from pretty JSON)
    out["elected"] = elected_from_pretty(PRETTY_PATH, out)
    out["elected_count"] = len(out["elected"])

    print(json.dumps(out, indent=2))

if __name__ == "__main__":
    main()