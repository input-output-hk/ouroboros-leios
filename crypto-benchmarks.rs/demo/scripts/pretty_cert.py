#!/usr/bin/env python3
import sys, os, json
try:
    import cbor2
except Exception as e:
    print(json.dumps({"error": f"cbor2 import failed: {e}"}, indent=2))
    sys.exit(1)

if len(sys.argv) < 2:
    print("Usage: pretty_cert.py CERT_PATH [VOTES_PATH]", file=sys.stderr)
    sys.exit(2)

cert_path = sys.argv[1]
votes_path = sys.argv[2] if len(sys.argv) > 2 else None

if not os.path.isfile(cert_path):
    print(json.dumps({"error": f"certificate not found: {cert_path}"}, indent=2))
    sys.exit(1)

def hex8(b):
    if isinstance(b, (bytes, bytearray)):
        return b[:8].hex()
    return None

def hex_full(b):
    if isinstance(b, (bytes, bytearray)):
        return "0x" + b.hex()
    return None

with open(cert_path, 'rb') as f:
    c = cbor2.load(f)

pv = c.get("persistent_voters") or c.get("persistent") or c.get("pv")
npv = c.get("nonpersistent_voters") or c.get("nonpersistent") or c.get("npv")

pv_count = len(pv) if isinstance(pv, (list, tuple)) else 0
if isinstance(npv, dict):
    npv_keys = list(npv.keys())
    npv_count = len(npv)
elif isinstance(npv, list):
    npv_keys = npv
    npv_count = len(npv)
else:
    npv_keys = []
    npv_count = 0

votes_bytes = None
if votes_path and os.path.isfile(votes_path):
    try:
        votes_bytes = os.path.getsize(votes_path)
    except OSError:
        votes_bytes = None

cert_bytes = None
try:
    cert_bytes = os.path.getsize(cert_path)
except OSError:
    cert_bytes = None

compression_ratio = None
if votes_bytes and cert_bytes and cert_bytes > 0:
    compression_ratio = round(votes_bytes / cert_bytes, 3)

out = {
    "sigma_tilde_eid_prefix": hex8(c.get("sigma_tilde_eid") or c.get("agg_sig_eid")),
    "sigma_tilde_m_prefix":   hex8(c.get("sigma_tilde_m")   or c.get("agg_sig_m")),
    "eid": hex_full(c.get("eid")),
    "eb":  hex_full(c.get("eb")),
    "persistent_voters_count": pv_count,
    "nonpersistent_voters_count": npv_count,
    "nonpersistent_voters_sample": npv_keys[:3],
}

if votes_bytes is not None:
    out["votes_bytes"] = votes_bytes
if cert_bytes is not None:
    out["certificate_bytes"] = cert_bytes
if compression_ratio is not None:
    out["compression_ratio"] = compression_ratio

print(json.dumps(out, indent=2))