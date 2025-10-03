#!/usr/bin/env python3
import sys, os, json, argparse

try:
    import cbor2
except Exception as e:
    print(json.dumps({"error": f"cbor2 import failed: {e}"},
                     indent=2))
    sys.exit(1)

def hex8(b):
    if isinstance(b, (bytes, bytearray)):
        return b[:8].hex()
    return None

def hex_full(b):
    if isinstance(b, (bytes, bytearray)):
        return "0x" + b.hex()
    return None

def load_cbor(path):
    with open(path, 'rb') as f:
        return cbor2.load(f)

def main():
    ap = argparse.ArgumentParser(
        description="Pretty print certificate (and optional votes) as JSON")
    ap.add_argument("certificate", help="Path to certificate.cbor")
    ap.add_argument("votes", nargs="?", default=None,
                    help="Optional path to votes.cbor")
    ap.add_argument("--all-voters", action="store_true",
                    help="Include full lists of persistent and non-persistent voters")
    ap.add_argument("--max-ids", type=int, default=5,
                    help="When not using --all-voters, include at most N voter IDs (default 5)")
    args = ap.parse_args()

    cert_path = args.certificate
    votes_path = args.votes

    if not os.path.isfile(cert_path):
        print(json.dumps({"error": f"certificate not found: {cert_path}"}, indent=2))
        sys.exit(1)

    c = load_cbor(cert_path)

    # Handle schema variants
    pv = c.get("persistent_voters") or c.get("persistent") or c.get("pv")
    npv = c.get("nonpersistent_voters") or c.get("nonpersistent") or c.get("npv")

    # Normalize PV list
    if isinstance(pv, (list, tuple)):
        pv_list = list(pv)
    elif isinstance(pv, dict):
        # (unlikely) but normalize to keys
        pv_list = list(pv.keys())
    else:
        pv_list = []

    # Normalize NPV list (keys, since values are sigs)
    if isinstance(npv, dict):
        npv_list = list(npv.keys())
    elif isinstance(npv, (list, tuple)):
        npv_list = list(npv)
    else:
        npv_list = []

    pv_count  = len(pv_list)
    npv_count = len(npv_list)

    # Sizes for compression ratio
    votes_bytes = os.path.getsize(votes_path) if (votes_path and os.path.isfile(votes_path)) else None
    cert_bytes  = os.path.getsize(cert_path)
    compression_ratio = None
    if votes_bytes and cert_bytes > 0:
        compression_ratio = round(votes_bytes / cert_bytes, 3)

    out = {
        "sigma_tilde_eid_prefix": hex8(c.get("sigma_tilde_eid") or c.get("agg_sig_eid")),
        "sigma_tilde_m_prefix":   hex8(c.get("sigma_tilde_m")   or c.get("agg_sig_m")),
        "eid": hex_full(c.get("eid")),
        "eb":  hex_full(c.get("eb")),
        "persistent_voters_count": pv_count,
        "nonpersistent_voters_count": npv_count,
    }

    # Samples vs full lists
    if args.all_voters:
        out["persistent_voters"] = pv_list
        out["nonpersistent_voters"] = npv_list
    else:
        k = max(0, args.max_ids)
        if k > 0:
            # Include a sample of both lists (consistent ordering shown by tool)
            out["persistent_voters_sample"] = pv_list[:k]
            out["nonpersistent_voters_sample"] = npv_list[:k]

    if votes_bytes is not None:
        out["votes_bytes"] = votes_bytes
    if cert_bytes is not None:
        out["certificate_bytes"] = cert_bytes
    if compression_ratio is not None:
        out["compression_ratio"] = compression_ratio

    print(json.dumps(out, indent=2))

if __name__ == "__main__":
    main()