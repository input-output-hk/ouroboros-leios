#!/usr/bin/env python3
"""Fetch mainnet block headers for whole epochs from Koios (public, keyless)
into ../mainnet/blocks_<epoch>.jsonl, one JSON object per block:
block_height, block_time (unix), epoch_no, epoch_slot, block_size (bytes),
tx_count, pool. Also fetches the epoch's protocol parameters into
../mainnet/params_<epoch>.json (max_block_size, max_tx_size, execution
budgets), which the measurement uses as the ceiling of that epoch.

    python3 mainnet_blocks.py 660 661 316 304

Paged 1000 blocks per call, 0.7 s between calls; stops on the first error
response instead of paging over it. Existing files are kept unless --force.
"""
import json
import os
import sys
import time
import urllib.parse
import urllib.request

K = "https://api.koios.rest/api/v1"
HERE = os.path.dirname(os.path.abspath(__file__))
# the data folder: $LEIOS_MAINNET if set (the report repository's copy sets it), else ../mainnet next to this file
OUT = os.environ.get("LEIOS_MAINNET") or os.path.join(HERE, "..", "mainnet")
UA = "leios-analysis/0.1"


def get(url, tries=3):
    for i in range(tries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": "application/json"})
            with urllib.request.urlopen(req, timeout=90) as r:
                return json.load(r)
        except Exception as e:  # noqa: BLE001
            if i == tries - 1:
                raise
            print(f"  retry after error: {e}", file=sys.stderr)
            time.sleep(5 * (i + 1))


def fetch_epoch(epoch, force=False):
    os.makedirs(OUT, exist_ok=True)
    pf = os.path.join(OUT, f"params_{epoch}.json")
    if force or not os.path.exists(pf):
        p = get(f"{K}/epoch_params?_epoch_no={epoch}")
        if not isinstance(p, list) or not p:
            sys.exit(f"epoch_params {epoch}: unexpected response {str(p)[:200]}")
        json.dump(p[0], open(pf, "w"))
        time.sleep(0.7)
    bf = os.path.join(OUT, f"blocks_{epoch}.jsonl")
    if os.path.exists(bf) and not force:
        print(f"epoch {epoch}: {bf} exists, skipped")
        return
    rows, off = [], 0
    while True:
        q = urllib.parse.urlencode({"epoch_no": f"eq.{epoch}", "select": "block_height,block_time,epoch_no,epoch_slot,block_size,tx_count,pool",
                                    "order": "block_height.asc", "limit": 1000, "offset": off})
        r = get(f"{K}/blocks?{q}")
        if not isinstance(r, list):
            sys.exit(f"blocks {epoch} offset {off}: unexpected response {str(r)[:200]}")
        rows += r
        print(f"  epoch {epoch}: {len(rows)} blocks", file=sys.stderr)
        if len(r) < 1000:
            break
        off += 1000
        time.sleep(0.7)
    with open(bf, "w") as f:
        for x in rows:
            f.write(json.dumps(x) + "\n")
    print(f"epoch {epoch}: {len(rows)} blocks -> {bf}")


if __name__ == "__main__":
    force = "--force" in sys.argv
    for e in [a for a in sys.argv[1:] if not a.startswith("--")]:
        fetch_epoch(int(e), force)
