#!/usr/bin/env python3
"""Praos block fullness and throughput on mainnet over epochs fetched by
mainnet_blocks.py (../mainnet/blocks_<epoch>.jsonl, params_<epoch>.json).

    python3 mainnet_praos.py 660 661 --bin 3600 --top 5
    python3 mainnet_praos.py 316 --from 2022-01-20T00:00:00 --to 2022-01-22T00:00:00

For each epoch and for the chosen window: RB count and spacing, block
size percentiles, fullness against that epoch's max_block_size (the
limit changed over the chain's history: 65,536 B to epoch 315, 73,728
from 316, 81,920 from about 330, 90,112 from 335), bytes per second
against the Praos expectation max_block_size x f (f = 0.05), transactions
per block and the mean transaction size (block bytes over transactions,
so it includes the block header's share). --bin groups the blocks into
bins of that many seconds and lists the --top fullest bins, to locate the
congested windows. kB = 1000 bytes.
"""
import argparse
import datetime as dt
import json
import os
import statistics

HERE = os.path.dirname(os.path.abspath(__file__))
# the data folder: $LEIOS_MAINNET if set (the report repository's copy sets it), else ../mainnet next to this file
DATA = os.environ.get("LEIOS_MAINNET") or os.path.join(HERE, "..", "mainnet")
F = 0.05


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("epochs", nargs="+", type=int)
    ap.add_argument("--from", dest="from_", help="UTC start of the window, YYYY-MM-DDTHH:MM:SS")
    ap.add_argument("--to", help="UTC end of the window (exclusive)")
    ap.add_argument("--bin", type=int, default=3600, help="bin width in seconds for the fullest-bins list (default 3600)")
    ap.add_argument("--top", type=int, default=5, help="how many fullest bins to list (default 5)")
    ap.add_argument("--full", type=float, default=0.95, help="a block is 'full' at this share of max_block_size (default 0.95)")
    a = ap.parse_args()

    blocks, caps = [], {}
    for e in a.epochs:
        p = json.load(open(os.path.join(DATA, f"params_{e}.json")))
        caps[e] = int(p["max_block_size"])
        for line in open(os.path.join(DATA, f"blocks_{e}.jsonl")):
            b = json.loads(line)
            b["cap"] = caps[e]
            blocks.append(b)
    blocks.sort(key=lambda b: b["block_height"])
    t0 = ts(a.from_) if a.from_ else None
    t1 = ts(a.to) if a.to else None
    sel = [b for b in blocks if (t0 is None or b["block_time"] >= t0) and (t1 is None or b["block_time"] < t1)]
    if not sel:
        raise SystemExit("no blocks in the window")

    print(f"epochs {a.epochs}, max_block_size " + ", ".join(f"{e}: {c:,} B" for e, c in caps.items())
          + f"; window {fmt(sel[0]['block_time'])} to {fmt(sel[-1]['block_time'])} UTC"
          + (" (whole epochs)" if t0 is None and t1 is None else ""))
    print()
    report(sel, a.full)
    print()
    bins = {}
    for b in sel:
        k = b["block_time"] // a.bin * a.bin
        bins.setdefault(k, []).append(b)
    rows = []
    for k, bs in bins.items():
        rows.append((sum(x["block_size"] for x in bs) / sum(x["cap"] for x in bs), k, bs))
    rows.sort(reverse=True)
    print(f"Fullest {a.top} bins of {a.bin} s (bytes carried over the cap of every RB in the bin):")
    print()
    print("| bin start (UTC) | RBs | mean fullness | RBs ≥ full | kB/s | expected kB/s |")
    print("|---|---|---|---|---|---|")
    for frac, k, bs in rows[:a.top]:
        full = sum(1 for x in bs if x["block_size"] >= a.full * x["cap"])
        kbs = sum(x["block_size"] for x in bs) / a.bin / 1000
        exp = statistics.mean(x["cap"] for x in bs) * F / 1000
        print(f"| {fmt(k)} | {len(bs)} | {100*frac:.0f}% | {full} ({100*full/len(bs):.0f}%) | {kbs:.2f} | {exp:.2f} |")


def report(sel, full):
    n = len(sel)
    span = sel[-1]["block_time"] - sel[0]["block_time"]
    sizes = sorted(b["block_size"] for b in sel)
    fr = sorted(b["block_size"] / b["cap"] for b in sel)
    txs = sum(b["tx_count"] for b in sel)
    q = lambda v, p: v[min(int(p * (len(v) - 1)), len(v) - 1)]
    cap = statistics.mean(b["cap"] for b in sel)
    print("| measure | value |")
    print("|---|---|")
    spacing = span / max(n - 1, 1)
    density = (n - 1) / span / F  # observed RBs per slot over the expected f: 1 = no slot lost
    print(f"| RBs | {n:,} over {span/3600:.1f} h, one every {spacing:.1f} s (expected {1/F:.0f} s); chain density {100*density:.1f}% of f |")
    print(f"| ceiling at 20 s spacing, cap x f | {cap*F/1000:.2f} kB/s |")
    print(f"| cap with measured chain density, cap / measured spacing | {cap/spacing/1000:.2f} kB/s |")
    print(f"| RB size p10 / p50 / p90 / max | {q(sizes,.1)/1000:.1f} / {q(sizes,.5)/1000:.1f} / {q(sizes,.9)/1000:.1f} / {sizes[-1]/1000:.1f} kB (cap {cap/1000:.1f} kB) |")
    print(f"| fullness, mean / p50 | {100*statistics.mean(fr):.0f}% / {100*q(fr,.5):.0f}% |")
    print(f"| RBs at ≥ {100*full:.0f}% of the cap | {sum(1 for x in fr if x >= full):,} ({100*sum(1 for x in fr if x >= full)/n:.0f}%) |")
    print(f"| RBs under half the cap | {sum(1 for x in fr if x < 0.5):,} ({100*sum(1 for x in fr if x < 0.5)/n:.0f}%) |")
    carried = sum(sizes) / span
    print(f"| bytes carried | {carried/1000:.2f} kB/s: {100*carried/(cap*F):.0f}% of the ceiling at f, {100*carried/(cap/spacing):.0f}% of the cap with measured chain density (= mean fullness) |")
    print(f"| transactions | {txs:,}; {txs/n:.1f} per RB; {txs/span:.1f} per s |")
    print(f"| mean bytes per transaction (block bytes / txs) | {sum(sizes)/txs:.0f} B |")


def ts(s):
    return int(dt.datetime.strptime(s, "%Y-%m-%dT%H:%M:%S").replace(tzinfo=dt.timezone.utc).timestamp())


def fmt(t):
    return dt.datetime.fromtimestamp(t, dt.timezone.utc).strftime("%Y-%m-%d %H:%M")


if __name__ == "__main__":
    main()
