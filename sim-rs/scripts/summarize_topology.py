#!/usr/bin/env python3
"""Print summary statistics for a topology YAML/JSON file."""

import json
import math
import sys


def percentile(sorted_vals, p):
    """Return the p-th percentile (0-100) from a sorted list."""
    idx = int(len(sorted_vals) * p / 100)
    return sorted_vals[min(idx, len(sorted_vals) - 1)]


def summarize(path, verbose=False):
    with open(path) as f:
        data = json.load(f)
    nodes = data["nodes"]
    n = len(nodes)

    bp_deg = []
    relay_deg = []
    bandwidths = set()
    lats = []
    stakes = []

    for info in nodes.values():
        deg = len(info.get("producers", {}))
        stake = info.get("stake", 0)
        if stake > 0:
            bp_deg.append(deg)
            stakes.append(stake)
        else:
            relay_deg.append(deg)
        for link in info.get("producers", {}).values():
            lats.append(link["latency-ms"])
            bandwidths.add(link.get("bandwidth-bytes-per-second", 0))

    relay_deg.sort()
    bp_deg.sort()
    lats.sort()
    stakes.sort(reverse=True)
    m = len(lats)
    rd = len(relay_deg)

    print(f"Topology: {path}")
    print(f"  Nodes:  {n} ({len(bp_deg)} BPs, {len(relay_deg)} relays)")
    print(f"  Links:  {m}")
    if bandwidths:
        bw = sorted(bandwidths)
        if len(bw) == 1:
            print(f"  Bandwidth: {bw[0]:,} B/s")
        else:
            print(f"  Bandwidth: {bw[0]:,} - {bw[-1]:,} B/s")

    if rd:
        print(f"  Relay degree: min={relay_deg[0]}  p25={percentile(relay_deg, 25)}"
              f"  med={percentile(relay_deg, 50)}  p75={percentile(relay_deg, 75)}"
              f"  max={relay_deg[-1]}")
    if bp_deg:
        print(f"  BP degree:    min={bp_deg[0]}  max={bp_deg[-1]}")

    if m:
        print(f"  Latency (ms): min={lats[0]:.2f}  p5={percentile(lats, 5):.1f}"
              f"  p25={percentile(lats, 25):.1f}  med={percentile(lats, 50):.1f}"
              f"  p75={percentile(lats, 75):.1f}  p95={percentile(lats, 95):.1f}"
              f"  max={lats[-1]:.1f}")

    if stakes:
        print(f"  Stake total:  {sum(stakes):,}")
        if verbose:
            print(f"  Stake top 5:  {stakes[:5]}")
            print(f"  Stake bot 5:  {stakes[-5:]}")


def summarize_oneline(path):
    """Print a one-line summary (used by generate_topology.py)."""
    with open(path) as f:
        data = json.load(f)
    nodes = data["nodes"]
    n = len(nodes)
    links = sum(len(v.get("producers", {})) for v in nodes.values())
    bp = sum(1 for v in nodes.values() if v.get("stake", 0) > 0)
    lats = sorted(
        link["latency-ms"]
        for v in nodes.values()
        for link in v.get("producers", {}).values()
    )
    m = len(lats)
    relay_deg = sorted(
        len(v.get("producers", {}))
        for v in nodes.values()
        if v.get("stake", 0) == 0
    )
    rd = len(relay_deg)
    print(
        f"{n} nodes ({bp} BPs, {n - bp} relays), {links} links, "
        f"relay degree med={relay_deg[rd // 2]}, "
        f"latency med={lats[m // 2]:.1f} p95={lats[19 * m // 20]:.1f} max={lats[-1]:.1f} ms",
    )


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Summarize a topology YAML/JSON file.")
    parser.add_argument("topology", nargs="+", help="Path(s) to topology file(s)")
    parser.add_argument("-v", "--verbose", action="store_true", help="Show extra detail")
    parser.add_argument("-1", "--oneline", action="store_true", help="One-line summary per file")
    args = parser.parse_args()

    for path in args.topology:
        if args.oneline:
            if len(args.topology) > 1:
                print(f"{path}: ", end="")
            summarize_oneline(path)
        else:
            summarize(path, verbose=args.verbose)
            if len(args.topology) > 1:
                print()
