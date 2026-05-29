#!/usr/bin/env python3
"""Aggregate MemorySizes telemetry events from a cluster JSONL log.

Usage:
  scripts/memory-report.py <events.jsonl>                # text summary
  scripts/memory-report.py <events.jsonl> --csv <key>    # time-series CSV per node
  scripts/memory-report.py <events.jsonl> --leak-check   # flag metrics that don't plateau

<key> uses dot notation against the MemorySizes message body, e.g.:
  leios_store.notifications
  leios.cand_vote_offers
  praos.chain_tree
  fragments.bytes_estimate
"""

import json
import statistics
import sys
from collections import defaultdict


def load_events(path):
    events = []
    with open(path) as f:
        for line in f:
            try:
                d = json.loads(line)
            except json.JSONDecodeError:
                continue
            msg = d.get("message", {})
            if msg.get("type") != "MemorySizes":
                continue
            events.append((d["time_s"], msg))
    return events


def dig(d, dotted):
    cur = d
    for part in dotted.split("."):
        if not isinstance(cur, dict) or part not in cur:
            return None
        cur = cur[part]
    return cur


METRICS = [
    "leios_store.notifications",
    "leios_store.notifications_bytes_estimate",
    "leios_store.blocks",
    "leios_store.block_txs",
    "leios_store.eb_tx_hashes",
    "leios_store.votes",
    "leios.cand_block_offers",
    "leios.cand_eb_offers",
    "leios.cand_eb_txs_offers",
    "leios.cand_vote_offers",
    "leios.cand_pending_eb",
    "leios.cand_pending_eb_txs",
    "leios.eb_tx_hash_entries_total",
    "leios.elections",
    "leios.endorsed_unvalidated_ebs",
    "praos.chain_tree",
    "praos.block_cache",
    "praos.header_first_seen",
    "praos.validated",
    "praos.peer_chain_total",
    "praos.in_flight",
    "fragments.bytes_estimate",
    "fragments.fragment_total",
]


def by_node(events):
    out = defaultdict(list)
    for t, msg in events:
        out[msg["node"]].append((t, msg))
    for node in out:
        out[node].sort(key=lambda x: x[0])
    return out


def percentile(xs, p):
    if not xs:
        return 0.0
    xs = sorted(xs)
    k = (len(xs) - 1) * p
    f, c = int(k), min(int(k) + 1, len(xs) - 1)
    return xs[f] + (xs[c] - xs[f]) * (k - f)


def summary(events):
    if not events:
        print("no MemorySizes events found")
        return
    t0 = min(t for t, _ in events)
    tN = max(t for t, _ in events)
    nodes = by_node(events)
    print(f"file: {len(events)} MemorySizes events, {len(nodes)} nodes, duration {tN - t0:.1f}s")
    print(f"time range: {t0:.1f} → {tN:.1f}")
    print()

    # final-sample stats across nodes
    print("Final-sample distribution across nodes (min / p50 / p95 / max):")
    print(f"  {'metric':<42} {'min':>10} {'p50':>10} {'p95':>10} {'max':>10}")
    for m in METRICS:
        vals = []
        for samples in nodes.values():
            v = dig(samples[-1][1], m)
            if isinstance(v, (int, float)):
                vals.append(v)
        if not vals:
            continue
        print(
            f"  {m:<42} {min(vals):>10.1f} {percentile(vals, 0.5):>10.1f} "
            f"{percentile(vals, 0.95):>10.1f} {max(vals):>10.1f}"
        )

    print()
    # growth trajectory: cluster mean per 20s window for the headline metrics
    headline = [
        "leios_store.notifications",
        "leios_store.notifications_bytes_estimate",
        "leios.cand_eb_offers",
        "leios.eb_tx_hash_entries_total",
        "praos.chain_tree",
        "praos.block_cache",
    ]
    window_s = 20.0
    n_windows = max(1, int((tN - t0) // window_s) + 1)
    print(f"Cluster-mean trajectory by {int(window_s)}s window:")
    header = f"  {'metric':<42}" + "".join(f"{int(i * window_s):>8}s" for i in range(n_windows))
    print(header)
    for m in headline:
        buckets = [[] for _ in range(n_windows)]
        for t, msg in events:
            v = dig(msg, m)
            if not isinstance(v, (int, float)):
                continue
            idx = min(int((t - t0) // window_s), n_windows - 1)
            buckets[idx].append(v)
        row = f"  {m:<42}"
        for b in buckets:
            row += f"{statistics.mean(b) if b else 0:>9.1f}"
        print(row)


def leak_check(events):
    """Check whether each metric plateaus in the last quarter of the run.

    Compares mean of the last quarter against mean of the previous quarter.
    A metric that's still climbing during the last quarter is flagged "growing".
    A long warm-up that plateaus near the end will not be flagged.
    """
    if not events:
        print("no events")
        return
    t0 = min(t for t, _ in events)
    tN = max(t for t, _ in events)
    duration = tN - t0
    if duration < 60:
        print(f"run too short ({duration:.1f}s) for leak detection")
        return
    q = duration / 4
    cutoffs = [t0 + q, t0 + 2 * q, t0 + 3 * q]
    print("Leak check: cluster-mean per quarter (q1/q2/q3/q4); q4_delta = mean(last q4 half) − mean(first q4 half)")
    print(f"  duration={duration:.1f}s, samples={len(events)}")
    print()
    print(
        f"  {'metric':<42} {'q1':>9} {'q2':>9} {'q3':>9} {'q4':>9} "
        f"{'q3→q4':>8} {'q4_delta':>10}  flag"
    )
    q4_start = cutoffs[2]
    q4_mid = t0 + 3.5 * q
    for m in METRICS:
        quarters = [[], [], [], []]
        q4_first_half, q4_second_half = [], []
        for t, msg in events:
            v = dig(msg, m)
            if not isinstance(v, (int, float)):
                continue
            if t < cutoffs[0]:
                quarters[0].append(v)
            elif t < cutoffs[1]:
                quarters[1].append(v)
            elif t < cutoffs[2]:
                quarters[2].append(v)
            else:
                quarters[3].append(v)
                (q4_first_half if t < q4_mid else q4_second_half).append(v)
        if not all(quarters) or not q4_first_half or not q4_second_half:
            continue
        means = [statistics.mean(q) for q in quarters]
        q34 = means[3] - means[2]
        q4d = statistics.mean(q4_second_half) - statistics.mean(q4_first_half)
        # plateau if q4_delta is small (absolute < 0.5 AND relative < 1%)
        rel = abs(q4d) / max(means[3], 1)
        if abs(q4d) < 0.5 and rel < 0.01:
            flag = "  plateau"
        elif q4d > 0.5 and q4d / max(means[3], 1) > 0.02:
            flag = "  growing"
        elif q4d < -0.5:
            flag = "  shrinking"
        else:
            flag = "  near-plateau"
        print(
            f"  {m:<42} {means[0]:>9.1f} {means[1]:>9.1f} {means[2]:>9.1f} {means[3]:>9.1f} "
            f"{q34:>+8.1f} {q4d:>+10.3f}{flag}"
        )


def csv_dump(events, key):
    nodes = by_node(events)
    node_names = sorted(nodes.keys())
    t0 = min(t for t, _ in events)
    # pivot: for each sample row, time and one column per node
    rows = defaultdict(dict)
    for t, msg in events:
        v = dig(msg, key)
        if v is None:
            continue
        rows[round(t - t0, 3)][msg["node"]] = v
    print("time_s," + ",".join(node_names))
    for t in sorted(rows):
        print(f"{t}," + ",".join(str(rows[t].get(n, "")) for n in node_names))


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(2)
    path = sys.argv[1]
    events = load_events(path)
    if "--csv" in sys.argv:
        i = sys.argv.index("--csv")
        if i + 1 >= len(sys.argv):
            print("--csv requires a key", file=sys.stderr)
            sys.exit(2)
        csv_dump(events, sys.argv[i + 1])
    elif "--leak-check" in sys.argv:
        leak_check(events)
    else:
        summary(events)


if __name__ == "__main__":
    main()
