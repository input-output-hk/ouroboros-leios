#!/usr/bin/env python3
"""Diffusion by population without node identities (report section 6.3):
from a window's per-node diffusion tables (diffusion.csv for the closure
stage and diffusion-body.csv for the body stage, written by
diffusion_nodes.py) and its coverage table (voters.csv, testnet windows),
two CSVs:

  diffusion_bins.csv   per stage, the nodes counted by their own p90 of the
                       stage's age (seconds after the EB's slot) in bins, and
                       the median node's p50, p90 and never-completed share
  upstream.csv         the nodes grouped by how many peers delivered their
                       announcements: count, the group's closure p90 at its
                       median node and at its 90th-percentile node, its body
                       p90 at the median node, its never-completed share at
                       the median node, its vote rate at the median node and
                       at the 10th-percentile node (the tail), and the share
                       of the committee's weight its pools hold (testnet)

    diffusion_bins.py OUTPUT_DIR     (reads and writes in that window's outputs folder)
"""
import argparse, csv, os, statistics as st

BINS = [2, 3, 4, 7, 15, 60]
# upstream 0 = the peer is not in the node's records (the IOG and PIR hosts' monitoring events carry no source peer)
GROUPS = [(1, 1, "1 upstream peer"), (2, 3, "2 to 3"), (4, 10, "4 to 10"), (11, 30, "11 to 30"), (31, 10 ** 9, "31 and more"), (0, 0, "not recorded (IOG and PIR hosts)")]


def load(path, min_ebs=50):
    if not os.path.exists(path):
        return []
    with open(path, newline="") as f:
        return [r for r in csv.DictReader(f) if int(r["ebs"]) >= min_ebs]


def fl(x):
    return float(x) if x not in ("", "NULL", None) else None


def q(v, p):
    v = sorted(v)
    i = (len(v) - 1) * p
    lo = int(i)
    return v[lo] + (v[min(lo + 1, len(v) - 1)] - v[lo]) * (i - lo)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("out")
    a = ap.parse_args()
    clo, body = load(os.path.join(a.out, "diffusion.csv")), load(os.path.join(a.out, "diffusion-body.csv"))
    # hosts whose own records carry no peer (upstream 0): the count from the monitoring's per-peer events, if pulled
    hp = os.path.join(a.out, "upstream_hosts.csv")
    if os.path.exists(hp):
        fix = {r["agent"]: r["upstream"] for r in csv.DictReader(open(hp, newline=""))}
        for r in clo:
            if int(r["upstream"]) == 0 and r["agent"] in fix:
                r["upstream"] = fix[r["agent"]]
    with open(os.path.join(a.out, "diffusion_bins.csv"), "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["stage", "bin", "nodes"])
        for stage, rows in (("body", body), ("closure", clo)):
            v = [fl(r["p90"]) for r in rows if fl(r["p90"]) is not None]
            edges = [0] + BINS + [None]
            for lo, hi in zip(edges[:-1], edges[1:]):
                name = "under %g s" % hi if lo == 0 else ("%g s and over" % lo if hi is None else "%g to %g s" % (lo, hi))
                w.writerow([stage, name, sum(1 for x in v if x >= lo and (hi is None or x < hi))])
            w.writerow([stage, "nodes", len(rows)])
            p50 = [fl(r["p50"]) for r in rows if fl(r.get("p50")) is not None]
            if p50:  # the testnet tables carry p90, p95 and p99 only
                w.writerow([stage, "median node p50", "%.2f" % st.median(p50)])
            w.writerow([stage, "median node p90", "%.2f" % st.median(v)])
            w.writerow([stage, "median node never completed %", "%.1f" % st.median(fl(r["never"]) for r in rows if fl(r["never"]) is not None)])
    # committee weight per pool, mean over the window's committees
    weight = {}
    vpath = os.path.join(a.out, "voters.csv")
    if os.path.exists(vpath):
        per = {}
        for r in csv.DictReader(open(vpath, newline="")):
            d = per.setdefault(r["win"], {})
            d[r["pool_id"]] = d.get(r["pool_id"], 0.0) + float(r["weight"])
        tot = {win: sum(d.values()) for win, d in per.items()}
        pools = {p for d in per.values() for p in d}
        for p in pools:
            weight[p] = st.mean(per[win].get(p, 0.0) / tot[win] for win in per)
    bodyp90 = {(r["agent"], r["pool"]): fl(r["p90"]) for r in body}
    with open(os.path.join(a.out, "upstream.csv"), "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["group", "nodes", "closure_p90_median_node", "closure_p90_p90_node", "body_p90_median_node", "never_median_node", "vote_pct_median_node", "vote_pct_p10_node", "committee_weight_share"])
        for lo, hi, name in GROUPS:
            rows = [r for r in clo if lo <= int(r["upstream"]) <= hi]
            if not rows:
                continue
            cp = [fl(r["p90"]) for r in rows if fl(r["p90"]) is not None]
            bp = [bodyp90.get((r["agent"], r["pool"])) for r in rows]
            bp = [x for x in bp if x is not None]
            vr = [fl(r["vote_pct"]) for r in rows if fl(r.get("vote_pct")) is not None]
            ws = sum(weight.get(r["pool"], 0.0) for r in rows) if weight else None
            w.writerow([name, len(rows), "%.2f" % q(cp, .5), "%.2f" % q(cp, .9), "%.2f" % q(bp, .5) if bp else "",
                        "%.1f" % st.median(fl(r["never"]) for r in rows), "%.0f" % st.median(vr) if vr else "", "%.0f" % q(vr, .1) if vr else "", "%.2f" % ws if ws is not None else ""])
    print("wrote diffusion_bins.csv and upstream.csv in %s (%d closure rows, %d body rows)" % (a.out, len(clo), len(body)))


if __name__ == "__main__":
    main()
