#!/usr/bin/env python3
"""The diffusion tables of report section 6.3, printed as Markdown from the
saved outputs of instruments/diffusion_bins.py.

    diffusion_table.py [--outputs DIR] TABLE WINDOW [WINDOW ...]

TABLE    bins      nodes counted by their own p90 of the closure age (or
                   --stage body), one column per population, with the median
                   node's p90 and never-completed share (diffusion_bins.csv)
         upstream  the nodes grouped by the number of peers that delivered
                   their announcements, per window: count, closure p90 at the
                   group's median node, body p90, vote rate at the median and
                   the 10th-percentile node, committee weight (upstream.csv)
WINDOW   a key of WINDOWS below
"""
import argparse, csv, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUTPUTS = os.path.normpath(os.path.join(HERE, "..", "outputs"))
WINDOWS = {
    "f1-high": "testnet 40 kB / 260 kB, loaded hours",
    "f2-high": "testnet 308 kB / 2 MB, loaded hours",
    "1kb": "testnet 308 kB / 2 MB, 1 kB transactions",
    "cluster-40k260k": "cluster 40 kB / 260 kB, 200 B",
    "cluster-100k1m": "cluster 100 kB / 1 MB, 200 B",
    "cluster-100k1m-374": "cluster 100 kB / 1 MB, 374 B",
    "cluster-100k1m-374-patched": "cluster 100 kB / 1 MB, 374 B, changed build",
}


def read(path):
    if not os.path.exists(path):
        return []
    with open(path, newline="") as f:
        return list(csv.DictReader(f))


def bins(outputs, names, stage):
    cols = {}
    for name in names:
        rows = read(os.path.join(outputs, name, "diffusion_bins.csv"))
        cols[name] = {r["bin"]: r["nodes"] for r in rows if r["stage"] == stage}
    order = [b for b in cols[names[0]]] if names else []
    print("| nodes by their own p90 of the %s age | " % stage + " | ".join(WINDOWS[n] for n in names) + " |")
    print("|---|" + "---|" * len(names))
    for b in order:
        label = b if b in ("nodes",) else (b if " s" in b else b)
        if b == "median node p50":
            continue
        print("| %s | " % label + " | ".join((cols[n].get(b, "-") + (" s" if b == "median node p90" else " %" if "never" in b else "")) for n in names) + " |")


def upstream(outputs, names):
    print("| window | peers delivering the node's announcements | nodes | closure p90, median node | closure p90, 90th-percentile node | body p90, median node | never completed, median node | vote rate, median node | vote rate, 10th-percentile node | share of the committee's weight |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    pct = lambda v: (v + " %") if v else "-"
    for name in names:
        for r in read(os.path.join(outputs, name, "upstream.csv")):
            print("| %s | %s | %s | %s s | %s s | %s s | %s %% | %s | %s | %s |" % (
                WINDOWS[name], r["group"], r["nodes"], r["closure_p90_median_node"], r["closure_p90_p90_node"], r["body_p90_median_node"] or "-",
                r["never_median_node"], pct(r["vote_pct_median_node"]), pct(r.get("vote_pct_p10_node", "")), r["committee_weight_share"] or "-"))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("table", choices=["bins", "upstream"])
    ap.add_argument("windows", nargs="+", metavar="WINDOW")
    ap.add_argument("--outputs", default=OUTPUTS)
    ap.add_argument("--stage", default="closure", choices=["closure", "body"])
    a = ap.parse_args()
    bad = [w for w in a.windows if w not in WINDOWS]
    if bad:
        sys.exit("unknown window %s" % ", ".join(bad))
    if a.table == "bins":
        bins(a.outputs, a.windows, a.stage)
    else:
        upstream(a.outputs, a.windows)


if __name__ == "__main__":
    main()
