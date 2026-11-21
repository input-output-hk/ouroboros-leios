#!/usr/bin/env python3
"""The diffusion tables of report section 6.4, printed as Markdown from the
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
    "f1-high": "testnet 40 kB / 260 kB, 257 B",
    "f2-high": "testnet 308 kB / 2 MB, 318 B",
    "1kb": "testnet 308 kB / 2 MB, 1 kB",
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
    # the report's form, one row per population: the bins from 2 s up and the node count; the under-2 s bin
    # (empty on every population) and the median node's rows stay in the instrument's output
    order = [b for b in cols[names[0]] if not b.startswith("median node") and b != "under 2 s"] if names else []
    # short bin headers ("2 - 3 s"); the statistic binned is named in the first column's header
    head = lambda b: b if b == "nodes" else b.replace("15 s and over", "> 15 s").replace(" to ", " - ")
    print("| population | " + " | ".join(head(b) for b in order) + " |")
    print("|---|" + "---:|" * len(order))
    for n in names:
        print("| %s | " % WINDOWS[n] + " | ".join(cols[n].get(b, "-") for b in order) + " |")


def upstream(outputs, names):
    # per group: the closure p90 and the vote rate at the median node and at the unfavourable-quartile node (the
    # quartile the stage tables of section 4 read), the body p90 at the median node, the committee weight
    print("| window | upstream peers | nodes | closure p90, s: median / quartile node | body p90, s: median node | vote rate: median / quartile node | committee weight |")
    print("|---|---|---:|---:|---:|---:|---:|")
    for name in names:
        for i, r in enumerate(read(os.path.join(outputs, name, "upstream.csv"))):
            print("| %s | %s | %s | %s / %s | %s | %s %% / %s %% | %s |" % (
                WINDOWS[name] if i == 0 else "", r["group"].replace(" upstream peer", ""), r["nodes"], r["closure_p90_median_node"], r["closure_p90_q3_node"], r["body_p90_median_node"] or "-",
                r["vote_pct_median_node"] or "-", r["vote_pct_q1_node"] or "-", r["committee_weight_share"] or "-"))


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
