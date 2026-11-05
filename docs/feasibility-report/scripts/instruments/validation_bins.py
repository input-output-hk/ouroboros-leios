#!/usr/bin/env python3
"""Validation time by the share of the EB's transactions the voter had not
seen (report sections 6.1 and 6.2), without a model: on the per-(node, EB)
validation records of one window or run (validation_pairs.csv), the
validation time per EB, where the time is the one after the later of the
closure's arrival and the slot plus 3 s, on the EBs of one size (the
500-transaction class holding the most distinct EBs in the window, so that
the transaction count is not mixed into the comparison), grouped by the
applied share (applied over applied plus reapplied) of each record.

Per group: the median over the records in the group, for each named host
(--hosts, the IOG and PIR producers, printed by instance class and
deployment, the IOG producers behind their relays apart from the PIR hosts
in the open network; a cell is
marked tentative when a host in it has fewer than 30 records, and left
blank when every host has fewer than 10) and for the other nodes as a
distribution over one node set,
the nodes with 20 or more records in every group (per node the median of
its records, then the median node and the quartiles across nodes).
Records of every EB the voter validated, certified or not. Printed as
Markdown.

    validation_bins.py validation_pairs.csv [--hosts data/hosts.csv] > validation_bins.md
"""
import argparse, csv, statistics as st
from collections import defaultdict

BINS = [(0, .1, "under 10 %"), (.1, .3, "10 to 30 %"), (.3, .5, "30 to 50 %"), (.5, .7, "50 to 70 %"), (.7, 1.01, "70 % and over")]


def q(v, p):
    v = sorted(v)
    i = (len(v) - 1) * p
    lo = int(i)
    return v[lo] + (v[min(lo + 1, len(v) - 1)] - v[lo]) * (i - lo)


def binof(s):
    for lo, hi, name in BINS:
        if lo <= s < hi:
            return name
    return BINS[-1][2]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("pairs")
    ap.add_argument("--hosts")
    ap.add_argument("--min-records", type=int, default=20, help="records a node needs in a group to count in the distribution")
    ap.add_argument("--min-host-records", type=int, default=30, help="records a named host needs in a group for a firm cell")
    a = ap.parse_args()
    hosts = {r["agent"]: r for r in csv.DictReader(open(a.hosts, newline=""))} if a.hosts else {}
    recs = defaultdict(lambda: defaultdict(list))   # agent -> bin -> [(s per 1000 txs, s per EB)]
    with open(a.pairs, newline="") as f:
        for r in csv.DictReader(f):
            if not r["duration_s"]:
                continue
            d, ap_, re_ = float(r["duration_s"]), float(r["applied"]), float(r["reapplied"])
            n = ap_ + re_
            if not (0 <= d < 60) or n < 100:
                continue
            recs[r["agent"]][binof(ap_ / n)].append((1000.0 * d / n, d, n, r["eb"]))
    names = [b[2] for b in BINS]
    cls = defaultdict(list)
    for agent, byb in recs.items():
        if agent in hosts:
            h = hosts[agent]
            cls[(h["instance"], h["vcpu"], h["generation"], h["deployment"])].append((h["host"], byb))
    label = "operator nodes" if hosts else "all nodes"
    # one EB size: the 500-transaction class holding the most distinct EBs (the modal class of the window)
    ebs_by_class = defaultdict(set)
    for byb in recs.values():
        for rs in byb.values():
            for x in rs:
                ebs_by_class[int(x[2] // 500) * 500].add(x[3])
    mode = max(ebs_by_class, key=lambda c: len(ebs_by_class[c]))
    lo_n, hi_n = mode, mode + 499
    print("EBs of %s to %s transactions, the window's most common size class, %d EBs; a cell in which a host has fewer than %d records is marked tentative.\n" % ("{:,}".format(lo_n), "{:,}".format(hi_n + 1), len(ebs_by_class[mode]), a.min_host_records))
    print("| validation time per EB, s (median; records in brackets) | " + " | ".join("applied share " + n for n in names) + " |")
    print("|---|" + "---|" * len(names))
    inband = lambda rs: [x for x in rs if lo_n <= x[2] <= hi_n]
    for (inst, vcpu, gen, dep), hs in sorted(cls.items(), key=lambda kv: (kv[0][2] != "current", kv[0][1], kv[0][3], kv[0][0])):
        cells = []
        for b in names:
            vals = [q([x[1] for x in inband(byb[b])], .5) for _, byb in hs if len(inband(byb[b])) >= 10]
            n = sum(len(inband(byb[b])) for _, byb in hs)
            firm = all(len(inband(byb[b])) >= a.min_host_records for _, byb in hs if len(inband(byb[b])) >= 10)
            mark = "" if firm else ", tentative"
            cells.append("-" if not vals else ("%.2f (%d%s)" % (vals[0], n, mark) if len(vals) == 1 else "%.2f to %.2f (%d%s)" % (min(vals), max(vals), n, mark)))
        print("| %s, %s vCPU, %s: %s | %s |" % (inst, vcpu, gen, ", ".join(sorted(h for h, _ in hs)), " | ".join(cells)))
    # the other nodes: the same set in every column (nodes with the minimum records in every group), so that a
    # column's median node is not a different population from the next column's
    same = {ag: byb for ag, byb in recs.items() if ag not in hosts and all(len(inband(byb[b])) >= a.min_records for b in names)}
    label2 = label + ", the %d with %d+ EBs of this size in every group" % (len(same), a.min_records)
    for stat, p, title in (("median node", .5, "%s, median node" % label2), ("q1", .25, "lower quartile node"), ("q3", .75, "upper quartile node")):
        cells = []
        for b in names:
            per = [q([x[1] for x in inband(byb[b])], .5) for byb in same.values()]
            cells.append("-" if not per else "%.2f" % q(per, p))
        print("| %s | %s |" % (title, " | ".join(cells)))


if __name__ == "__main__":
    main()
