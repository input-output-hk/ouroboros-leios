#!/usr/bin/env python3
"""The testnet's votes repriced: how many of the recorded votes would be in
time if the voters ran at the rate of a measured host class, or if the
voting loop's own cost were removed, read per vote and never projected to
a certification rate (report section 8.2). The voters that send no logs
cannot be repriced, so the reading is of the reporting voters' votes; the
prose says what that implies.

    voter_reprice.py voter_stages_pairs.csv --hosts data/hosts.csv
        --costs current:A_OLD:A_CHAINED:R "two older:..." "three older:..."
        [--fixed 0.02] [--deadline 7] [--min-records 10] > voter_reprice.md

Input: the per-(voter, EB) records of voter_stages.sql, one row per vote a
node scheduled, with the closure's arrival, the validation and its counts.
A vote whose closure arrived after the deadline, or never, is late in
every row, since no validation speed touches it. A vote whose closure was
in hand but whose validation never finished has no counts to reprice and
stays "never validated" in every row. The other votes get a validation
time per row, validated' = max(closure, 3 s) + duration', and are in time
when validated' <= the deadline.

Rows:
  as recorded              duration' = the recorded validation time
  closures as recorded,    the recorded time of every voter slower than the
  hosts at least current   current generation scaled by class cost / own
  generation               cost, read on the reapply cost as section 7.2
                           reads the hardware (a node without a reapply
                           reading uses its apply cost, else is not moved);
                           faster voters keep their own time
  old-input, class X       duration' = fixed + applied x A_old + reapplied x R
                           at the class's costs (--costs, the report's tables)
  loop's cost removed,     duration' = fixed + applied x A_chained + reapplied x R
  class X

First table, per row: the votes in time; the votes out of time with the
closure in hand (the validation finished past the deadline, whatever the
arrival); when those votes' closures arrived (p50 / p90 after the slot),
which says whether they are long validations or late arrivals; the
validation time per vote (p50 / p90 / max of duration' over the votes with
one). The shares no row moves,
the closure arrived after the deadline or never, the validation never
finished, and the closure arrived between the 3 s mark and the deadline,
are printed once in the lead line. The chained rows follow the old-input
ones. Then one table per EB size bin with the same rows and columns, so
that the EB size at which validation stops being a cause can be read.
"""
import argparse
import csv
from collections import defaultdict

GEN_LABEL = {"current": "current generation", "two older": "c6id", "three older": "c5d"}
GEN_ORDER = ["current", "two older", "three older"]
BINS = [(0, 2000, "under 2,000"), (2000, 4000, "2,000 to 4,000"), (4000, 6000, "4,000 to 6,000"), (6000, 10**9, "6,000 and up")]
COLS = "in time | out of time | closure at, s: p50 / p90 | validation, s: p50 / p90 / max"


def med(v):
    v = sorted(v)
    return v[len(v) // 2] if v else None


def pct(v, p):
    v = sorted(v)
    return v[int((len(v) - 1) * p)] if v else float("nan")


def fnum(s):
    return float(s) if s not in ("", None) else None


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("pairs", help="voter_stages_pairs.csv of the window")
    ap.add_argument("--hosts", required=True, help="data/hosts.csv: the IOG and PIR hosts' agents and generations")
    ap.add_argument("--costs", nargs="+", required=True, metavar="GEN:APPLY_OLD_MS:APPLY_CHAINED_MS:REAPPLY_US",
                    help="per host class (current, 'two older', 'three older'; quote the name) the cost per applied transaction on old-input "
                         "closures, the same on chained closures, and the cost per reapplied transaction, from the report's tables")
    ap.add_argument("--fixed", type=float, default=0.02, help="the per-EB fixed term of the rebuilt time, seconds")
    ap.add_argument("--deadline", type=float, default=7.0)
    ap.add_argument("--min-records", type=int, default=10)
    a = ap.parse_args()
    given = {}
    for c in a.costs:
        g, ao, ac, rr = c.rsplit(":", 3)
        given[g] = (float(ao) * 1e-3, float(ac) * 1e-3, float(rr) * 1e-6)
    hosts = {r["agent"]: r for r in csv.DictReader(open(a.hosts, newline=""))}

    # the votes: (agent, eb, txs, closure_s or None, duration_s or None, applied, reapplied)
    votes = []
    txs = {}
    for r in csv.DictReader(open(a.pairs, newline="")):
        c, d = fnum(r["closure_s"]), fnum(r["duration_s"])
        x, y = fnum(r["applied"]) or 0.0, fnum(r["reapplied"]) or 0.0
        t = fnum(r["txs"])
        if t is not None:
            txs[r["eb"]] = max(txs.get(r["eb"], 0.0), t)
        if d is not None and not (0 <= d < 120):
            d = None
        votes.append((r["agent"], r["eb"], c, d, x, y))
    votes = [v for v in votes if v[1] in txs]

    # per node costs from its own records, as testnet_speed.py reads them
    by_node = defaultdict(list)
    for ag, eb, c, d, x, y in votes:
        if d is not None and x + y >= 1:
            by_node[ag].append((d, x, y))
    cost = {}
    for ag, rs in by_node.items():
        re_ = [d / (x + y) for d, x, y in rs if x == 0]
        rg = med(re_) if len(re_) >= a.min_records else None
        app = [(d - y * rg) / x for d, x, y in rs if x / (x + y) >= 0.5] if rg is not None else []
        ag_ = med(app) if len(app) >= a.min_records else None
        cost[ag] = (ag_, rg)
    cls = {}
    for g in GEN_ORDER:
        ags = [ag for ag, h in hosts.items() if h["generation"] == g and ag in cost]
        cls[g] = (med([cost[ag][0] for ag in ags if cost[ag][0] is not None]), med([cost[ag][1] for ag in ags if cost[ag][1] is not None]))
    ca, cr = cls["current"]
    ratio, unmoved = {}, []
    for ag, (na, nr) in cost.items():
        if nr is not None and cr is not None:
            ratio[ag] = min(1.0, cr / nr)
        elif na is not None and ca is not None:
            ratio[ag] = min(1.0, ca / na)
        else:
            ratio[ag] = 1.0
            unmoved.append(ag)
    moved = sum(1 for r in ratio.values() if r < 1)

    def reprice(kind, arg=None):
        """Per vote the outcome under a row: 'in', 'closure', 'out' or 'never', with the closure's arrival and
        duration' for the repriced ones. kind: 'recorded', 'hardware' (arg = ratio per node), 'rebuild' (arg = (A, R))."""
        out = []
        for ag, eb, c, d, x, y in votes:
            if c is None or c > a.deadline:
                out.append((eb, "closure", c, None))
                continue
            if d is None:
                out.append((eb, "never", c, None))
                continue
            start = max(c, 3.0)
            if kind == "recorded" or x + y < 1:
                d2 = d
            elif kind == "hardware":
                d2 = arg.get(ag, 1.0) * d
            else:
                d2 = a.fixed + x * arg[0] + y * arg[1]
            out.append((eb, "in" if start + d2 <= a.deadline else "out", c, d2))
        return out

    def summary(out, ebs=None):
        """The row's cells: votes in time; out of time with the closure in hand; those votes' closure arrival
        p50 / p90; validation per vote p50 / p90 / max."""
        rows = [o for o in out if ebs is None or o[0] in ebs]
        n = len(rows)
        d = [x for _, _, _, x in rows if x is not None]
        late_c = [c for _, k, c, _ in rows if k == "out"]
        share = lambda k: 100.0 * sum(1 for _, kk, _, _ in rows if kk == k) / n
        return "%.1f %% | %.1f %% | %s | %.2f / %.2f / %.1f" % (
            share("in"), share("out"), "%.1f / %.1f" % (pct(late_c, .5), pct(late_c, .9)) if late_c else "-",
            pct(d, .5), pct(d, .9), max(d))

    def constant(out, ebs=None):
        """The shares no row moves: the closure arrived after the deadline or never; the validation never
        finished; the closure arrived between the 3 s mark and the deadline (a shortened budget)."""
        rows = [o for o in out if ebs is None or o[0] in ebs]
        n = len(rows)
        return tuple(100.0 * sum(1 for _, kk, _, _ in rows if kk == k) / n for k in ("closure", "never")) + (
            100.0 * sum(1 for _, k, c, _ in rows if k in ("in", "out") and c > 3.0) / n,)

    rec = reprice("recorded")
    hw = reprice("hardware", ratio)
    rows = [("as recorded", rec), ("closures as recorded, hosts at least current generation", hw)]
    for g in GEN_ORDER:
        if g in given:
            rows.append(("old-input, %s" % GEN_LABEL[g], reprice("rebuild", (given[g][0], given[g][2]))))
    for g in GEN_ORDER:
        if g in given:
            rows.append(("loop's cost removed, %s" % GEN_LABEL[g], reprice("rebuild", (given[g][1], given[g][2]))))

    nvotes, nebs = len(votes), len(txs)
    cl, nv, mid = constant(rec)
    print("Votes %s on %s EBs from %d nodes; deadline %g s after the EB slot. Late in every row: %.1f %% of the votes whose closure arrived "
          "after the deadline or never, and %.1f %% whose validation never finished (no counts to reprice); %.1f %% of the votes had the "
          "closure arrive between the 3 s mark and the deadline, a shortened budget. Hardware row: %d nodes "
          "slower than the current generation scaled down by their own reapply cost over the class's (%s), %d without a reading not moved. "
          "Rebuilt rows: %g s per EB plus the applied transactions at the class's cost (old-input, or chained with the loop's cost removed) "
          "and the reapplied ones at its reapply cost; costs per class (ms / ms / us): %s.\n" % (
              "{:,}".format(nvotes), "{:,}".format(nebs), len(by_node), a.deadline, cl, nv, mid, moved,
              "%.0f us" % (cr * 1e6) if cr else "n/a", len(unmoved), a.fixed,
              "; ".join("%s %.2f / %.2f / %.0f" % (g, ao * 1e3, ac * 1e3, rr * 1e6) for g, (ao, ac, rr) in given.items())))
    print("| row | %s |" % COLS)
    print("|---|" + "---|" * 4)
    for label, out in rows:
        print("| %s | %s |" % (label, summary(out)))

    for lo, hi, lab in BINS:
        ebs = {eb for eb, t in txs.items() if lo <= t < hi}
        if not ebs:
            continue
        cl, nv, mid = constant(rec, ebs)
        print("\nEBs of %s transactions, %s EBs; late in every row: %.1f %% of the votes for the closure's arrival, %.1f %% never validated; "
              "%.1f %% had the closure arrive between the 3 s mark and the deadline.\n" % (lab, "{:,}".format(len(ebs)), cl, nv, mid))
        print("| row | %s |" % COLS)
        print("|---|" + "---|" * 4)
        for label, out in rows:
            print("| %s | %s |" % (label, summary(out, ebs)))


if __name__ == "__main__":
    main()
