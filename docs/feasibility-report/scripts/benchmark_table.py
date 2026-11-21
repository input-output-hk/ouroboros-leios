#!/usr/bin/env python3
"""The ledger benchmark table of report section 7 (Table 7.1): the operators'
survey of db-analyser's ledger operations (data/benchmark_survey.csv, one
row per machine, no machine named), printed by processor model with the
machines' count and the range of each cost, and the distribution over the
27 machines.

    benchmark_table.py [--data data/benchmark_survey.csv] [--full]

Every cost is in microseconds per transaction of the survey's chain fragment (2,086
two-input transactions of about 368 B per block): apply and reapply with
the UTxO in memory and on disk (LSM, page cache bypassed), the columns
ordered so that the two apply readings sit together and the two in-memory
readings sit together. Processor models are grouped as the survey reports
them; a model's row gives the range over its machines. --full adds the
machines' logical CPU counts and virtualisation as they report them (the
expanded table, not in the report).
"""
import argparse, csv, os
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.normpath(os.path.join(HERE, "..", "data", "benchmark_survey.csv"))
COLS = [("apply_on_disk_us", "apply, on disk"), ("apply_in_memory_us", "apply, in memory"),
        ("reapply_in_memory_us", "reapply, in memory"), ("reapply_on_disk_us", "reapply, on disk")]


def q(v, p):
    v = sorted(v)
    i = (len(v) - 1) * p
    lo = int(i)
    return v[lo] + (v[min(lo + 1, len(v) - 1)] - v[lo]) * (i - lo)


def rng(xs):
    xs = sorted(xs)
    return "%.0f" % xs[0] if xs[0] == xs[-1] else "%.0f to %.0f" % (xs[0], xs[-1])


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--data", default=DATA)
    ap.add_argument("--full", action="store_true", help="add the machines' logical CPU counts and virtualisation, as they report them")
    a = ap.parse_args()
    rows = list(csv.DictReader(open(a.data, newline="")))
    by = defaultdict(list)
    for r in rows:
        by[r["processor"]].append(r)
    extra = ["logical CPUs", "virtualisation"] if a.full else []
    print("| " + " | ".join(["processor (machines); every cost in microseconds per transaction"] + extra + [c[1] for c in COLS]) + " |")
    print("|---|" + "---|" * (len(extra) + len(COLS)))
    order = sorted(by.items(), key=lambda kv: min(float(r["apply_in_memory_us"]) for r in kv[1]))
    for proc, rs in order:
        cells = ["%s (%d)" % (proc, len(rs))]
        if a.full:
            cpus = sorted({r["logical_cpus"] for r in rs if r["logical_cpus"]}, key=int)
            virt = sorted({r["virtualisation"] or "not stated" for r in rs})
            cells += [", ".join(cpus) or "not stated", ", ".join(virt)]
        cells += [rng([float(r[c[0]]) for r in rs]) for c in COLS]
        print("| " + " | ".join(cells) + " |")
    print()
    print("| over the %d machines, microseconds per transaction | min | lower quartile | median | upper quartile | max |" % len(rows))
    print("|---|---|---|---|---|---|")
    for col, label in COLS:
        v = [float(r[col]) for r in rows]
        print("| %s | %.0f | %.0f | %.0f | %.0f | %.0f |" % (label, min(v), q(v, .25), q(v, .5), q(v, .75), max(v)))


if __name__ == "__main__":
    main()
