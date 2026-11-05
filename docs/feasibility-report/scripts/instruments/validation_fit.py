#!/usr/bin/env python3
"""The cost of validating a transaction at the vote, per node (report
section 6.1 and 6.4): on the per-(node, EB) validation records of a window
or run (validation_pairs.csv, written by validation_pairs.sql or
cluster_validation_pairs.sql), the least-squares fit

    duration = a x applied + b x reapplied + c

pooled over all records and per node with 100 or more records, where
duration is the validation time after the later of the closure's arrival
and the slot plus 3 s, applied the transactions validated in full and
reapplied the ones already validated. Printed as Markdown: the pooled
rates, the distribution of the per-node rates across nodes (no node named),
and, with --hosts, the rates of the named hosts by instance class.

A node that holds nearly every transaction of every EB (applied share near
zero) gives the fit almost no variation in the applied count, so its rate
per applied transaction is poorly identified; the distribution keeps every
node as the earlier analyses did, while the host-class table fits each
host on the EBs where it applied 500 or more transactions in full (at
least 30 such records, otherwise blank), which is where the rate is
measured.

    validation_fit.py validation_pairs.csv [--hosts data/hosts.csv] > validation_fit.md

--hosts  a CSV agent,host,instance,vcpu,generation: the hosts to print by
         class (the IOG and PIR producers); every other node stays in the
         distribution only
"""
import argparse, csv, statistics as st
from collections import defaultdict


def solve3(rs):
    S = [[0.0] * 3 for _ in range(3)]
    T = [0.0] * 3
    for r in rs:
        x = (r[0], r[1], 1.0)
        for i in range(3):
            T[i] += x[i] * r[2]
            for j in range(3):
                S[i][j] += x[i] * x[j]
    M = [S[i] + [T[i]] for i in range(3)]
    for i in range(3):
        p = max(range(i, 3), key=lambda k: abs(M[k][i]))
        M[i], M[p] = M[p], M[i]
        if abs(M[i][i]) < 1e-12:
            return None
        for k in range(3):
            if k != i:
                f = M[k][i] / M[i][i]
                M[k] = [M[k][j] - f * M[i][j] for j in range(4)]
    sol = [M[i][3] / M[i][i] for i in range(3)]
    res = [r[2] - (sol[0] * r[0] + sol[1] * r[1] + sol[2]) for r in rs]
    return sol, (sum(e * e for e in res) / max(len(rs) - 3, 1)) ** 0.5


def q(v, p):
    v = sorted(v)
    i = (len(v) - 1) * p
    lo = int(i)
    return v[lo] + (v[min(lo + 1, len(v) - 1)] - v[lo]) * (i - lo)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("pairs")
    ap.add_argument("--hosts")
    ap.add_argument("--min-records", type=int, default=100)
    a = ap.parse_args()
    by = defaultdict(list)
    n = 0
    with open(a.pairs, newline="") as f:
        for r in csv.DictReader(f):
            if not r["duration_s"] or not (0 <= float(r["duration_s"]) < 60):
                continue
            by[r["agent"]].append((float(r["applied"]), float(r["reapplied"]), float(r["duration_s"])))
            n += 1
    allrows = [x for rs in by.values() for x in rs]
    (pa, pb, pc), rmse = solve3(allrows)
    share = [x[0] / max(x[0] + x[1], 1) for x in allrows]
    print("| pooled over %s records of %d nodes | per applied transaction | per reapplied transaction | fixed per EB | residual | applied share, median record |" % ("{:,}".format(n), len(by)))
    print("|---|---|---|---|---|---|")
    print("| fit | %.2f ms | %.3f ms | %.2f s | %.2f s | %.0f %% |" % (pa * 1000, pb * 1000, pc, rmse, 100 * q(share, 0.5)))
    fits = {}
    for agent, rs in by.items():
        if len(rs) < a.min_records:
            continue
        f = solve3(rs)
        if f:
            (x, y, z), e = f
            fits[agent] = (x * 1000, y * 1000, z, e, len(rs), q([r[0] / max(r[0] + r[1], 1) for r in rs], 0.5))
    av = [v[0] for v in fits.values()]
    bv = [v[1] for v in fits.values()]
    print()
    print("| per node, %d nodes with %d or more records | min | p25 | median | p75 | max |" % (len(fits), a.min_records))
    print("|---|---|---|---|---|---|")
    print("| ms per applied transaction | %.2f | %.2f | %.2f | %.2f | %.2f |" % (min(av), q(av, .25), q(av, .5), q(av, .75), max(av)))
    print("| ms per reapplied transaction | %.3f | %.3f | %.3f | %.3f | %.3f |" % (min(bv), q(bv, .25), q(bv, .5), q(bv, .75), max(bv)))
    if a.hosts:
        hosts = {r["agent"]: r for r in csv.DictReader(open(a.hosts, newline=""))}
        cls = defaultdict(list)
        for agent, rs in by.items():
            if agent not in hosts:
                continue
            big = [r for r in rs if r[0] >= 500]
            f = solve3(big) if len(big) >= 30 else None
            cls[(hosts[agent]["instance"], hosts[agent]["vcpu"], hosts[agent]["generation"], hosts[agent]["deployment"])].append(
                (hosts[agent]["host"], len(big), f[0][0] * 1000 if f else None, f[0][1] * 1000 if f else None, f[0][2] if f else None))
        print()
        print("| host class (instance, vCPU, generation) | hosts | EBs with 500+ applied, per host | ms per applied transaction | ms per reapplied transaction | fixed per EB |")
        print("|---|---|---|---|---|---|")
        rng = lambda xs, fmt: ("-" if not xs else (fmt % xs[0]) if len(xs) == 1 else (fmt % min(xs)) + " to " + (fmt % max(xs)))
        order = lambda kv: st.median([x[2] for x in kv[1] if x[2] is not None] or [9e9])
        for (inst, vcpu, gen, dep), hs in sorted(cls.items(), key=order):
            av = [x[2] for x in hs if x[2] is not None]
            bv = [x[3] for x in hs if x[3] is not None]
            cv = [x[4] for x in hs if x[4] is not None]
            print("| %s, %s vCPU, %s | %s | %s | %s | %s | %s s |" % (inst, vcpu, gen, ", ".join(sorted(h for h, *_ in hs)), rng([x[1] for x in hs], "%d"), rng(av, "%.2f"), rng(bv, "%.3f"), rng(cv, "%.2f")))


if __name__ == "__main__":
    main()
