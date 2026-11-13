#!/usr/bin/env python3
"""Certification and throughput of a cluster run on faster hosts or with a
cheaper voting loop, and the EBs that fail by the share of their
transactions the voters applied in full (report sections 6.2 and 8), from
the run's per-(voter, EB) validation records (validation_pairs.csv) and its
ladder export.

    host_speed.py validation_pairs.csv ladder.jsonl E_KB --costs APPLY_MS REAPPLY_US
        [LABEL:APPLY_RATIO:REAPPLY_RATIO[:closure] ...] > host_speed.md

Per record: validated' = max(closure, 3 s) + duration', where duration is
the recorded validation time after that start and duration' scales its
apply part and its reapply part separately: the record's time is split
between the two operations in proportion to applied x APPLY_MS and
reapplied x REAPPLY_US, the run's measured costs (Table 7.3), and each part
is multiplied by its ratio. A row 'c6id:0.85:0.85' is the run on hosts two
generations newer (the hardware factor of Table 7.2 on both operations), a
row 'loop fix:0.19:1' the loop with its apply cost at the chained level of
the same hosts (section 7.3's mechanism removed) and reapply unchanged; a
row ending in ':closure' starts the validation when the closure arrived
instead of at the 3 s mark. A voter votes if validated' <= 7 s; an EB
certifies with QUORUM voters or more. Throughput is the ladder's formula
    kB/s = f_obs x (p_obs x B + (1 - p_obs x s) x R)
with B the certified bytes per eligible EB (the EBs' transactions at the
run's transaction size, from the ladder export) and s the certification
share, pinned so that the as-measured row equals the run's measured
kB/s; tx/s at the run's transaction size. Each row also gives the time at
which the voter completing the quorum has validated (p50 / p90 over EBs)
and the transactions that voter could have validated by the deadline with
the closure arriving as it did. The last line applies the rule to the
recorded times, the check that it reproduces the chain's certification.
Voters that never produced a validation record are not in the input, so
the gain is understated by their share (1.6 % of pairs on the 374 B run,
0.3 % on the 200 B run).

Second table: the EBs that still fail under each row, by the share of
their transactions the voters applied in full (mean over the EB's voters).
E_KB is kept for the command's shape and not used. A bare ratio in place
of a row scales both parts alike.
"""
import csv, json, sys
from collections import defaultdict

R, QUORUM, DEADLINE = 88.0, 39, 7.0


def parse_rows(args):
    """ROW arguments 'label:apply_ratio:reapply_ratio[:closure]', or bare ratios applied to both; the
    trailing 'closure' starts the validation at the closure's arrival instead of the 3 s mark."""
    out = []
    for x in args:
        if ":" in x:
            parts = x.split(":")
            at_closure = parts[-1] == "closure"
            if at_closure:
                parts = parts[:-1]
            label, ra, rr = ":".join(parts[:-2]), parts[-2], parts[-1]
            out.append((label, float(ra), float(rr), at_closure))
        else:
            out.append(("%.2f" % float(x), float(x), float(x), False))
    return out


def main():
    ap = [x for x in sys.argv[1:] if not x.startswith("--costs")]
    costs = None
    if "--costs" in sys.argv:
        i = sys.argv.index("--costs")
        costs = (float(sys.argv[i + 1]) * 1e-3, float(sys.argv[i + 2]) * 1e-6)
        ap = sys.argv[1:i] + sys.argv[i + 3:]
    path, ladder = ap[0], ap[1]
    levers = parse_rows(ap[3:]) or [("as measured", 1.0, 1.0, False)]
    d = json.loads(open(ladder).readline())
    p, f, tx_size = d["p_obs"], d["f_observed"], d["tx_size"]
    measured = [r for r in d["ladder"] if r["level"] == "measured"][0]
    rows = [r for r in csv.DictReader(open(path, newline="")) if r["duration_s"] and r["closure_s"]]
    rows = [r for r in rows if 0 <= float(r["duration_s"]) < 120 and -5 < float(r["closure_s"]) < 120]
    ebs = defaultdict(list)
    for r in rows:
        a, b = float(r["applied"]), float(r["reapplied"])
        c = float(r["closure_s"])
        ebs[r["eb"]].append((max(c, 3.0), float(r["duration_s"]), float(r["validated_s"]), a / max(a + b, 1), a, b, max(c, 0.0)))
    n = len(ebs)
    txs = {eb: max(x[4] + x[5] for x in recs) for eb, recs in ebs.items()}

    def scaled(rec, ra, rr, at_closure=False):
        """The record's validation time with the apply part scaled by ra and the reapply part by rr: the split
        of the recorded time between the two follows the run's costs (--costs), or ra alone without them;
        at_closure starts the validation when the closure arrived instead of at the 3 s mark."""
        start, dur, _, _, x, y, closure = rec
        if at_closure:
            start = closure
        if costs is None or ra == rr:
            return start + ra * dur
        A, Rr = costs
        return start + dur * (x * A * ra + y * Rr * rr) / max(x * A + y * Rr, 1e-9)

    def throughput(cert_txs, cert):
        """The ladder's kB/s with the EB term at the certified bytes per eligible EB (transactions x the run's
        transaction size) and the plain-RB term at the certification share; pinned to the measured figure below."""
        return f * (p * cert_txs * tx_size / 1000.0 / n + (1 - p * cert / n) * R)

    def outcome(ra, rr, at_closure=False):
        """(late records, EBs certified, their transactions, quorum times, headroom): per EB the time at
        which the QUORUM-th voter has validated, and the closure transactions that voter could have
        validated by the deadline with the closure arriving as it did."""
        late = cert = 0
        tx = 0
        qt, room = [], []
        for eb, recs in ebs.items():
            times = sorted(scaled(rec, ra, rr, at_closure) for rec in recs)
            v = sum(1 for t in times if t <= DEADLINE)
            late += len(recs) - v
            if v >= QUORUM:
                cert += 1
                tx += txs[eb]
            if len(times) >= QUORUM:
                i = QUORUM - 1
                t = times[i]
                start = sorted(rec[6] if at_closure else rec[0] for rec in recs)[i]
                qt.append(t)
                if t > start:
                    room.append(txs[eb] * (DEADLINE - start) / (t - start))
        return late, cert, tx, qt, room

    def pct(v, p):
        v = sorted(v)
        return v[int((len(v) - 1) * p)] if v else float("nan")

    late0, cert0, tx0, _, _ = outcome(1.0, 1.0)
    pin = measured["kbs"] / throughput(tx0, cert0)
    print("EBs with records %s, records %s, quorum %d voters%s. Throughput by the ladder's formula with the EB term at the certified bytes (transactions x %.0f B) "
          "and the plain-RB term at the certification share, pinned to the run's measured %.1f kB/s and %.1f tx/s." % (
              "{:,}".format(n), "{:,}".format(len(rows)), QUORUM,
              "; the run's costs per applied / reapplied transaction %.2f ms / %.0f us split each record's time between the two operations" % (costs[0] * 1e3, costs[1] * 1e6) if costs else "",
              tx_size, measured["kbs"], measured["tps"]))
    print()
    print("| voters' speed | apply, reapply relative to the run's hosts | late votes | EBs certified | certification | kB/s | tx/s | quorum voter validated at, s: p50 / p90 | transactions that voter validates by the deadline, median |")
    print("|---|---|---|---|---|---|---|---|---|")
    for label, ra, rr, at_closure in levers:
        late, cert, tx, qt, room = outcome(ra, rr, at_closure)
        kb = pin * throughput(tx, cert)
        print("| %s | %.2f, %.2f | %.1f %% | %s | %.1f %% | %.1f | %.1f | %.2f / %.2f | %s |" % (
            label, ra, rr, 100.0 * late / len(rows), "{:,}".format(cert), 100.0 * cert / n, kb, kb * 1000.0 / tx_size,
            pct(qt, .5), pct(qt, .9), "{:,}".format(int(round(pct(room, .5), -2)))))
    late = sum(1 for r in rows if float(r["validated_s"]) > DEADLINE)
    cert = sum(1 for recs in ebs.values() if sum(1 for x in recs if x[2] <= DEADLINE) >= QUORUM)
    print()
    print("As recorded: %.1f %% of the votes late, %s EBs (%.1f %%) with %d or more voters validated by 7 s." % (100.0 * late / len(rows), "{:,}".format(cert), 100.0 * cert / n, QUORUM))
    binof = lambda s: "under 30 %" if s < .3 else "30 to 40 %" if s < .4 else "40 to 50 %" if s < .5 else "50 to 60 %" if s < .6 else "60 to 70 %" if s < .7 else "70 % and over"
    order = ["under 30 %", "30 to 40 %", "40 to 50 %", "50 to 60 %", "60 to 70 %", "70 % and over"]
    print()
    print("The quorum voter is the one whose validation completes the quorum (the %d-th earliest per EB); its closure start is the %d-th earliest start. "
          "The transactions it validates by the deadline are the EB's scaled by (deadline - start) / (validated - start), the closure arriving as it did." % (QUORUM, QUORUM))
    tot, fails = defaultdict(int), {l[0]: defaultdict(int) for l in levers}
    for recs in ebs.values():
        b = binof(sum(x[3] for x in recs) / len(recs))
        tot[b] += 1
        for label, ra, rr, at_closure in levers:
            if sum(1 for rec in recs if scaled(rec, ra, rr, at_closure) <= DEADLINE) < QUORUM:
                fails[label][b] += 1
    print()
    print("| share of the EB's transactions the voters applied in full | EBs | " + " | ".join("fail: %s" % l[0] for l in levers) + " |")
    print("|---|---|" + "---|" * len(levers))
    for b in order:
        if tot[b]:
            print("| %s | %d | %s |" % (b, tot[b], " | ".join("%.0f %%" % (100.0 * fails[l[0]][b] / tot[b]) for l in levers)))


if __name__ == "__main__":
    main()
