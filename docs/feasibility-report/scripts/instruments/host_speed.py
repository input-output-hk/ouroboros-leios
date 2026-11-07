#!/usr/bin/env python3
"""Certification and throughput of a cluster run on faster hosts, and the
EBs that fail by the share of their transactions the voters applied in full
(report sections 6.2 and 8), from the run's per-(voter, EB) validation
records (validation_pairs.csv) and its ladder export.

Per record: validated' = max(closure, 3 s) + ratio x duration, where
duration is the recorded validation time after that start and ratio the
host's cost per transaction relative to the run's hosts (c5d.2xlarge:
ratio 1; the testnet measured the c6id hosts at about 0.8 and the c8id
hosts at 0.5 to 0.7 of the c5d cost on the same work). A voter votes if
validated' <= 7 s; an EB certifies with QUORUM voters or more; the
certification rate goes through the ladder's formula
    kB/s = f_obs x (p_obs s E + (1 - p_obs s) R)
scaled so that the ratio-1 row equals the measured throughput. The last
line applies the same rule to the recorded times, the check that the rule
reproduces the chain's certification. Voters that never produced a
validation record are not in the input, so the gain is understated by
their share (1.6 % of pairs on the 374 B run, 0.3 % on the 200 B run).

Second table: the EBs that still fail at each ratio, by the share of their
transactions the voters applied in full, i.e. had not validated before the
closure arrived (applied share, mean over the EB's voters).

    host_speed.py validation_pairs.csv ladder.jsonl E_KB [ratio ...] > host_speed.md

E_KB is the run's typical certified closure in kB (the median certified
closure of sizes.md); p_obs, f_obs and the measured kB/s come from the
ladder export.
"""
import csv, json, sys
from collections import defaultdict

R, QUORUM, DEADLINE = 88.0, 39, 7.0


def main():
    path, ladder, E = sys.argv[1], sys.argv[2], float(sys.argv[3])
    ratios = [float(x) for x in sys.argv[4:]] or [1.0, 0.9, 0.8, 0.7, 0.6, 0.5, 0.4]
    d = json.loads(open(ladder).readline())
    p, f = d["p_obs"], d["f_observed"]
    measured = [r for r in d["ladder"] if r["level"] == "measured"][0]["kbs"]
    rows = [r for r in csv.DictReader(open(path, newline="")) if r["duration_s"] and r["closure_s"]]
    rows = [r for r in rows if 0 <= float(r["duration_s"]) < 120 and -5 < float(r["closure_s"]) < 120]
    ebs = defaultdict(list)
    for r in rows:
        a, b = float(r["applied"]), float(r["reapplied"])
        ebs[r["eb"]].append((max(float(r["closure_s"]), 3.0), float(r["duration_s"]), float(r["validated_s"]), a / max(a + b, 1)))
    n = len(ebs)
    kbs = lambda s: f * (p * s * E + (1 - p * s) * R)
    ceiling, base = kbs(1.0), None
    print("EBs with records %s, records %s, quorum %d voters, E %.0f kB, p observed %.3f, f observed %.4f per s, R %.0f kB." % ("{:,}".format(n), "{:,}".format(len(rows)), QUORUM, E, p, f, R))
    print()
    print("| host speed, cost relative to the run's hosts | late votes | votes per EB | certified | certification | kB/s | of the ceiling |")
    print("|---|---|---|---|---|---|---|")
    for ratio in ratios:
        late = votes = cert = 0
        for recs in ebs.values():
            v = sum(1 for start, dur, _, _ in recs if start + ratio * dur <= DEADLINE)
            late += len(recs) - v
            votes += v
            cert += v >= QUORUM
        s = cert / n
        base = base or kbs(s)
        print("| %.2f | %.1f %% | %.1f | %s | %.1f %% | %.1f | %.0f %% |" % (ratio, 100.0 * late / len(rows), votes / n, "{:,}".format(cert), 100 * s, measured * kbs(s) / base, 100 * kbs(s) / ceiling))
    late = sum(1 for r in rows if float(r["validated_s"]) > DEADLINE)
    cert = sum(1 for recs in ebs.values() if sum(1 for _, _, v, _ in recs if v <= DEADLINE) >= QUORUM)
    print()
    print("Ceiling at full certification %.1f kB/s. As recorded: %.1f %% of the votes late, %s EBs (%.1f %%) with %d or more voters validated by 7 s." % (measured * ceiling / base, 100.0 * late / len(rows), "{:,}".format(cert), 100.0 * cert / n, QUORUM))
    binof = lambda s: "under 30 %" if s < .3 else "30 to 40 %" if s < .4 else "40 to 50 %" if s < .5 else "50 to 60 %" if s < .6 else "60 to 70 %" if s < .7 else "70 % and over"
    order = ["under 30 %", "30 to 40 %", "40 to 50 %", "50 to 60 %", "60 to 70 %", "70 % and over"]
    tot, fails = defaultdict(int), {r: defaultdict(int) for r in ratios}
    for recs in ebs.values():
        b = binof(sum(x[3] for x in recs) / len(recs))
        tot[b] += 1
        for ratio in ratios:
            if sum(1 for start, dur, _, _ in recs if start + ratio * dur <= DEADLINE) < QUORUM:
                fails[ratio][b] += 1
    print()
    print("| share of the EB's transactions the voters applied in full | EBs | " + " | ".join("fail at %.1f" % r for r in ratios) + " |")
    print("|---|---|" + "---|" * len(ratios))
    for b in order:
        if tot[b]:
            print("| %s | %d | %s |" % (b, tot[b], " | ".join("%.0f %%" % (100.0 * fails[r][b] / tot[b]) for r in ratios)))


if __name__ == "__main__":
    main()
