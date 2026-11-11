#!/usr/bin/env python3
"""One testnet host running the voting-loop change against its control
(report section 9.2), from the archived Loki pull of the two hosts' voting
events: the cost per applied and per reapplied transaction on each host,
the validation time by applied count, and the votes each host cast or
missed, printed as Markdown.

    loop_hosts.py [--data DIR] [--pulls DIR] [--hosts FILE] [--changed HOST] [--control HOST]
                  [--from-slot N] [--to-slot N] > outputs/loop-fix-pir7/loop_hosts.md

--data       the data folder (default: the parent of this repository)
--pulls      the pull folder with one <agent>_voting.jsonl per host (default
             grafana/archive/loki/loop-fix-pir7 under --data; DATA.md)
--hosts      the hosts table (default data/hosts.csv in this repository),
             which maps a host label to its agent, the pull file's stem
--changed    the host on the changed build, by label (default PIR7), or
             LABEL=AGENT where the hosts table does not carry the agent
             (the public copy numbers the agents)
--control    the host on the unchanged build, the same (default PIR9)
--from-slot, --to-slot   the EB slots read (default 1,899,900 on, the changed
             host's restart, to the end of the pull)

Per host and EB the records are read as validation_pairs.sql reads them: the
closure's arrival (closureAgeSeconds of BlockTxsAcquired), the validated
time (EbValidated's timestamp less the slot's time, slot 0 at 1792281600),
the validation time after the later of the closure and the 3 s mark, the
applied and reapplied counts, the transaction count (BodyHits) and the
vote's outcome (voted unless NotVoted, by reason). Each host is read on
the EBs it validated.

Table 9.1: per host the least-squares fit of the validation time to the
applied and reapplied counts with a constant (the apply and reapply cost per
transaction), and the median validation time per applied transaction on the
EBs applying 500 or more with fewer reapplied than a third of that. Table
9.2: per host the validation time by its own applied count (EBs, p50 / p90,
and the median validation time over the applied count), EBs applying 100
or more. Then the votes: scheduled (the EBs the host's chain tip still
announced at the vote), cast, missed, and for the missed ones whether the
closure arrived after the deadline or the validation ran past it, with the
largest validation on each host.
"""
import argparse
import json
import os
import statistics as st
from collections import defaultdict

SLOT0 = 1792281600
BINS = [(100, 500, "100 to 500"), (500, 1000, "500 to 1,000"), (1000, 2000, "1,000 to 2,000"), (2000, 10**9, "2,000 and up")]


def q(v, p):
    v = sorted(v)
    return v[int((len(v) - 1) * p)] if v else float("nan")


def fit(rows):
    """Least squares of t = a x + r y + c over (x, y, t): (a, r, c)."""
    n = len(rows)
    sx = sum(x for x, _, _ in rows); sy = sum(y for _, y, _ in rows); stt = sum(t for _, _, t in rows)
    sxx = sum(x * x for x, _, _ in rows); syy = sum(y * y for _, y, _ in rows); sxy = sum(x * y for x, y, _ in rows)
    sxt = sum(x * t for x, _, t in rows); syt = sum(y * t for _, y, t in rows)
    # normal equations [[sxx, sxy, sx], [sxy, syy, sy], [sx, sy, n]] . [a, r, c] = [sxt, syt, stt]
    m = [[sxx, sxy, sx, sxt], [sxy, syy, sy, syt], [sx, sy, n, stt]]
    for i in range(3):
        p = max(range(i, 3), key=lambda k: abs(m[k][i]))
        m[i], m[p] = m[p], m[i]
        for k in range(3):
            if k != i:
                f = m[k][i] / m[i][i]
                m[k] = [a - f * b for a, b in zip(m[k], m[i])]
    return tuple(m[i][3] / m[i][i] for i in range(3))


def read(path, lo, hi):
    """Per EB of the host: dict with slot, txs, closure, validated, applied, reapplied, outcome."""
    ebs = defaultdict(dict)
    for line in open(path):
        d = json.loads(line)
        data = d["data"]
        eb, slot = data.get("ebHash"), data.get("ebSlot")
        if eb is None or slot is None or not (lo <= slot < hi):
            continue
        r = ebs[eb]
        r["slot"] = slot
        ns = d["ns"].rsplit(".", 1)[-1]
        t = d["ts"] / 1e9 - (SLOT0 + slot)
        if ns == "BodyHits":
            r["txs"] = max(r.get("txs", 0), data["txsInEb"])
        elif ns == "BlockTxsAcquired":
            r["closure"] = min(r.get("closure", 1e9), data.get("closureAgeSeconds", t))
        elif ns == "EbValidated" and "validated" not in r:
            r["validated"], r["applied"], r["reapplied"] = t, data["applied"], data["reapplied"]
        elif ns == "NotVoted":
            r["outcome"] = data.get("reason", "notVoted")
        elif ns == "VoteScheduled":
            r.setdefault("scheduled", True)
    return ebs


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    here = os.path.dirname(os.path.abspath(__file__))
    ap.add_argument("--data", dest="root", default=os.path.normpath(os.path.join(here, "..", "..", "..")))
    ap.add_argument("--pulls", default="grafana/archive/loki/loop-fix-pir7")
    ap.add_argument("--hosts", default=os.path.normpath(os.path.join(here, "..", "..", "data", "hosts.csv")))
    ap.add_argument("--changed", default="PIR7")
    ap.add_argument("--control", default="PIR9")
    ap.add_argument("--from-slot", type=int, default=1899900)
    ap.add_argument("--to-slot", type=int, default=10**9)
    ap.add_argument("--deadline", type=float, default=7.0)
    a = ap.parse_args()
    pulls = a.pulls if os.path.isabs(a.pulls) else os.path.join(a.root, a.pulls)
    import csv
    agent_of = {r["host"]: r["agent"] for r in csv.DictReader(open(a.hosts, newline=""))}
    hosts, agents = [], {}
    for label, spec in (("the changed host", a.changed), ("the control", a.control)):
        host, _, agent = spec.partition("=")
        hosts.append((label, host))
        agents[host] = agent or agent_of[host]
    a.changed, a.control = hosts[0][1], hosts[1][1]
    data = {label: read(os.path.join(pulls, "%s_voting.jsonl" % agents[host]), a.from_slot, a.to_slot) for label, host in hosts}
    for label, _ in hosts:
        for eb, r in data[label].items():
            if "validated" in r and "closure" in r:
                r["duration"] = r["validated"] - max(r["closure"], 3.0)
    val = {label: sorted(eb for eb, r in data[label].items() if "duration" in r) for label, _ in hosts}
    slots = [r["slot"] for label, _ in hosts for r in data[label].values()]
    print("EBs announced in the window %d, slots %s to %s; validated by %s %d, by %s %d (%s).\n" % (
        len(set(eb for label, _ in hosts for eb in data[label])), "{:,}".format(min(slots)), "{:,}".format(max(slots)),
        a.changed, len(val[hosts[0][0]]), a.control, len(val[hosts[1][0]]), a.pulls))

    t0 = SLOT0 + min(slots)
    t1 = SLOT0 + max(slots)
    import datetime as dt
    f = lambda t: dt.datetime.fromtimestamp(t, dt.timezone.utc)
    print("| host, %s to %s UTC | EBs validated | apply cost per transaction | reapply cost per transaction | EBs applying 500 or more with few reapplies: validation per applied transaction, p50 |" % (
        f(t0).strftime("%Y-%m-%d %H:%M"), f(t1).strftime("%m-%d %H:%M")))
    print("|---|---:|---:|---:|---:|")
    for label, _ in hosts:
        rows = [(data[label][eb]["applied"], data[label][eb]["reapplied"], data[label][eb]["duration"]) for eb in val[label]]
        ac, rc, _ = fit(rows)
        dom = [t / x for x, y, t in rows if x >= 500 and y < x / 3]
        print("| %s | %d | %.2f ms | %.2f ms | %.2f ms |" % (label, len(rows), ac * 1e3, rc * 1e3, st.median(dom) * 1e3 if dom else float("nan")))

    print("\n| transactions applied in the EB | %s |" % " | ".join(
        "%s: EBs | validation p50 / p90 | per applied transaction, p50" % label for label, _ in hosts))
    print("|---|" + "---:|---:|---:|" * len(hosts))
    for lo, hi, lab in BINS:
        cells = []
        for label, _ in hosts:
            ebs = [eb for eb in val[label] if lo <= data[label][eb]["applied"] < hi]
            d = [data[label][eb]["duration"] for eb in ebs]
            per = [data[label][eb]["duration"] / data[label][eb]["applied"] for eb in ebs]
            cells.append("%d | %.2f / %.2f s | %.2f ms" % (len(ebs), q(d, .5), q(d, .9), st.median(per) * 1e3) if ebs else "0 | - | -")
        print("| %s | %s |" % (lab, " | ".join(cells)))

    print()
    for label, agent in hosts:
        d = data[label]
        sched = [eb for eb, r in d.items() if r.get("scheduled") and r.get("outcome") != "chainTipDoesNotAnnounce"]
        missed = [eb for eb in sched if d[eb].get("outcome") == "tooLate"]
        closure_late = [eb for eb in missed if d[eb].get("closure", 1e9) > a.deadline]
        val_late = [eb for eb in missed if eb not in closure_late]
        other = [eb for eb in sched if d[eb].get("outcome") not in (None, "tooLate")]
        big = max((eb for eb in d if "duration" in d[eb]), key=lambda eb: d[eb]["duration"], default=None)
        print("%s (%s): votes scheduled %d, cast %d, too late %d (closure after the deadline or never: %d, at %s s; validation past the deadline: %d, closures by %s s), other reasons %d; "
              "largest validation %.2f s on an EB of %s transactions (%s applied)." % (
                  label, agent, len(sched), len(sched) - len(missed) - len(other), len(missed), len(closure_late),
                  ", ".join("%.1f" % d[eb]["closure"] if d[eb].get("closure", 1e9) < 1e8 else "never" for eb in closure_late) or "-",
                  len(val_late), ("%.1f" % max(d[eb].get("closure", 0) for eb in val_late)) if val_late else "-", len(other),
                  d[big]["duration"], "{:,}".format(d[big].get("txs", 0)), "{:,}".format(d[big]["applied"])))


if __name__ == "__main__":
    main()
