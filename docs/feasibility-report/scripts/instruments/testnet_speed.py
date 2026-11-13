#!/usr/bin/env python3
"""Certification and throughput of a testnet window if the slow voters ran at
the rate of a measured host class (report section 8): a repricing of the
window's per-(node, EB) validation records with each voter's validation
time scaled to the class's cost per transaction, the vote rule and a
stake-weighted quorum applied to the result.

    testnet_speed.py validation_pairs.csv --voters voters.csv --windows windows-KEY.txt
        --ebs tally_quorum_ebs.csv --hosts data/hosts.csv --ladder ladder.jsonl
        --costs current:A_OLD:A_CHAINED:R "two older:..." "three older:..."
        [--fleet closure_fleet_per_eb.csv] [--fixed 0.02] [--slot0 1792281600] [--deadline 7]
        [--top 1 2 3 5 10 20] > host_speed.md

Two kinds of rows. The hardware row keeps the closures as they were and
scales the recorded time of every voter slower than the current
generation: per voter node, its cost per reapplied transaction is read as
validation_shape.py reads it (the median of the validation time over the
transaction count on the records in which the node applied nothing, 10 or
more), a host class's cost is the median over its hosts (data/hosts.csv, by
generation), and the node's ratio is class cost / own cost, on the reapply
cost because it does not depend on where the closure's inputs come from
and so reads the hardware alone (section 7.2); a node without a reapply
reading uses its apply cost, else is not moved (counted); faster nodes keep
their own time. Per record validated' = max(closure, 3 s) + ratio x
duration, with duration the recorded validation time after that start.

The pessimistic rows rebuild every voter's time from the record's counts
as if every closure were old-input and every voter ran a given host class:
validated' = max(closure, 3 s) + fixed + applied x A + reapplied x R, with
A the class's cost per applied transaction on old-input closures and R its
cost per reapplied transaction (--costs, from the report's tables; the
fixed term is the recorded validation time of the smallest EBs). The same
rows are printed again with A the class's cost on chained closures: the
loop fix, what the voters would pay if the per-transaction pass over the
closure's input table (section 7.3) were removed, the apply cost then
falling to the level the chained closures already show.

A pool votes if the earliest validated' among its nodes is within the
deadline; the pool's weight is its committee seats in the EB's window
(voters.csv, normalised to the window).

The reporting voters hold 61 to 75 % of the committee's weight, so the
quorum cannot be read as 75 % of the recorded weight. The rule is
calibrated: on the recorded times, the threshold on the reporting weight
that best reproduces the chain's certification per EB (tally_quorum_ebs.csv)
is found, its agreement reported, and the same threshold is applied to the
repricings; the voters that send no logs are thereby assumed to vote as they
did. Throughput is the window's measured kB/s and tx/s (ladder.jsonl)
scaled by the transactions of the EBs the rule certifies, each EB counted
by its transaction count, so an EB size that certifies only after the
speed-up enters at its size.

Second table, for the current-generation target: the recovery when only
the k heaviest slow voters are moved, k from --top, which says how many
voters the recovery depends on.
"""
import argparse, csv, json
from collections import defaultdict
from datetime import datetime, timezone

GEN_LABEL = {"current": "current generation (c8id, r8id)", "two older": "two generations older (c6id)", "three older": "three generations older (c5d)"}
GEN_ORDER = ["current", "two older", "three older"]


def med(v):
    v = sorted(v)
    return v[len(v) // 2] if v else None


def parse_time(s):
    s = s.strip()
    if len(s) == 16:
        s += ":00"
    return datetime.fromisoformat(s).replace(tzinfo=timezone.utc).timestamp()


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("pairs")
    ap.add_argument("--voters", required=True)
    ap.add_argument("--windows", required=True)
    ap.add_argument("--ebs", required=True)
    ap.add_argument("--hosts", required=True)
    ap.add_argument("--ladder", required=True)
    ap.add_argument("--fleet", help="closure_fleet_per_eb.csv of the window, for the arrival line on the EBs still failing")
    ap.add_argument("--slot0", type=int, default=1792281600)
    ap.add_argument("--deadline", type=float, default=7.0)
    ap.add_argument("--costs", nargs="+", required=True, metavar="GEN:APPLY_OLD_MS:APPLY_CHAINED_MS:REAPPLY_US",
                    help="per host class (current, 'two older', 'three older'; quote the name) the cost per applied transaction on old-input "
                         "closures, the same on chained closures, and the cost per reapplied transaction, from the report's tables")
    ap.add_argument("--fixed", type=float, default=0.02, help="the per-EB fixed term of the rebuilt time, seconds")
    ap.add_argument("--top", type=int, nargs="*", default=[1, 2, 3, 5, 10, 20])
    ap.add_argument("--min-records", type=int, default=10)
    a = ap.parse_args()
    given = {}
    for c in a.costs:
        g, ao, ac, rr = c.rsplit(":", 3)
        given[g] = (float(ao) * 1e-3, float(ac) * 1e-3, float(rr) * 1e-6)

    # windows (1-based index as voters.csv's win column) and the committee weights per window, normalised
    wins = [(parse_time(l.split()[0]), parse_time(l.split()[1])) for l in open(a.windows) if l.strip() and not l.startswith("#")]
    weight = defaultdict(lambda: defaultdict(float))
    for r in csv.DictReader(open(a.voters, newline="")):
        weight[int(r["win"])][r["pool_id"]] += float(r["weight"])
    for w in weight:
        tot = sum(weight[w].values())
        for p in weight[w]:
            weight[w][p] /= tot

    def win_of(slot):
        t = a.slot0 + slot
        for i, (s, e) in enumerate(wins, 1):
            if s <= t < e:
                return i
        return None

    # the EBs of the window and the chain's verdict
    ebs = {}
    for r in csv.DictReader(open(a.ebs, newline="")):
        w = win_of(int(r["slot"]))
        if w is not None:
            ebs[r["eb"]] = (w, r["certified"] == "1")
    hosts = {r["agent"]: r for r in csv.DictReader(open(a.hosts, newline=""))}

    # records per node
    recs = defaultdict(list)
    for r in csv.DictReader(open(a.pairs, newline="")):
        if not r["duration_s"] or not r["closure_s"] or r["eb"] not in ebs:
            continue
        d, c, v = float(r["duration_s"]), float(r["closure_s"]), float(r["validated_s"])
        x, y = float(r["applied"]), float(r["reapplied"])
        if not (0 <= d < 120) or not (-5 < c < 120) or x + y < 1:
            continue
        recs[r["agent"]].append((r["eb"], max(c, 3.0), d, v, x, y, r["pool"]))

    # per node costs
    cost = {}
    for ag, rs in recs.items():
        re_ = [d / (x + y) for _, _, d, _, x, y, _ in rs if x == 0]
        rg = med(re_) if len(re_) >= a.min_records else None
        app = [(d - y * rg) / x for _, _, d, _, x, y, _ in rs if x / (x + y) >= 0.5] if rg is not None else []
        ag_ = med(app) if len(app) >= a.min_records else None
        cost[ag] = (ag_, rg)
    cls = {}
    for g in GEN_ORDER:
        ags = [ag for ag, h in hosts.items() if h["generation"] == g and ag in cost]
        cls[g] = (med([cost[ag][0] for ag in ags if cost[ag][0] is not None]), med([cost[ag][1] for ag in ags if cost[ag][1] is not None]))

    def ratio_for(g):
        """Per node the ratio to the class g (<= 1), and the nodes not moved for lack of a reading."""
        ca, cr = cls[g]
        out, unmoved = {}, []
        for ag, (na, nr) in cost.items():
            if nr is not None and cr is not None:
                out[ag] = min(1.0, cr / nr)
            elif na is not None and ca is not None:
                out[ag] = min(1.0, ca / na)
            else:
                out[ag] = 1.0
                unmoved.append(ag)
        return out, unmoved

    pools = {ag: rs[0][6] for ag, rs in recs.items()}
    nrec = sum(len(rs) for rs in recs.values())

    def replay(ratio, rebuild=None):
        """Per EB the reporting weight that votes in time and the late records: the recorded time scaled by
        ratio per node, or, with rebuild = (apply cost, reapply cost), the time rebuilt from the counts.
        Also per EB the pools' earliest (start, validated') pairs, for the quorum voter's reading."""
        first = defaultdict(dict)  # eb -> pool -> (earliest validated', its start)
        late = 0
        for ag, rs in recs.items():
            r = ratio[ag] if isinstance(ratio, dict) else ratio
            for eb, start, d, _, x, y, pool in rs:
                t = start + (a.fixed + x * rebuild[0] + y * rebuild[1] if rebuild else r * d)
                late += t > a.deadline
                if t < first[eb].get(pool, (1e9, 0))[0]:
                    first[eb][pool] = (t, start)
        w = {}
        for eb, (win, _) in ebs.items():
            w[eb] = sum(weight[win].get(pool, 0.0) for pool, (t, _) in first.get(eb, {}).items() if t <= a.deadline)
        replay.first = first
        return w, late

    def quorum_reading(first):
        """Per EB the time at which the reporting weight reaches the calibrated threshold T (the quorum voter)
        and the closure transactions that voter validates by the deadline with the closure arriving as it did:
        (quorum times, headroom)."""
        qt, room = [], []
        for eb, (win, _) in ebs.items():
            acc = 0.0
            for pool, (t, start) in sorted(first.get(eb, {}).items(), key=lambda kv: kv[1][0]):
                acc += weight[win].get(pool, 0.0)
                if acc >= T:
                    qt.append(t)
                    if t > start:
                        room.append(txs.get(eb, 0) * (a.deadline - start) / (t - start))
                    break
        return qt, room

    def pct(v, p):
        v = sorted(v)
        return v[int((len(v) - 1) * p)] if v else float("nan")

    base, late0 = replay(1.0)
    # calibration: the threshold on the reporting weight that best reproduces the chain's verdict
    cands = sorted(set(base.values()))
    best = None
    for i, t in enumerate(cands):
        agree = sum((base[eb] >= t) == cert for eb, (_, cert) in ebs.items())
        if best is None or agree > best[0]:
            best = (agree, t)
    agree, T = best
    n = len(ebs)
    chain_cert = sum(cert for _, cert in ebs.values())
    txs = {}
    for rs in recs.values():
        for eb, _, _, _, x, y, _ in rs:
            txs[eb] = max(txs.get(eb, 0), x + y)
    d = json.loads(open(a.ladder).readline())
    measured = [r for r in d["ladder"] if r["level"] == "measured"][0]
    kbs0, tps0 = measured["kbs"], measured["tps"]
    p_obs, f_obs, tx_size, R = d["p_obs"], d["f_observed"], d["tx_size"], 88.0

    def throughput(cert_txs, cert):
        """The ladder's kB/s with the EB term at the certified bytes per EB and the plain-RB term at the
        certification share; pinned to the measured figure by the caller."""
        return f_obs * (p_obs * cert_txs * tx_size / 1000.0 / n + (1 - p_obs * cert / n) * R)

    def outcome(w):
        """(EBs certified, their transactions) under the calibrated rule."""
        cert = [eb for eb in ebs if w[eb] >= T]
        return len(cert), sum(txs.get(eb, 0) for eb in cert)

    cert0, tx_rec = outcome(base)
    first0 = replay.first
    pin = kbs0 / throughput(tx_rec, cert0)
    ratio_cur, unmoved = ratio_for("current")
    w_hw, late_hw = replay(ratio_cur)
    first_hw = replay.first
    moved = sum(1 for r in ratio_cur.values() if r < 1)

    def cell(w, first):
        c, tx = outcome(w)
        qt, room = quorum_reading(first)
        kb = pin * throughput(tx, c)
        return "%s | %.1f %% | %.1f | %.1f | %.2f / %.2f | %s" % ("{:,}".format(c), 100.0 * c / n, kb, kb * 1000.0 / tx_size,
                                                                 pct(qt, .5), pct(qt, .9), "{:,}".format(int(round(pct(room, .5), -2))))

    fleet = {}
    if a.fleet:
        for r in csv.DictReader(open(a.fleet, newline="")):
            fleet[r["eb"]] = float(r["t90"]) if r["t90"] else 1e9

    def arrival(w):
        """Of the EBs the rule does not certify, by the closure's arrival at 90 % of the reporting nodes
        (closure_fleet_per_eb.csv): by the deadline, after it, or never."""
        in_time = after = never = 0
        for eb in ebs:
            if w[eb] >= T:
                continue
            t90 = fleet.get(eb, 1e9)
            if t90 >= 1e8:
                never += 1
            elif t90 <= a.deadline:
                in_time += 1
            else:
                after += 1
        return in_time, after, never

    print("EBs %s, of which the chain certified %s; validation records %s from %d nodes (%d pools); deadline %.0f s after the EB slot. "
          "Calibrated threshold on the reporting weight %.3f (the reporting voters hold %.0f to %.0f %% of the committee): the rule agrees with the chain on %s EBs (%.1f %%) and certifies %s. "
          "Hardware factors from the hosts' measured cost per reapplied transaction, by class: %s; %d voters slower than the current generation, %d without a reading. "
          "Rebuilt times: %.0f ms per EB plus the applied transactions at the class's cost on old-input closures and the reapplied ones at its reapply cost, "
          "or the applied ones at the class's cost on chained closures (the loop's cost removed); costs per class (ms / ms / us): %s. "
          "Throughput scaled from the window's measured %.1f kB/s and %.1f tx/s by the transactions of the EBs certified." % (
              "{:,}".format(n), "{:,}".format(chain_cert), "{:,}".format(nrec), len(recs), len(set(pools.values())), a.deadline, T,
              100 * min(sum(weight[w].get(p, 0) for p in set(pools.values())) for w in weight), 100 * max(sum(weight[w].get(p, 0) for p in set(pools.values())) for w in weight),
              "{:,}".format(agree), 100.0 * agree / n, "{:,}".format(cert0),
              "; ".join("%s %s us" % (g, "%.0f" % (cls[g][1] * 1e6) if cls[g][1] else "-") for g in GEN_ORDER), moved, len(unmoved), a.fixed * 1e3,
              "; ".join("%s %.2f / %.2f / %.0f" % (g, given[g][0] * 1e3, given[g][1] * 1e3, given[g][2] * 1e6) for g in GEN_ORDER if g in given), kbs0, tps0))
    print()
    head = "EBs certified | certification | kB/s | tx/s | quorum voter validated at, s: p50 / p90 | transactions that voter validates by the deadline, median"
    print("| voters' speed and closures | %s | with the loop's cost removed: %s |" % (head, head))
    print("|---|" + "---|" * 12)
    print("| as recorded | %s | - | - | - | - | - | - |" % cell(base, first0))
    print("| closures as they were, every voter at least at the current generation | %s | - | - | - | - | - | - |" % cell(w_hw, first_hw))
    arrival_line = None
    for g in GEN_ORDER:
        if g not in given:
            continue
        ao, ac, rr = given[g]
        w1, _ = replay(None, (ao, rr))
        f1 = replay.first
        w2, _ = replay(None, (ac, rr))
        f2 = replay.first
        print("| every closure old-input, every voter at the %s | %s | %s |" % (GEN_LABEL[g], cell(w1, f1), cell(w2, f2)))
        if g == "current" and fleet:
            arrival_line = (n - outcome(w2)[0],) + arrival(w2)
    print()
    print("The quorum voter is the one whose vote brings the reporting weight to the calibrated threshold; its closure start is its own. "
          "The transactions it validates by the deadline are the EB's scaled by (deadline - start) / (validated - start), the closure arriving as it did. "
          "Throughput by the ladder's formula with the EB term at the certified bytes (transactions x %.0f B) and the plain-RB term at the certification share, pinned to the measured figure." % tx_size)
    if arrival_line:
        print()
        print("Of the %s EBs not certified with the loop's cost removed on current-generation hosts, %s had the closure at 90 %% of the reporting nodes by the deadline, "
              "%s had it there only after the deadline, and %s never had it there (closure_fleet_per_eb.csv)." % tuple("{:,}".format(x) for x in arrival_line))
    print()
    # who moves the needle: the current-generation target, the k heaviest slow voters only
    ratio = ratio_cur
    pw = defaultdict(float)
    for ag, r in ratio.items():
        if r < 1:
            p = pools[ag]
            pw[p] = max(pw[p], sum(weight[w].get(p, 0) for w in weight) / len(weight))
    order = sorted(pw, key=lambda p: -pw[p])
    print("| slow voters moved to the current generation, heaviest first | their weight | EBs certified | certification |")
    print("|---|---|---|---|")
    for k in [k for k in a.top if k < len(order)] + [len(order)]:
        chosen = set(order[:k])
        part = {ag: (r if pools[ag] in chosen else 1.0) for ag, r in ratio.items()}
        w, _ = replay(part)
        cert = sum(1 for eb in ebs if w[eb] >= T)
        print("| %s | %.0f %% | %s | %.1f %% |" % ("all %d" % k if k == len(order) else k, 100 * sum(pw[p] for p in chosen), "{:,}".format(cert), 100.0 * cert / n))


if __name__ == "__main__":
    main()
