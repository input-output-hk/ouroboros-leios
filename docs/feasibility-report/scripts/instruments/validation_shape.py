#!/usr/bin/env python3
"""The cost of validating one transaction at the vote on EBs of one size,
one transaction shape and one input provenance (report section 7): per host
class, two readings over the per-(node, EB) validation records of a window
or run (validation_pairs.csv of validation_pairs.sql /
cluster_validation_pairs.sql), restricted to EBs of one size class and, on
the testnet, to certified closures selected by the per-RB composition file
from db-sync: by transaction size (every transaction inside a band) and by
input provenance (the share of the closure's inputs that spend an output
created in the same block):

  per reapplied transaction = the median, over the records in which the node
      applied no transaction of the EB, of the validation time over the EB's
      transaction count;
  per applied transaction = the median, over the records in which the node
      applied half or more of the EB, of the validation time net of the
      reapplied transactions at the rate above, over the applied count.

Neither reading fits a line: each is a median of per-record ratios, so the
contended tail does not pull it. On one size class the two counts are
complements, so a two-rate fit is degenerate there; the readings are the
gross cost per transaction of each kind at that EB size (the per-EB fixed
part, about 10 ms on the testnet hosts, is inside them).

    validation_shape.py validation_pairs.csv [--class LO HI ...]
        [--hosts data/hosts.csv] [--shape eb_shape_dbsync.csv --chain blocks.sqlite
         [--min-size MIN --max-size MAX] [--same-block-min P] [--same-block-max P]
         [--provenance CHAINED_MIN OLD_MAX]]
        > validation_shape.md

--class  an EB size class in transactions (applied + reapplied), inclusive;
         one table per class; without it, the 500-transaction class holding
         the most distinct EBs (the cluster runs, one transaction shape)
--hosts  agent,host,deployment,instance,vcpu,generation: the hosts printed by
         class; every other node goes into the operators' quartiles row
--shape  the certified closures' composition from db-sync (one row per
         certifying RB: the minimum and maximum transaction size in bytes
         and the same-block share of the inputs) with --chain the chain
         cache mapping the certifying RB to its EB; --min-size/--max-size
         keep the EBs whose closure has every transaction between MIN and
         MAX bytes, --same-block-min/--same-block-max the EBs whose closure
         has that share (0 to 1) of its inputs spending an output of the
         same block; the filters combine
--provenance  two selections side by side in one table: the chained
         closures (same-block share >= CHAINED_MIN) and the old-input
         closures (share <= OLD_MAX), each under the size band if given;
         the operators' row is then over one node set, the nodes with
         enough EBs under both selections
The apply cost is printed in milliseconds per transaction and the reapply
cost in microseconds, the units spelled out in the table headers.
A record is one node validating one EB; the tables count them as EBs per
host. A host cell resting on fewer than 10 EBs is marked tentative; the
operators' quartiles are over the nodes with 10 or more EBs behind the
apply reading and 20 or more behind the reapply reading in the class (under
every selection printed).
"""
import argparse, csv, sqlite3
from collections import defaultdict

GEN_RANK = {"current": 0, "two older": 1, "three older": 2}


def med(v):
    v = sorted(v)
    return v[len(v) // 2] if v else None


def q(v, p):
    return sorted(v)[int((len(v) - 1) * p)]


def rng(xs, fmt):
    if not xs:
        return "-"
    lo, hi = fmt % min(xs), fmt % max(xs)
    return lo if lo == hi else lo + " to " + hi


def readings(rs, reapply_share, apply_share):
    """(records, apply records, apply cost, reapply records, reapply cost) of one node's records."""
    re_ = [r[0] / r[3] for r in rs if r[1] / r[3] <= reapply_share]
    rg = med(re_)
    app = [(r[0] - r[2] * rg) / r[1] for r in rs if r[1] / r[3] >= apply_share] if rg is not None else []
    return (len(rs), len(app), med(app), len(re_), rg)


def cells(v, min_records):
    """The apply and reapply cells of one host class from its hosts' readings."""
    av = [x[2] * 1e3 for x in v if x[2] is not None]
    bv = [x[4] * 1e6 for x in v if x[4] is not None]
    return ("%s (%s)%s" % (rng(av, "%.2f"), rng([x[1] for x in v], "%d"), " tentative" if any(x[1] < min_records for x in v) else ""),
            "%s (%s)%s" % (rng(bv, "%.0f"), rng([x[3] for x in v], "%d"), " tentative" if any(x[3] < min_records for x in v) else ""))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("pairs")
    ap.add_argument("--class", dest="classes", nargs=2, type=int, action="append", metavar=("LO", "HI"))
    ap.add_argument("--hosts")
    ap.add_argument("--shape")
    ap.add_argument("--chain")
    ap.add_argument("--min-size", type=float)
    ap.add_argument("--max-size", type=float)
    ap.add_argument("--same-block-min", type=float)
    ap.add_argument("--same-block-max", type=float)
    ap.add_argument("--provenance", nargs=2, type=float, metavar=("CHAINED_MIN", "OLD_MAX"))
    ap.add_argument("--reapply-share", type=float, default=0.0)
    ap.add_argument("--apply-share", type=float, default=0.5)
    ap.add_argument("--min-records", type=int, default=10)
    a = ap.parse_args()
    hosts = {r["agent"]: r for r in csv.DictReader(open(a.hosts, newline=""))} if a.hosts else {}

    # the selections: a list of (name, description, keep set or None)
    rows_shape = []
    if a.shape:
        con = sqlite3.connect(a.chain)
        eb_of = dict(con.execute("select c.block_no, p.eb_announcement_hash from block c join block p on p.block_no = c.block_no - 1 where c.has_leios_cert = 1"))
        for r in csv.DictReader(open(a.shape, newline="")):
            if int(r["block_no"]) in eb_of and r["txs"] and int(r["txs"]) > 0:
                rows_shape.append((eb_of[int(r["block_no"])], float(r["min_size"]), float(r["max_size"]), float(r["same_block"]) if r["same_block"] else None))

    def select(sb_min, sb_max):
        keep, desc = set(), []
        for eb, mn, mx, sb in rows_shape:
            if a.min_size is not None and not (a.min_size <= mn and mx <= a.max_size):
                continue
            if sb_min is not None and not (sb is not None and sb >= sb_min):
                continue
            if sb_max is not None and not (sb is not None and sb <= sb_max):
                continue
            keep.add(eb)
        if a.min_size is not None:
            desc.append("whose transactions are all of %s to %s B" % ("{:,}".format(int(a.min_size)), "{:,}".format(int(a.max_size))))
        if sb_min is not None and sb_max is not None:
            desc.append("in which %.0f to %.0f %% of the inputs spend an output of the same block" % (100 * sb_min, 100 * sb_max))
        elif sb_min is not None:
            desc.append("in which %.0f %% or more of the inputs spend an output of the same block" % (100 * sb_min))
        elif sb_max is not None:
            desc.append("in which %.0f %% or less of the inputs spend an output of the same block" % (100 * sb_max))
        return keep, "certified closures " + " and ".join(desc)

    if a.provenance:
        selections = [("chained closures", select(a.provenance[0], None)), ("old-input closures", select(None, a.provenance[1]))]
    elif a.shape:
        selections = [("", select(a.same_block_min, a.same_block_max))]
    else:
        selections = [("", (None, ""))]

    recs = defaultdict(list)
    with open(a.pairs, newline="") as f:
        for r in csv.DictReader(f):
            if not r["duration_s"]:
                continue
            d, x, y = float(r["duration_s"]), float(r["applied"]), float(r["reapplied"])
            n = x + y
            if not (0 <= d < 60) or n < 100:
                continue
            recs[r["agent"]].append((d, x, y, n, r["eb"]))
    if not a.classes:
        # the 500-transaction class holding the most distinct EBs, as validation_bins.py takes it
        by_class = defaultdict(set)
        for rs in recs.values():
            for r in rs:
                by_class[int(r[3] // 500) * 500].add(r[4])
        mode = max(by_class, key=lambda c: len(by_class[c]))
        a.classes = [(mode, mode + 499)]

    for lo, hi in a.classes:
        # per selection: per agent the readings, and the EB count
        per_sel, ebs = [], []
        for name, (keep, desc) in selections:
            sel = {ag: [r for r in rs if lo <= r[3] <= hi and (keep is None or r[4] in keep)] for ag, rs in recs.items()}
            per_sel.append({ag: readings(rs, a.reapply_share, a.apply_share) for ag, rs in sel.items() if rs})
            ebs.append(len({r[4] for rs in sel.values() for r in rs}))
        lead = "EBs of %s to %s transactions" % ("{:,}".format(lo), "{:,}".format(hi))
        if a.provenance:
            lead += ": " + "; ".join("%s, %s, %s EBs" % (name, desc, "{:,}".format(n)) for (name, (_, desc)), n in zip(selections, ebs))
        elif a.shape:
            lead += ", %s, %s EBs" % (selections[0][1][1], "{:,}".format(ebs[0]))
        else:
            lead += ", %s EBs" % "{:,}".format(ebs[0])
        print(lead + "; a host cell resting on fewer than %d EBs is marked tentative.\n" % a.min_records)
        groups = [name for name, _ in selections]
        head = "| host class (instance, vCPU, generation) | hosts | " + " | ".join(
            "%sper applied transaction, milliseconds (EBs per host) | per reapplied transaction, microseconds (EBs per host)" % (g + ": " if g else "") for g in groups) + " | EBs validated per host |"
        print(head)
        print("|---|---|" + "---|---|" * len(groups) + "---|")
        cls = defaultdict(list)
        for ag, h in hosts.items():
            if any(ag in ps for ps in per_sel):
                cls[(GEN_RANK.get(h["generation"], 9), int(h["vcpu"]), h["deployment"], h["instance"], h["generation"])].append((h["host"], ag))
        for key, hs in sorted(cls.items()):
            _, vcpu, dep, inst, gen = key
            hs.sort()
            out, counts = [], []
            for ps in per_sel:
                v = [ps[ag] for _, ag in hs if ag in ps]
                out.extend(cells(v, a.min_records) if v else ("-", "-"))
                counts.append(rng([x[0] for x in v], "%d") if v else "-")
            print("| %s, %d vCPU, %s (%s) | %s | %s | %s |" % (inst, vcpu, gen, dep, ", ".join(h for h, _ in hs), " | ".join(out), "; ".join(counts)))
        # the operators: the nodes with enough EBs under every selection printed
        ops = [ag for ag in recs if ag not in hosts
               and all(ag in ps and ps[ag][1] >= a.min_records and ps[ag][3] >= 2 * a.min_records and ps[ag][2] is not None for ps in per_sel)]
        if ops:
            out = []
            for ps in per_sel:
                av = [ps[ag][2] * 1e3 for ag in ops]
                bv = [ps[ag][4] * 1e6 for ag in ops]
                out.append("%.2f / %.2f / %.2f" % (q(av, .25), q(av, .5), q(av, .75)))
                out.append("%.0f / %.0f / %.0f" % (q(bv, .25), q(bv, .5), q(bv, .75)))
            label = ("operators (%d nodes with enough EBs under both selections)" if a.provenance else "operators (%d nodes)") % len(ops) if hosts else "nodes (%d)" % len(ops)
            print("| %s: lower quartile / median / upper quartile node | | %s | %s |" % (
                label, " | ".join(out), "; ".join(rng([ps[ag][0] for ag in ops], "%d") for ps in per_sel)))
        print()


if __name__ == "__main__":
    main()
