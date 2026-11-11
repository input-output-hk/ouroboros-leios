#!/usr/bin/env python3
"""Where a voter loses an EB: arrival, validation or the deadline, per EB and
summarised by EB size.

Reads the per-(voter, EB) records of voter_stages.sql, one row per vote a
node scheduled (voters that refused the EB because their own chain tip did
not announce it, or found themselves off the committee, are already left
out). For every EB, the shares are taken over its voters, so a voter that
never validated the EB counts as lost rather than disappearing from the
record:

  closure in hand   by the 3 s mark / by the 7 s deadline / after it or never
  validation        within 4 s / longer / never finished
  outcome           voted in time / too late, the late votes attributed to one
                    cause each: the closure came after 7 s; the closure was
                    in time but the validation ran past 7 s; the validation
                    never finished

Per EB-size bin (the transaction count the body hits report, or the body
size over 36 B per reference where the build has no body-hits event) the
counts are written to voter_stages.csv (--csv) for the report's printer
(stage_table.py --voters), and two tables are printed. The stages table
gives the EBs, the voters per EB and the closure and validation shares
pooled over the bin's votes (each group adds to 100 %). The outcome table
gives the voted and late shares, the late votes by cause, the share of EBs
whose late voters exceed a quarter of their voters (the quorum's margin, by
count of reporting voters), and, from the chain cache, the share certified
(next_has_cert of the announcing RB) of the bin's EBs the chain could
certify (the next RB --gap slots away or more; the CSV keeps both counts).

  voter_stages.py voter_stages_pairs.csv --chain chain-2026-10-18/blocks.sqlite --csv outputs/f2-high/voter_stages.csv
  voter_stages.py voter_stages_pairs.csv --chain cluster/<run>/blocks.sqlite --gap 15 --table outcome
"""
import argparse
import csv
import os
import sqlite3
import statistics as st
from collections import defaultdict

BINS = [(0, 2000, "under 2,000"), (2000, 4000, "2,000 to 4,000"), (4000, 6000, "4,000 to 6,000"), (6000, 10**9, "6,000 and up")]
COUNTS = ["votes", "by3", "after3", "never_closure", "val4", "val_long", "never_val",
          "voted", "late", "late_closure", "late_val", "late_never"]
FIELDS = ["bin", "ebs", "voters_p50"] + COUNTS + ["late_over_margin", "known", "eligible", "certified"]
STAGES_HEAD = "| EB size, txs | EBs | voters per EB | closure by 3 s / after 3 s / after 7 s or never | validation within 4 s / longer / never |"
OUTCOME_HEAD = ("| EB size, txs | EBs | voted in time / too late | late: closure arrived after 7 s / validation past 7 s / never validated "
                "| EBs with late voters over a quarter | certified, of the EBs the chain could certify |")


def fnum(s):
    return float(s) if s not in ("", None) else None


def summarise(pairs_path, chain_path, gap, margin):
    """The per-bin counts of FIELDS from the per-(voter, EB) records and the chain cache."""
    ebs = defaultdict(list)
    txs = {}
    with open(pairs_path, newline="") as f:
        for r in csv.DictReader(f):
            eb = r["eb"]
            t = fnum(r["txs"])
            if t is not None:
                txs[eb] = max(txs.get(eb, 0), t)
            ebs[eb].append((fnum(r["closure_s"]), fnum(r["validated_s"]), fnum(r["duration_s"]), r["outcome"]))

    # per announced EB: eligible if the next RB came --gap slots or more after the announcing one; certified if that RB carried the certificate
    chain = {}
    if chain_path != "none" and os.path.exists(chain_path):
        db = sqlite3.connect(chain_path)
        for h, g, c in db.execute(
                "select b.eb_announcement_hash, n.slot_no - b.slot_no, b.next_has_cert from block b join block n on n.block_no = b.block_no + 1 "
                "where b.eb_announcement_hash is not null"):
            chain[h] = (g is not None and g >= gap, bool(c))

    # per EB: counts over its voters
    per_eb = []
    for eb, vs in ebs.items():
        n = len(vs)
        if n == 0 or eb not in txs:
            continue
        by3 = sum(1 for c, _, _, _ in vs if c is not None and c <= 3)
        by7 = sum(1 for c, _, _, _ in vs if c is not None and c <= 7)
        val4 = sum(1 for c, v, d, _ in vs if d is not None and d <= 4)
        val_long = sum(1 for c, v, d, _ in vs if d is not None and d > 4)
        late = [(c, v, d) for c, v, d, o in vs if o == "tooLate"]
        late_closure = sum(1 for c, v, d in late if c is None or c > 7)
        late_val = sum(1 for c, v, d in late if c is not None and c <= 7 and v is not None)
        per_eb.append(dict(txs=txs[eb], votes=n,
                           by3=by3, after3=by7 - by3, never_closure=n - by7,
                           val4=val4, val_long=val_long, never_val=n - val4 - val_long,
                           voted=sum(1 for _, _, _, o in vs if o == "voted"), late=len(late),
                           late_closure=late_closure, late_val=late_val, late_never=len(late) - late_closure - late_val,
                           chain=chain.get(eb)))

    rows = []
    for lo, hi, lab in BINS:
        rs = [r for r in per_eb if lo <= r["txs"] < hi]
        if not rs:
            continue
        known = [r for r in rs if r["chain"] is not None]
        eligible = [r for r in known if r["chain"][0]]
        row = dict(bin=lab, ebs=len(rs), voters_p50=st.median(r["votes"] for r in rs))
        for k in COUNTS:
            row[k] = sum(r[k] for r in rs)
        row["late_over_margin"] = sum(r["late"] > margin * r["votes"] for r in rs)
        row["known"], row["eligible"], row["certified"] = len(known), len(eligible), sum(r["chain"][1] for r in eligible)
        rows.append(row)
    return rows


def stages_row(r, label=None):
    v = float(r["votes"])
    cells = [r["bin"], format(int(r["ebs"]), ","), "%.0f" % float(r["voters_p50"]),
             "%.0f / %.0f / %.0f %%" % tuple(100.0 * float(r[k]) / v for k in ("by3", "after3", "never_closure")),
             "%.0f / %.0f / %.0f %%" % tuple(100.0 * float(r[k]) / v for k in ("val4", "val_long", "never_val"))]
    return "| " + " | ".join(([label] if label else []) + cells) + " |"


def outcome_row(r, label=None):
    v = float(r["votes"])
    eligible, certified = float(r["eligible"]), float(r["certified"])
    cells = [r["bin"], format(int(r["ebs"]), ","),
             "%.0f / %.0f %%" % tuple(100.0 * float(r[k]) / v for k in ("voted", "late")),
             "%.0f / %.0f / %.0f %%" % tuple(100.0 * float(r[k]) / v for k in ("late_closure", "late_val", "late_never")),
             "%.0f %%" % (100.0 * float(r["late_over_margin"]) / float(r["ebs"])),
             ("%.0f %%" % (100.0 * certified / eligible)) if eligible else "-"]
    return "| " + " | ".join(([label] if label else []) + cells) + " |"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("pairs", help="voter_stages_pairs.csv from voter_stages.sql")
    ap.add_argument("--chain", default=os.path.join(os.path.dirname(__file__), "..", "..", "..", "chain-2026-10-18", "blocks.sqlite"),
                    help="chain cache for the eligible and certified shares (eb_announcement_hash, next_has_cert); 'none' leaves the columns out")
    ap.add_argument("--gap", type=int, default=14, help="certification gap in slots: an EB is eligible when the next RB is this far or more (default 14)")
    ap.add_argument("--margin", type=float, default=0.25, help="late share above which an EB cannot reach the quorum (default 0.25)")
    ap.add_argument("--csv", help="write the per-bin counts here (the printer's input); default none")
    ap.add_argument("--table", choices=["stages", "outcome", "both"], default="both", help="which table to print (default both)")
    a = ap.parse_args()

    rows = summarise(a.pairs, a.chain, a.gap, a.margin)
    if a.csv:
        with open(a.csv, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=FIELDS)
            w.writeheader()
            w.writerows(rows)
    if a.table in ("stages", "both"):
        print(STAGES_HEAD)
        print("|---|---:|---:|---:|---:|")
        for r in rows:
            print(stages_row(r))
    if a.table == "both":
        print()
    if a.table in ("outcome", "both"):
        print(OUTCOME_HEAD)
        print("|---|---:|---:|---:|---:|---:|")
        for r in rows:
            print(outcome_row(r))


if __name__ == "__main__":
    main()
