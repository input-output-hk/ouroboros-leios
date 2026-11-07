#!/usr/bin/env python3
"""Validation by EB size class (report section 4.3.1): on the per-(node, EB)
validation records of a testnet window (validation_pairs.csv), per class of
the EB's transaction count (the classes of the closure-tail sub-table,
Table 4.9), the records and the EBs; the closure's arrival after the EB's
slot, median over the records, and the share of records with the closure in
hand by the slot plus 3 s, when the vote window opens; the validation time
after the later of the closure's arrival and the slot plus 3 s, median; the
age at which the record was validated, median, and the share validated
within 7 s of the slot, the deadline. Records of every EB the node validated,
certified or not; a node that never validated an EB has no record in the
file, so the shares are of the validations that completed. Printed as
Markdown.

    validation_classes.py validation_pairs.csv > validation_classes.md
"""
import argparse, csv, statistics as st

BINS = [(0, 2000, "under 2,000 txs"), (2000, 4000, "2,000-4,000"), (4000, 6000, "4,000-6,000"), (6000, 1e12, "6,000 and up")]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("pairs")
    a = ap.parse_args()
    recs = []
    with open(a.pairs, newline="") as f:
        for r in csv.DictReader(f):
            if not r["duration_s"] or not r["closure_s"]:
                continue
            d = float(r["duration_s"])
            if not (0 <= d < 60):
                continue
            recs.append((float(r["applied"]) + float(r["reapplied"]), float(r["closure_s"]), d, float(r["validated_s"]), r["eb"]))
    print("| EB size | records | EBs | closure arrival after the slot, s (p50) | closure in hand by 3 s | validation, s (p50) | validated at, s after the slot (p50) | validated within 7 s |")
    print("|---|---|---|---|---|---|---|---|")
    for lo, hi, lab in BINS:
        rs = [r for r in recs if lo <= r[0] < hi]
        if not rs:
            continue
        print("| %s | %s | %s | %.2f | %.0f %% | %.2f | %.2f | %.0f %% |" % (
            lab, format(len(rs), ","), format(len({r[4] for r in rs}), ","), st.median(r[1] for r in rs),
            100.0 * sum(r[1] <= 3 for r in rs) / len(rs), st.median(r[2] for r in rs), st.median(r[3] for r in rs),
            100.0 * sum(r[3] <= 7 for r in rs) / len(rs)))


if __name__ == "__main__":
    main()
