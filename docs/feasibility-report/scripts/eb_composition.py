#!/usr/bin/env python3
"""The EB classes of a testnet window by transaction size (report section
4.3, the 1 kB-transaction window): every eligible EB classed by its
reference count from the chain cache, and the exact composition of every
certified closure from db-sync (the transactions a certifying RB carries are
the certified closure, each with its size).

    eb_composition.py START END [--even-hours] [--chain blocks.sqlite] [--composition CSV] [--slot0 1792281600] [--gap 14]

START, END   UTC, 'YYYY-MM-DD HH:MM'; --even-hours keeps the EBs whose slot
             falls in an even UTC hour (the generator's loaded hours)
--chain      the chain cache (default chain-2026-10-18/blocks.sqlite in the
             data folder, the parent of this repository)
--composition  the certified closures' composition from db-sync, a saved
             output (default outputs/1kb/eb_composition_dbsync.csv): one row
             per certifying RB with its transaction count, bytes, and the
             counts of 700 B-and-up and under-400 B transactions, written
             outside this repository by the db-sync query (DATA.md)
Classes by references (36 B each): under 2,500 = closures of about 1 kB
transactions (the 2 MB cap holds at most ~2,000 of them); 6,000 and up =
closures of small transactions (the reference cap, 8,555); between = mixed.
Composition: transactions of 700 B or more count as the 1 kB kind, under
400 B as the small kind.
"""
import argparse, csv, os, sqlite3

HERE = os.path.dirname(os.path.abspath(__file__))
CLASSES = [(0, 2500, "under 2,500 references (1 kB closures)"), (2500, 6000, "2,500-6,000 references (mixed)"), (6000, 10 ** 9, "6,000 references and up (small transactions)")]


def q(xs, p):
    xs = sorted(xs)
    i = (len(xs) - 1) * p
    lo = int(i)
    return xs[lo] + (xs[min(lo + 1, len(xs) - 1)] - xs[lo]) * (i - lo) if xs else float("nan")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("start")
    ap.add_argument("end")
    ap.add_argument("--even-hours", action="store_true")
    ap.add_argument("--chain", default=os.path.join(HERE, "..", "..", "chain-2026-10-18", "blocks.sqlite"))
    ap.add_argument("--composition", default=os.path.join(HERE, "..", "outputs", "1kb", "eb_composition_dbsync.csv"))
    ap.add_argument("--slot0", type=int, default=1792281600)
    ap.add_argument("--gap", type=int, default=14)
    a = ap.parse_args()
    db = sqlite3.connect(a.chain)
    rows = db.execute("""
        select b.block_no, b.slot_no, b.eb_announcement_size / 36, b.eb_closure_size, n.has_leios_cert
        from block b join block n on n.block_no = b.block_no + 1
        where b.eb_announcement_hash is not null and n.slot_no - b.slot_no >= ?
          and ? + b.slot_no >= cast(strftime('%s', ?) as integer) and ? + b.slot_no < cast(strftime('%s', ?) as integer)""",
        (a.gap, a.slot0, a.start, a.slot0, a.end)).fetchall()
    if a.even_hours:
        rows = [r for r in rows if ((a.slot0 + r[1]) // 3600) % 2 == 0]
    with open(a.composition, newline="") as f:
        comp = {int(r["block_no"]): {k: int(v) for k, v in r.items()} for r in csv.DictReader(f)}
    print("| EB class | eligible EBs | certified | certified closure p50 | transactions p50 (certified) | of which about 1 kB / small, p50 | closures that are mixed |")
    print("|---|---|---|---|---|---|---|")
    for lo, hi, label in CLASSES:
        rs = [r for r in rows if lo <= r[2] < hi]
        cert = [r for r in rs if r[4] == 1]
        # the certifying RB is the next block
        cs = [comp[r[0] + 1] for r in cert if r[0] + 1 in comp]
        mixed = sum(1 for c in cs if c["big"] and c["small"])
        print("| %s | %d | %d (%.0f %%) | %s | %s | %s | %s |" % (
            label, len(rs), len(cert), 100.0 * len(cert) / len(rs) if rs else 0,
            ("%s kB" % format(round(q([r[3] for r in cert if r[3]], 0.5) / 1e3), ",")) if cert else "-",
            format(round(q([c["txs"] for c in cs], 0.5)), ",") if cs else "-",
            ("%s / %s" % (format(round(q([c["big"] for c in cs], 0.5)), ","), format(round(q([c["small"] for c in cs], 0.5)), ","))) if cs else "-",
            ("%d of %d" % (mixed, len(cs))) if cs else "-"))
    print("\n%d eligible EBs, %d certified; composition from db-sync for %d certified closures." % (len(rows), sum(1 for r in rows if r[4] == 1), sum(1 for r in rows if r[4] == 1 and r[0] + 1 in comp)))


if __name__ == "__main__":
    main()
