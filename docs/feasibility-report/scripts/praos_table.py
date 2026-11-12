#!/usr/bin/env python3
"""The tables of report section 5 (Leios on Praos), printed as Markdown from
the chain caches and the saved outputs of the Praos-side queries, one row per
population and window, so every number in the section's tables is regenerated
by one command.

    praos_table.py [--root DIR] TABLE WINDOW [WINDOW ...]

TABLE    kinds     RB kinds on the chain: certifying or plain, announcing an
                   EB or not, and the plain RB's fullness (chain cache)
         adoption  adoption delay across the reporting nodes of a certifying
                   RB at the set's closure and of a full plain RB
                   (adoption_delay.sql / cluster_adoption.sql outputs)
         pairs     consecutive-slot leader pairs on the chain and forked, by
                   the kind of the pair's first RB (consecutive_pairs.sql /
                   cluster_forks.sql outputs)
         density   leader slots of the observed hosts, RBs on the chain,
                   orphans and chain density (chain cache and the outputs above)
         control   the benchmarking team's Praos control against its two
                   Leios cluster runs, typed from the team's report (no WINDOW)
         path      where the time goes on the testnet, per RB kind: at the
                   forger (forge_path.py output) and at the adopters
                   (adoption_path.sql output); testnet windows only, the
                   forger half where the window has a forge_path.md
WINDOW   a key of WINDOWS below (testnet windows and cluster runs)
--outputs  the saved outputs folder (default: outputs/ in this repository):
         <WINDOW>/adoption.md, pairs.md, adoption_path.md, forge_path.md
--data   the data folder holding the chain caches (default: the parent of
         this repository): chain-2026-10-18/blocks.sqlite for the testnet
         windows and <run>/blocks.sqlite for the cluster runs; read by
         kinds and density only
--trickle   density only: add a row per testnet window for the hours of its
         period outside the loaded windows (the trickle hours)

Testnet windows are restricted to their loaded hours (data/windows/ in this
repository, slot 0 = 1792281600); cluster runs are read whole. The saved
outputs are Markdown or DuckDB box tables; both are parsed.
"""
import argparse, os, sqlite3, sys

SLOT0 = 1792281600          # testnet slot 0 (restart of 2026-10-18)
F = 0.05                    # active slot coefficient on both populations
FULL = 80000                # a plain RB is full from 80 kB (limit 90,112 B)
SMALL = 20000               # and small under 20 kB
CERT_BYTES = 5000           # a certifying RB carries no transactions (about 1 kB)

HERE = os.path.dirname(os.path.abspath(__file__))
OUTPUTS = os.path.normpath(os.path.join(HERE, "..", "outputs"))
DATA = os.path.normpath(os.path.join(HERE, "..", ".."))
WINDOWS_DIR = os.path.normpath(os.path.join(HERE, "..", "data", "windows"))
OUT = OUTPUTS  # set from --outputs in main

WINDOWS = {
    "f1-high": dict(label="testnet 40 kB / 260 kB, loaded hours", period=("2026-10-21T12:00:00", "2026-10-22T01:00:00"),
                    cert_bin="a certifies, closure < 0.5 MB", cert_label="closure under 0.5 MB"),
    "f2-high": dict(label="testnet 308 kB / 2 MB, loaded hours", period=("2026-10-24T12:00:00", "2026-10-26T13:00:00"),
                    cert_bin="d certifies, closure 1.5-2 MB", cert_label="closure 1.5-2 MB"),
    "1kb": dict(label="testnet 308 kB / 2 MB, 1 kB transactions", period=("2026-10-28T18:00:00", "2026-10-29T01:00:00"),
                cert_bin="d certifies, closure 1.5-2 MB", cert_label="closure 1.5-2 MB"),
    "cluster-40k260k": dict(label="cluster 40 kB / 260 kB, 200 B",
                            run="cluster/2026-10-17-21-38-cf576-notag-value-leios-workload-all-n2n-40k260k-1i1o1w-nomadperf-dira-nom",
                            cert_bin="c0 certifies, closure under 300 kB", cert_label="closure 222 kB"),
    "cluster-100k1m": dict(label="cluster 100 kB / 1 MB, 200 B",
                           run="cluster/2026-10-20-20-42-81787-w42notxsub-value-leios-workload-all-n2n-100k1m-1i1o1w-nomadperf-dira-nom",
                           cert_bin="c2 certifies, closure 500 kB to 1 MB", cert_label="closure 555 kB"),
    "cluster-100k1m-374": dict(label="cluster 100 kB / 1 MB, 374 B",
                               run="cluster/2026-10-21-16-22-81787-w42notxsub-value-leios-workload-all-n2n-100k1m-2i2o2w-nomadperf-dira-nom",
                               cert_bin="c2 certifies, closure 500 kB to 1 MB", cert_label="closure 0.5-1 MB"),
    "cluster-100k1m-374-patched": dict(label="cluster 100 kB / 1 MB, 374 B, changed build",
                                       run="cluster/2026-11-09-16-29-2a1ad-w45ezenotxsu-value-leios-workload-all-n2n-100k1m-2i2o2w-nomadperf-dira-nom",
                                       cert_bin="c2 certifies, closure 500 kB to 1 MB", cert_label="closure 1 MB"),
}
PLAIN_FULL = ("f plain RB, 80-88 kB", "p1 plain RB, full (80 kB and up)")

# The benchmarking team's comparison (cluster/reports/2026-10-23-18-49-e651d_praos-11.1.1_leios-40k260k_leios-100k1m.value-only.pdf,
# analysis of 2026-10-27): a Praos run of node 11.1.1 (cluster start 2026-09-05, 52 machines, value-only workload of
# two-input two-output transactions at 12 tx/s) against two Leios cluster runs of node 11.2.0.164 at the same workload
# (40 kB / 260 kB of 2026-10-23, 51 machines; 100 kB / 1 MB of 2026-10-21, 51 machines, the run read in section 4 as
# "cluster 100 kB / 1 MB, 374 B"). Values as printed in the report's tables.
CONTROL = [
    ("node, cluster start", "11.1.1, 2026-09-05", "11.2.0.164, 2026-10-23", "11.2.0.164, 2026-10-21"),
    ("RB size, mean", "88,956 B", "42,688 B", "65,120 B"),
    ("RBs certifying the predecessor's EB", "0", "0.527", "0.273"),
    ("height and slot battles per RB", "0.00091", "0.00524", "0.0218"),
    ("leadership to forged", "0.0008 s", "0.349 s", "0.586 s"),
    ("slot start to header announced", "0.063 s", "0.395 s", "0.690 s"),
    ("adopted by half the cluster", "0.61 s", "0.83 s", "1.28 s"),
    ("adopted by 90 % of the cluster", "1.07 s", "1.14 s", "1.63 s"),
    ("adopted by the whole cluster", "1.11 s", "1.21 s", "1.79 s"),
    ("process CPU, share of one core", "2.4 %", "7.8 %", "22.9 %"),
    ("kernel resident set", "8.2 GB", "11.6 GB", "12.2 GB"),
]
CONTROL_COLS = ("Praos control", "Leios 40 kB / 260 kB, 374 B", "Leios 100 kB / 1 MB, 374 B")


def tables(path):
    """All tables of a saved output (Markdown or DuckDB box), each a list of row dicts."""
    out, cur, header, last = [], None, None, None
    if not os.path.exists(path):
        return out
    for line in open(path):
        line = line.rstrip("\n")
        if line.startswith("|") or line.startswith("│"):
            cells = [c.strip() for c in line.strip().strip("|│").split("|" if line.startswith("|") else "│")]
            if line.startswith("|") and all(c.strip("-: ") == "" for c in cells):
                # a Markdown separator: the line before it is the header of a new table (tables may follow each other directly)
                if cur is not None and cur and cur[-1] is last:
                    cur.pop()
                header, cur = last_cells, []
                out.append(cur)
            elif line.startswith("│") and all(c in ("varchar", "int64", "int128", "double", "bigint", "float") for c in cells):
                continue
            elif header is None:
                header, cur = cells, []
                out.append(cur)
            else:
                last = dict(zip(header, cells))
                cur.append(last)
            last_cells = cells
        elif line.startswith("┌"):
            header, cur = None, None
        elif line.startswith("├") or line.startswith("└"):
            continue
        else:
            header, cur = None, None
    return out


def rows_of(path, column):
    """Rows of every table of the output that has the column, keyed by that column."""
    r = {}
    for t in tables(path):
        for row in t:
            if column in row:
                r[row[column]] = row
    return r


def windows_of(path):
    w = []
    for line in open(path):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        s, e = line.split()[:2]
        import datetime as dt
        w.append((dt.datetime.fromisoformat(s).replace(tzinfo=dt.timezone.utc).timestamp(),
                  dt.datetime.fromisoformat(e).replace(tzinfo=dt.timezone.utc).timestamp()))
    return w


def trickle_of(period, wins):
    """The hours of the period outside the loaded windows, as (start, end) ranges."""
    import datetime as dt
    s0, e0 = (dt.datetime.fromisoformat(x).replace(tzinfo=dt.timezone.utc).timestamp() for x in period)
    out, t = [], s0
    for s, e in sorted(wins):
        if s > t:
            out.append((t, min(s, e0)))
        t = max(t, e)
    if t < e0:
        out.append((t, e0))
    return out


def chain(root, name, trickle=False):
    """The window's RBs from its chain cache: (slot, size, certifies, announces) and the slots covered."""
    c = WINDOWS[name]
    if "run" in c:
        db = sqlite3.connect("file:" + os.path.join(root, c["run"], "blocks.sqlite") + "?mode=ro", uri=True)
        rows = db.execute("select slot_no, size, has_leios_cert, eb_announcement_hash is not null from block where slot_no is not null").fetchall()
        slots = max(r[0] for r in rows) - min(r[0] for r in rows) + 1
        return rows, slots
    db = sqlite3.connect("file:" + os.path.join(root, "chain-2026-10-18", "blocks.sqlite") + "?mode=ro", uri=True)
    wins = windows_of(os.path.join(WINDOWS_DIR, "windows-%s.txt" % name))
    if trickle:
        wins = trickle_of(c["period"], wins)
    rows = []
    for s, e in wins:
        rows += db.execute("select slot_no, size, has_leios_cert, eb_announcement_hash is not null from block "
                           "where slot_no is not null and slot_no >= ? and slot_no < ?", (s - SLOT0, e - SLOT0)).fetchall()
    return rows, int(sum(e - s for s, e in wins))


def fullness(size):
    return "full" if size >= FULL else ("small" if size < SMALL else "partial")


def kinds(root, names):
    print("| window | certifies, announces | certifies, no EB | plain, announces: full / partial / small | plain, no EB: full / partial / small |")
    print("|---|---|---|---|---|")
    for name in names:
        rows, _ = chain(root, name)
        n = {}
        for slot, size, cert, ann in rows:
            k = ("c" if cert else "p", bool(ann), fullness(size))
            n[k] = n.get(k, 0) + 1
        ca = sum(v for k, v in n.items() if k[0] == "c" and k[1])
        cn = sum(v for k, v in n.items() if k[0] == "c" and not k[1])
        pa = [n.get(("p", True, f), 0) for f in ("full", "partial", "small")]
        pn = [n.get(("p", False, f), 0) for f in ("full", "partial", "small")]
        print("| %s | %s | %s | %s | %s |" % (WINDOWS[name]["label"], "{:,}".format(ca), "{:,}".format(cn),
                                            " / ".join("{:,}".format(v) for v in pa), " / ".join("{:,}".format(v) for v in pn)))


def adoption_rows(root, name):
    path = os.path.join(OUT, name, "adoption.md")
    return rows_of(path, "kind"), path


def adoption(root, names):
    print("| window | certifying RB (closure) | certifying RBs | adopted p50 / p90 | within 1 s | full plain RB, p50 / p90 | within 1 s | full plain RBs |")
    print("|---|---|---|---|---|---|---|---|")
    for name in names:
        c = WINDOWS[name]
        r, path = adoption_rows(root, name)
        cert = r.get(c["cert_bin"])
        plain = next((r[k] for k in PLAIN_FULL if k in r), None)
        if cert is None or plain is None:
            print("| %s | n/a (%s) | | | | | | |" % (c["label"], os.path.relpath(path, root)))
            continue
        s = lambda v: "%.2f" % float(v)
        print("| %s | %s | %s | %s / %s s | %.0f %% | %s / %s s | %.0f %% | %s |" % (
            c["label"], c["cert_label"], "{:,}".format(int(cert["rbs"])), s(cert["delay_p50"]), s(cert["delay_p90"]), float(cert["within_1s_pct"]),
            s(plain["delay_p50"]), s(plain["delay_p90"]), float(plain["within_1s_pct"]), "{:,}".format(int(plain["rbs"]))))


def pairs_row(root, name):
    path = os.path.join(OUT, name, "pairs.md")
    r = rows_of(path, "on_chain_no_fork")
    return (next(iter(r.values())) if r else None), path


def frac(forked, on_chain):
    """'forked of all (share)': the forked pairs over the pairs of that kind, on the chain and forked together."""
    n = forked + on_chain
    return "%d of %d (%.0f %%)" % (forked, n, 100.0 * forked / n) if n else "-"


def pairs(root, names):
    print("| window | share forked among all consecutive-slot pairs | among the pairs led by a certifying RB | among the pairs led by a plain RB |")
    print("|---|---|---|---|")
    for name in names:
        c = WINDOWS[name]
        r, path = pairs_row(root, name)
        if r is None:
            print("| %s | n/a (%s) | | |" % (c["label"], os.path.relpath(path, root)))
            continue
        oc, occ, ocp = int(r["on_chain_no_fork"]), int(r["on_chain_first_certifies"]), int(r["on_chain_first_plain"])
        fk, fkc, fkp = int(r["forked"]), int(r["forked_first_certifies"]), int(r["forked_first_plain"])
        print("| %s | %s | %s | %s |" % (c["label"], frac(fk, oc), frac(fkc, occ), frac(fkp, ocp)))


def density(root, names, trickle=False):
    print("| window | observed hosts: leader slots / forged | RBs on the chain | expected at f = 0.05 (sd) | chain density | orphans seen by two or more observed hosts |")
    print("|---|---|---|---|---|---|")
    for name in names:
        c = WINDOWS[name]
        rows, slots = chain(root, name)
        exp = slots * F
        if trickle and "period" in c:
            # the chain alone: the leader-slot and orphan outputs are read over the loaded windows only
            trows, tslots = chain(root, name, trickle=True)
            texp = tslots * F
            print("| %s, trickle hours of the same period | - | %s | %s (%.1f %%) | %.2f | - |" % (
                c["label"].replace(", loaded hours", "").replace(", 1 kB transactions", " (1 kB period)"), "{:,}".format(len(trows)), "{:,.0f}".format(texp), 100 * texp ** 0.5 / texp, len(trows) / texp))
        a, _ = adoption_rows(root, name)
        lead = rows_of(os.path.join(OUT, name, "adoption.md"), "leader_slots")
        lead = next(iter(lead.values()), None)
        if "run" in c:
            f = rows_of(os.path.join(OUT, name, "pairs.md"), "forged_rbs_off_chain")
            orphans = int(next(iter(f.values()))["forged_rbs_off_chain"]) if f else None
            hosts = "all 51 nodes"
        else:
            t = [t for t in tables(os.path.join(OUT, name, "pairs.md")) if t and "forks" in t[0]]
            orphans = sum(int(x["forks"]) for x in t[-1]) if t else None
            hosts = "%s reporting hosts" % lead["hosts"] if lead else "reporting hosts"
        print("| %s | %s: %s / %s | %s | %s (%.1f %%) | %.2f | %s |" % (
            c["label"], hosts, "{:,}".format(int(lead["leader_slots"])) if lead else "n/a", "{:,}".format(int(lead["forged"])) if lead else "n/a",
            "{:,}".format(len(rows)), "{:,.0f}".format(exp), 100 * exp ** 0.5 / exp, len(rows) / exp,
            "{:,}".format(orphans) if orphans is not None else "n/a"))


PATH_KINDS = [("plain RB, 80-88 kB", "f plain RB, 80-88 kB", "full plain RB"),
              ("certifies, closure < 0.5 MB", "a certifies, closure < 0.5 MB", "certifies, closure under 0.5 MB"),
              ("certifies, closure 0.5-1 MB", "b certifies, closure 0.5-1 MB", "certifies, closure 0.5-1 MB"),
              ("certifies, closure 1-1.5 MB", "c certifies, closure 1-1.5 MB", "certifies, closure 1-1.5 MB"),
              ("certifies, closure 1.5-2 MB", "d certifies, closure 1.5-2 MB", "certifies, closure 1.5-2 MB")]


def path(root, names):
    """Per RB kind: at the forger (mempool snapshot, closure resolution, RB forged after the slot start) and at the adopters
    (body arrival, validation inside chain selection, adoption), medians; the forger columns need the window's forge_path.md."""
    print("| window | RB kind | RBs adopted | forger: mempool snapshot | closure resolved and applied | RB forged after slot start | adopters: body arrives | validation in chain selection | adopted |")
    print("|---|---|---|---|---|---|---|---|---|")
    for name in names:
        c = WINDOWS[name]
        if "run" in c:
            continue
        ad = rows_of(os.path.join(OUT, name, "adoption_path.md"), "kind")
        fp = os.path.join(OUT, name, "forge_path.md")
        ftab = [t for t in tables(fp) if t and "step" in t[0]]
        fsteps = {r["step"]: r for r in ftab[0]} if ftab else {}
        ctab = [t for t in tables(fp) if t and "closure" in t[0]]
        cres = {r["closure"]: r for r in ctab[0]} if ctab else {}
        for fk, ak, label in PATH_KINDS:
            a = ad.get(ak)
            if a is None:
                continue
            snap = fsteps.get("mempool-get-snapshot-for" if fk.startswith("plain") else "mempool-get-snapshot-for-no-cache", {}).get(fk, "-")
            forged = fsteps.get("ForgedBlock after slot start", {}).get(fk, "-")
            res = cres.get(fk, {}).get("duration p50 / p90", "-") if not fk.startswith("plain") else "none"
            p50 = lambda s: s.split("/")[0].strip() + " s" if s not in ("-", "none") else s
            print("| %s | %s | %s | %s | %s | %s | %s s | %s s | %s s |" % (
                c["label"], label, "{:,}".format(int(a["rbs"])), p50(snap), p50(res), p50(forged),
                "%.2f" % float(a["body_p50"]), "%.3f" % float(a["validation_p50"]), "%.2f" % float(a["adopted_p50"])))


def control():
    print("| | " + " | ".join(CONTROL_COLS) + " |")
    print("|---|---|---|---|")
    for row in CONTROL:
        print("| " + " | ".join(row) + " |")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("table", choices=["kinds", "adoption", "pairs", "density", "control", "path"])
    ap.add_argument("windows", nargs="*", metavar="WINDOW")
    ap.add_argument("--outputs", default=OUTPUTS)
    ap.add_argument("--data", dest="root", default=DATA)
    ap.add_argument("--trickle", action="store_true")
    a = ap.parse_args()
    global OUT
    OUT = a.outputs
    if a.table == "control":
        control()
        return
    if not a.windows:
        sys.exit("WINDOW required for %s (one of %s)" % (a.table, ", ".join(sorted(WINDOWS))))
    bad = [w for w in a.windows if w not in WINDOWS]
    if bad:
        sys.exit("unknown window %s (one of %s)" % (", ".join(bad), ", ".join(sorted(WINDOWS))))
    if a.table == "density":
        density(a.root, a.windows, a.trickle)
        return
    {"kinds": kinds, "adoption": adoption, "pairs": pairs, "path": path}[a.table](a.root, a.windows)


if __name__ == "__main__":
    main()
