#!/usr/bin/env python3
"""The forgers of the EBs whose body reached no reporting node (section
4.3.1): the window's EB announcements from the chain cache joined to their
forging pool (the db-sync fetch of slot leaders, kept outside the
repository) and to the nodes that received each EB's body (the per-EB rows
of closure_fleet.sql). Pools are split into those that served the body of
every eligible EB they announced, of none, and of some; the EBs at the
reference cap (8,550 references and up) are counted in each. Pools are
counted, never named.

    eb_forgers.py --chain blocks.sqlite --forgers forgers.csv --fleet closure_fleet_per_eb.csv
                  --diffusion diffusion.csv --from T --to T

--chain      the chain cache, opened read-only
--forgers    the slot leaders of the window's RBs (block_no, slot_no, hash, pool),
             fetched from db-sync by the analysis folder's grafana/eb_forgers_dbsync.py
--fleet      the per-EB rows of closure_fleet.sql (eb, nodes, nodes_body, ...)
--diffusion  the window's per-node closure output, for which pools report logs
--from/--to  the window, UTC 'YYYY-MM-DDTHH:MM'
"""
import argparse, csv, sqlite3
from collections import defaultdict

CAP = 8550


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    for k in ("chain", "forgers", "fleet", "diffusion"):
        ap.add_argument("--" + k, required=True)
    ap.add_argument("--from", dest="t0", required=True)
    ap.add_argument("--to", dest="t1", required=True)
    a = ap.parse_args()
    pool_of = {r["hash"]: r["pool"] for r in csv.DictReader(open(a.forgers))}
    body_of = {r["eb"]: int(r["nodes_body"]) for r in csv.DictReader(open(a.fleet))}
    reporting = {r["pool"] for r in csv.DictReader(open(a.diffusion))}
    con = sqlite3.connect("file:%s?mode=ro" % a.chain, uri=True)
    rows = con.execute("""select hash, eb_announcement_hash, eb_announcement_size from block
                          where time >= ? and time < ? and eb_announcement_hash is not null
                          and eb_announcement_size > 0""", (a.t0 + ":00Z", a.t1 + ":00Z")).fetchall()
    ebs = defaultdict(list)  # pool -> [(at the cap, body at 1+ node)]
    for h, eb, size in rows:
        if eb in body_of:
            ebs[pool_of.get(h, "?")].append((size // 36 >= CAP, body_of[eb] > 0))
    groups = {"every": [], "none": [], "some": []}
    for pool, l in ebs.items():
        served = sum(b for _, b in l)
        groups["none" if served == 0 else "every" if served == len(l) else "some"].append(pool)

    def cell(pools):
        n = sum(len(ebs[p]) for p in pools)
        cap = sum(c for p in pools for c, _ in ebs[p])
        rep = sum(p in reporting for p in pools)
        return "%d pools, %d EBs, %d at the cap, %d reporting" % (len(pools), n, cap, rep)

    print("EB forgers by body service, %s to %s UTC: %d EB announcements, %d of them eligible EBs heard by 40 or more reporting nodes (the fleet rows), from %d pools.\n"
          % (a.t0, a.t1, len(rows), sum(len(l) for l in ebs.values()), len(ebs)))
    print("| served the body of every eligible EB | of none | of some |")
    print("|---|---|---|")
    print("| %s | %s | %s |" % (cell(groups["every"]), cell(groups["none"]), cell(groups["some"])))
    print("\nEBs at the cap in the fleet rows: %d, all from pools that served no body: %s."
          % (sum(c for l in ebs.values() for c, _ in l), all(p in groups["none"] for p, l in ebs.items() for c, _ in l if c)))
    print("Per pool that served no body (eligible EBs, of which at the cap): %s"
          % ", ".join("%d/%d" % (len(ebs[p]), sum(c for c, _ in ebs[p])) for p in sorted(groups["none"], key=lambda p: -len(ebs[p]))))


if __name__ == "__main__":
    main()
