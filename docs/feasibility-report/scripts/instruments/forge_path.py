#!/usr/bin/env python3
"""The forge path of an RB on the IOG producers (report section 5.3), from the
archived Loki pulls of the 2 MB period: per RB forged by a host and on the
final chain, the duration of each forge-loop call by the kind of RB forged,
and the resolution of the closure at forge by the closure's size, printed as
Markdown. Restricted to the loaded windows.

    forge_path.py [--data DIR] [--pulls DIR] [--win FILE] [--chain FILE] > outputs/f2-high/forge_path.md

--data   the data folder (default: the parent of this repository)
--pulls  the pull folder with one <host>_<family>.jsonl.zst per host and
         family (default grafana/archive/loki/f2-adoption/producers under
         --data; DATA.md): `forge` (Forge.Loop events) for every producer,
         `forgecalls` (the forge-loop call trace, argument = slot) for the
         hosts that have it, `calls` (chain selection and the closure
         resolution at forge, argument = EB announcement hash)
--win    the loaded windows (default data/windows/windows-f2-high.txt in this repository)
--chain  the chain cache (default chain-2026-10-18/blocks.sqlite under --data)

Kinds as in adoption_delay.sql: a certifying RB by the closure it certifies
(the parent's EB closure), a plain RB full from 80 kB. Medians and 90th
percentiles are pooled over the hosts' RBs. The call-trace records are read
with `zstd -dc`.
"""
import argparse, datetime as dt, glob, json, os, sqlite3, subprocess

SLOT0 = 1792281600
STEPS = ["forge", "mempool-get-snapshot-for", "mempool-get-snapshot-for-no-cache", "partition-mempool", "forge-block", "on-forged-leios-eb"]
KINDS = ["plain RB, 80-88 kB", "certifies, closure < 0.5 MB", "certifies, closure 0.5-1 MB", "certifies, closure 1-1.5 MB", "certifies, closure 1.5-2 MB"]


def cbin(c):
    c = c or 0
    return KINDS[4] if c >= 1.5e6 else KINDS[3] if c >= 1e6 else KINDS[2] if c >= 5e5 else KINDS[1]


def windows(path):
    w = []
    for line in open(path):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        s, e = line.split()[:2]
        w.append((dt.datetime.fromisoformat(s).replace(tzinfo=dt.timezone.utc).timestamp(),
                  dt.datetime.fromisoformat(e).replace(tzinfo=dt.timezone.utc).timestamp()))
    return w


def inwin(w, t):
    return any(s <= t < e for s, e in w)


def records(path):
    p = subprocess.Popen(["zstd", "-dc", path], stdout=subprocess.PIPE)
    for line in p.stdout:
        yield json.loads(line)
    p.wait()


def q(v, p):
    v = sorted(v)
    return v[min(len(v) - 1, int(p * len(v)))] if v else None


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    here = os.path.dirname(os.path.abspath(__file__))
    ap.add_argument("--data", dest="root", default=os.path.normpath(os.path.join(here, "..", "..", "..")))
    ap.add_argument("--pulls", default="grafana/archive/loki/f2-adoption/producers")
    ap.add_argument("--win", default=os.path.normpath(os.path.join(here, "..", "..", "data", "windows", "windows-f2-high.txt")))
    ap.add_argument("--chain", default="chain-2026-10-18/blocks.sqlite")
    a = ap.parse_args()
    pulls, win = os.path.join(a.root, a.pulls), windows(a.win)

    db = sqlite3.connect("file:" + os.path.join(a.root, a.chain) + "?mode=ro", uri=True)
    blk, by_no, eb = {}, {}, {}
    for h, bn, slot, size, txs, cert, ebh, clo in db.execute(
            "select hash, block_no, slot_no, size, tx_count, has_leios_cert, eb_announcement_hash, eb_closure_size from block where slot_no is not null"):
        blk[h] = dict(block_no=bn, slot=slot, size=size, txs=txs, cert=cert)
        by_no[bn] = h
        if ebh:
            eb[ebh] = dict(closure=clo, block_no=bn)
    for h, b in blk.items():
        parent = blk.get(by_no.get(b["block_no"] - 1))
        b["kind"] = (cbin(db.execute("select eb_closure_size from block where block_no = ?", (b["block_no"] - 1,)).fetchone()[0]) if b["cert"] == 1
                     else KINDS[0] if b["size"] >= 80000 else "plain RB, < 80 kB")
    for e in eb.values():  # the transactions of a certified closure are counted on the certifying RB (the next block)
        nxt = blk.get(by_no.get(e["block_no"] + 1))
        e["txs"] = nxt["txs"] if nxt and nxt["cert"] == 1 else None

    # 1. the forge loop on the hosts with a call trace: durations per (host, slot) of each step, the RB's kind from the chain
    forged = {}   # (host, slot) -> (hash, ts of ForgedBlock)
    for path in sorted(glob.glob(os.path.join(pulls, "*_forge.jsonl.zst"))):
        host = os.path.basename(path).split("_")[0]
        for r in records(path):
            if r.get("ns") == "Forge.Loop.ForgedBlock":
                forged[(host, r["data"]["slot"])] = (r["data"]["block"], r["ts"] / 1e9)
    steps = {}    # (host, slot) -> {step: duration}
    hosts_with_calls = []
    for path in sorted(glob.glob(os.path.join(pulls, "*_forgecalls.jsonl.zst"))):
        host = os.path.basename(path).split("_")[0]
        hosts_with_calls.append(host)
        for r in records(path):
            d = r.get("data", {})
            if d.get("name") in STEPS and isinstance(d.get("argument"), int):
                steps.setdefault((host, d["argument"]), {})[d["name"]] = d["duration"]
    rows = {}     # kind -> {step: [durations]}, plus "forged after slot"
    n = {}
    for (host, slot), st in steps.items():
        f = forged.get((host, slot))
        if not f or f[0] not in blk or not inwin(win, SLOT0 + slot):
            continue
        k = blk[f[0]]["kind"]
        n[k] = n.get(k, 0) + 1
        for s, v in st.items():
            rows.setdefault(k, {}).setdefault(s, []).append(v)
        rows.setdefault(k, {}).setdefault("ForgedBlock after slot start", []).append(f[1] - (SLOT0 + slot))

    print("Forge-loop calls per RB forged and on the chain, hosts %s, loaded windows of %s; p50 / p90 s." % (", ".join(hosts_with_calls), os.path.basename(a.win)))
    print()
    print("| step | " + " | ".join(KINDS) + " |")
    print("|---|" + "---|" * len(KINDS))
    print("| RBs | " + " | ".join("{:,}".format(n.get(k, 0)) for k in KINDS) + " |")
    for s in ["mempool-get-snapshot-for", "mempool-get-snapshot-for-no-cache", "partition-mempool", "forge-block", "on-forged-leios-eb", "forge", "ForgedBlock after slot start"]:
        cells = []
        for k in KINDS:
            v = rows.get(k, {}).get(s)
            cells.append("%.3f / %.3f" % (q(v, .5), q(v, .9)) if v else "-")
        print("| %s | %s |" % (s, " | ".join(cells)))

    # 2. the closure resolution at forge on every host with the calls family, by the closure's size
    res = {}
    hosts_calls = []
    for path in sorted(glob.glob(os.path.join(pulls, "*_calls.jsonl.zst"))):
        hosts_calls.append(os.path.basename(path).split("_")[0])
        for r in records(path):
            d = r.get("data", {})
            if d.get("name") != "resolve-and-apply-leios-closure" or not inwin(win, r["ts"] / 1e9):
                continue
            e = eb.get(d.get("argument"))
            if not e or e["closure"] is None:
                continue
            res.setdefault(cbin(e["closure"]), []).append((d["duration"], e["closure"], e["txs"]))
    print()
    print("Closure resolution and application at forge (resolve-and-apply-leios-closure, argument = the EB announcement), %d hosts, by the closure's size." % len(hosts_calls))
    print()
    print("| closure | calls | closure p50 | transactions p50 | duration p50 / p90 | per transaction |")
    print("|---|---|---|---|---|---|")
    for k in KINDS[1:]:
        v = res.get(k)
        if not v:
            continue
        d50, c50 = q([x[0] for x in v], .5), q([x[1] for x in v], .5)
        t = [x[2] for x in v if x[2]]
        t50 = q(t, .5) if t else None
        print("| %s | %d | %.2f MB | %s | %.3f / %.3f s | %s |" % (k, len(v), c50 / 1e6, "{:,}".format(int(t50)) if t50 else "-",
                                                                 d50, q([x[0] for x in v], .9), "%.0f us" % (1e6 * d50 / t50) if t50 else "-"))


if __name__ == "__main__":
    main()
