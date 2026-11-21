#!/usr/bin/env python3
"""The outputs for the public copy of the repository: the per-node files
with every node and pool numbered (n1, n2, ... and p1, p2, ...) in place of
the agent names, hostnames and pool ids, and the ticker column emptied for
the operators' nodes, so that the printers read them unchanged and no
operator or host is named. The IOG and PIR hosts keep their labels (IOG1,
PIR7, the pool tickers the report's text and tables use) next to their
number; their hostnames are numbered like the operators' agent names,
also in the hosts table and in the outputs that mention them. The cluster
runs' nodes are already node-00 to node-50 and need no mapping.

    publish_outputs.py --out PUBLIC_COPY --map FILE [--outputs DIR] [--hosts FILE] WINDOW [WINDOW ...]

PUBLIC_COPY is the public repository folder; the script writes under its
outputs/<window>/ and its data/hosts.csv. The mapping (kind, name, number)
is read from --map if it exists and extended with names not yet in it, so
a node keeps its number across windows and across runs; it is written
back to --map. The mapping file is not part of the public copy.

Files rewritten per window, in the window folder and in its archive-only
subfolder when present: diffusion.csv, diffusion-body.csv (agent, pool,
ticker), validation_nodes.csv, tally_quorum_nodes.csv (agent), voters.csv
(pool_id, ticker), upstream_hosts.csv (agent), and the hostnames inside
forge_path.md. The Markdown views of the diffusion files are not
published.
"""
import argparse, csv, os, re

HERE = os.path.dirname(os.path.abspath(__file__))
FILES = {"diffusion.csv": ("agent", "pool", "ticker"), "diffusion-body.csv": ("agent", "pool", "ticker"),
         "validation_nodes.csv": ("agent",), "tally_quorum_nodes.csv": ("agent",), "voters.csv": ("pool_id", "ticker"),
         "upstream_hosts.csv": ("agent",)}
TEXT_FILES = ("forge_path.md",)
HOST_TICKER = re.compile(r"^(IOG|PIR)\d+$")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("windows", nargs="+", metavar="WINDOW")
    ap.add_argument("--out", required=True, help="the public copy's folder (outputs/ and data/ under it)")
    ap.add_argument("--outputs", default=os.path.normpath(os.path.join(HERE, "..", "outputs")))
    ap.add_argument("--map", required=True, help="the mapping file (kind, name, number), kept outside the repository")
    ap.add_argument("--hosts", default=os.path.normpath(os.path.join(HERE, "..", "data", "hosts.csv")))
    a = ap.parse_args()
    mapping = {}
    if os.path.exists(a.map):
        for r in csv.DictReader(open(a.map, newline="")):
            mapping[(r["kind"], r["name"])] = r["number"]
    nxt = {k: 1 + max([int(n[1:]) for (kk, _), n in mapping.items() if kk == k] or [0]) for k in ("agent", "pool")}

    def num(kind, name):
        if name == "":
            return name
        if (kind, name) not in mapping:
            mapping[(kind, name)] = ("n" if kind == "agent" else "p") + str(nxt[kind])
            nxt[kind] += 1
        return mapping[(kind, name)]

    # the hosts table: hostnames numbered, labels kept
    hosts = list(csv.DictReader(open(a.hosts, newline=""))) if os.path.exists(a.hosts) else []
    hostnames = [h["agent"] for h in hosts]
    for h in hosts:
        h["agent"] = num("agent", h["agent"])
    if hosts:
        os.makedirs(os.path.join(a.out, "data"), exist_ok=True)
        with open(os.path.join(a.out, "data", "hosts.csv"), "w", newline="") as f:
            wr = csv.DictWriter(f, fieldnames=list(hosts[0].keys()))
            wr.writeheader()
            wr.writerows(hosts)

    written = 0
    for w in a.windows:
        for sub in ("", "archive-only"):
            src = os.path.join(a.outputs, w, sub)
            if not os.path.isdir(src):
                continue
            dst = os.path.join(a.out, "outputs", w, sub)
            os.makedirs(dst, exist_ok=True)
            for name, cols in FILES.items():
                path = os.path.join(src, name)
                if not os.path.exists(path):
                    continue
                with open(path, newline="") as f:
                    rd = csv.DictReader(f)
                    rows, fields = list(rd), rd.fieldnames
                for r in rows:
                    keep_ticker = bool(HOST_TICKER.match(r.get("ticker", "") or ""))
                    for c in cols:
                        if c == "ticker":
                            r[c] = r[c] if keep_ticker else ""
                        elif c in ("pool", "pool_id"):
                            r[c] = num("pool", r[c])
                        else:
                            r[c] = num("agent", r[c])
                with open(os.path.join(dst, name), "w", newline="") as f:
                    wr = csv.DictWriter(f, fieldnames=fields)
                    wr.writeheader()
                    wr.writerows(rows)
                written += 1
            for name in TEXT_FILES:
                path = os.path.join(src, name)
                if not os.path.exists(path):
                    continue
                text = open(path).read()
                for hn in sorted(hostnames, key=len, reverse=True):
                    text = text.replace(hn, num("agent", hn))
                open(os.path.join(dst, name), "w").write(text)
                written += 1
    os.makedirs(os.path.dirname(a.map), exist_ok=True)
    with open(a.map, "w", newline="") as f:
        wr = csv.writer(f)
        wr.writerow(["kind", "name", "number"])
        for (kind, name), n in sorted(mapping.items(), key=lambda kv: (kv[0][0], int(kv[1][1:]))):
            wr.writerow([kind, name, n])
    print("wrote %d files under %s; mapping of %d agents and %d pools in %s" % (
        written, a.out, sum(1 for k, _ in mapping if k == "agent"), sum(1 for k, _ in mapping if k == "pool"), a.map))


if __name__ == "__main__":
    main()
