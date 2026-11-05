#!/usr/bin/env python3
"""The cost tables of report section 6 (and the host-speed counterfactual
of section 8), printed as Markdown from the saved outputs.

    cost_table.py [--outputs DIR] TABLE WINDOW [WINDOW ...]

TABLE    bins      validation time per EB by the share of the EB the voter
                   had not seen, on the window's most common EB size class,
                   one block per window: the IOG and PIR host classes and the
                   operators' quartiles (validation_bins.md); section 6.1
         fit       the validation fit per window: fixed cost per EB and the
                   rate per applied and per reapplied transaction, pooled and
                   at the median node with the quartiles, with the window's
                   transaction shape (validation_fit.md); section 7
         hosts     the IOG and PIR hosts by instance class within a window
                   (validation_fit.md, host-class table) with their resident
                   set and CPU (resources.md)
         resources the memory and CPU distributions per population (resources.md)
         unseen    the EBs that fail by the share of their transactions the
                   voters had not seen, cluster runs (host_speed.md, second table)
         speed     the host-speed counterfactual, cluster runs (host_speed.md,
                   first table); section 8
WINDOW   a key of WINDOWS below
"""
import argparse, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUTPUTS = os.path.normpath(os.path.join(HERE, "..", "outputs"))
WINDOWS = {
    "f1-high": dict(label="testnet 40 kB / 260 kB, loaded hours", shape="257 B, one input, no scripts"),
    "f2-high": dict(label="testnet 308 kB / 2 MB, loaded hours", shape="318 B, one input, no scripts"),
    "1kb": dict(label="testnet 308 kB / 2 MB, 1 kB transactions", shape="about 1 kB with metadata, and 235 to 260 B, mixed"),
    "cluster-40k260k": dict(label="cluster 40 kB / 260 kB, 200 B", shape="200 B, one input, one output", cluster=True),
    "cluster-100k1m": dict(label="cluster 100 kB / 1 MB, 200 B", shape="200 B, one input, one output", cluster=True),
    "cluster-100k1m-374": dict(label="cluster 100 kB / 1 MB, 374 B", shape="374 B, two inputs, two outputs", cluster=True),
}


def tables(path):
    """The Markdown tables of a saved output, each a list of row lists (header first)."""
    out, cur = [], None
    if not os.path.exists(path):
        return out
    for line in open(path):
        line = line.rstrip("\n")
        if line.startswith("|"):
            cells = [c.strip() for c in line.strip().strip("|").split("|")]
            if all(c.strip("-: ") == "" for c in cells):
                continue
            if cur is None:
                cur = []
                out.append(cur)
            cur.append(cells)
        else:
            cur = None
    return out


def bins(outputs, names):
    for i, name in enumerate(names):
        w = WINDOWS[name]
        path = os.path.join(outputs, name, "validation_bins.md")
        t = tables(path)
        if not t:
            print("%s: n/a\n" % w["label"])
            continue
        lead = next((l.strip() for l in open(path) if l.strip() and not l.startswith("|")), "")
        print("**Table 6.1%s.** %s (%s): %s\n" % ("abcdefgh"[i], w["label"], w["shape"], lead))
        for tab in t:
            print("| " + " | ".join(tab[0]) + " |")
            print("|---|" + "---|" * (len(tab[0]) - 1))
            for row in tab[1:]:
                print("| " + " | ".join(row) + " |")
            print()


def fit(outputs, names):
    print("| window | transactions | records, nodes | fixed per EB (pooled) | per applied transaction: pooled; nodes' quartiles and median | per reapplied transaction: pooled; nodes' median |")
    print("|---|---|---|---|---|---|")
    for name in names:
        w = WINDOWS[name]
        t = tables(os.path.join(outputs, name, "validation_fit.md"))
        if len(t) < 2:
            print("| %s | %s | n/a | | | |" % (w["label"], w["shape"]))
            continue
        head, row = t[0][0], t[0][1]
        m = re.search(r"over ([\d,]+) records of (\d+) nodes", head[0])
        per = {r[0]: r[1:] for r in t[1][1:]}
        a, b = per["ms per applied transaction"], per["ms per reapplied transaction"]
        print("| %s | %s | %s, %s | %s | %s ms; %s to %s, median %s | %s ms; median %s |" % (
            w["label"], w["shape"], m.group(1), m.group(2), row[3], row[1].replace(" ms", ""), a[1], a[3], a[2], row[2].replace(" ms", ""), b[2]))


def hosts(outputs, names):
    print("| window | host class | hosts | per applied transaction | per reapplied transaction | fixed per EB | resident set, median / peak | process CPU, cores, median interval |")
    print("|---|---|---|---|---|---|---|---|")
    for name in names:
        w = WINDOWS[name]
        t = tables(os.path.join(outputs, name, "validation_fit.md"))
        r = tables(os.path.join(outputs, name, "resources.md"))
        res = {}
        for tab in r:
            if tab and tab[0][0] == "host class":
                for row in tab[1:]:
                    res[row[0].split(",")[0]] = row
        if len(t) < 3:
            continue
        for row in t[2][1:]:
            inst = row[0].split(",")[0]
            rr = res.get(inst)
            print("| %s | %s | %s | %s ms | %s ms | %s | %s | %s |" % (
                w["label"], row[0], row[1], row[3], row[4], row[5], rr[3] if rr else "n/a", rr[5].split(" / ")[0] if rr else "n/a"))


def resources(outputs, names):
    print("| population | nodes | resident set at the node's peak, GB: p10 / median / p90 / max | GC live data at the peak, GB, median node | process CPU, cores, median node's median interval | GC share, median node |")
    print("|---|---|---|---|---|---|")
    for name in names:
        w = WINDOWS[name]
        t = tables(os.path.join(outputs, name, "resources.md"))
        if not t:
            print("| %s | n/a | | | | |" % w["label"])
            continue
        rows = {r[0]: r[1:] for r in t[0][1:]}
        n = re.search(r"(\d+) nodes", t[0][0][0]).group(1)
        peak = rows.get("resident set at the node's peak sample, GB", ["-"] * 4)
        print("| %s | %s | %s / %s / %s / %s | %s | %s | %s |" % (
            w["label"] + (" (operator nodes)" if not w.get("cluster") else ""), n, peak[0], peak[1], peak[2], peak[3],
            rows.get("GC live data at the peak, GB", ["-", "-"])[1], rows.get("process CPU, cores, the node's median interval", ["-", "-"])[1],
            rows.get("GC share of the process CPU time", ["-", "-"])[1]))


def unseen(outputs, names):
    first = True
    for name in names:
        w = WINDOWS[name]
        t = tables(os.path.join(outputs, name, "host_speed.md"))
        if len(t) < 2:
            continue
        tab = t[1]
        if first:
            print("| run | " + " | ".join(tab[0][:2]) + " | fail as recorded |")
            print("|---|---|---|---|")
            first = False
        for row in tab[1:]:
            print("| %s | %s | %s | %s |" % (w["label"], row[0], row[1], row[2]))


def speed(outputs, names):
    first = True
    for name in names:
        w = WINDOWS[name]
        t = tables(os.path.join(outputs, name, "host_speed.md"))
        if not t:
            continue
        tab = t[0]
        if first:
            print("| run | " + " | ".join(tab[0]) + " |")
            print("|---|" + "---|" * len(tab[0]))
            first = False
        for row in tab[1:]:
            print("| %s | %s |" % (w["label"], " | ".join(row)))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("table", choices=["bins", "fit", "hosts", "resources", "unseen", "speed"])
    ap.add_argument("windows", nargs="+", metavar="WINDOW")
    ap.add_argument("--outputs", default=OUTPUTS)
    a = ap.parse_args()
    bad = [w for w in a.windows if w not in WINDOWS]
    if bad:
        sys.exit("unknown window %s" % ", ".join(bad))
    {"bins": bins, "fit": fit, "hosts": hosts, "resources": resources, "unseen": unseen, "speed": speed}[a.table](a.outputs, a.windows)


if __name__ == "__main__":
    main()
