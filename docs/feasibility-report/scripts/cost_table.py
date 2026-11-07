#!/usr/bin/env python3
"""The cost tables of report section 6 (and the host-speed counterfactual
of section 8), printed as Markdown from the saved outputs.

    cost_table.py [--outputs DIR] TABLE WINDOW [WINDOW ...]

TABLE    bins      validation time per EB by the share of the EB the voter
                   applied in full, on the window's most common EB size class,
                   one block per window: the IOG and PIR host classes and the
                   operators' quartiles (validation_bins.md); section 6.1
         shape     the cost per applied and per reapplied transaction at the
                   vote on EBs of one size class, per host class and the
                   operators' quartiles, on the chained closures and on the
                   old-input closures side by side, one block per testnet
                   window (validation_shape.md; Tables 7.2a and 7.2b) and one
                   block for the cluster runs (Table 7.3); a host cell resting
                   on fewer than 10 EBs reads "too few EBs" and the EBs
                   each host validated are left out, with --full the expanded
                   tables as the instrument prints them
         series    the same on the chained closures of one transaction size
                   across the EB size classes and on the classes the cluster
                   runs populate (validation_shape_series.md); read in 7.2's
                   and 7.3's prose
         kind      the within-kind check: one window's closures of one
                   transaction size by their same-block input share
                   (validation_shape_kind.md); read in 7.2's prose
         resources the memory and CPU distributions per population (resources.md)
         unseen    the EBs that fail by the share of their transactions the
                   voters applied in full, cluster runs (host_speed.md, second table)
         speed     the host-speed counterfactual, cluster runs (host_speed.md,
                   first table); section 8
WINDOW   a key of WINDOWS below
"""
import argparse, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUTPUTS = os.path.normpath(os.path.join(HERE, "..", "outputs"))
WINDOWS = {
    "f1-high": dict(label="testnet 40 kB / 260 kB, loaded hours", shape="257 B, one input, no scripts"),
    "f2-high": dict(label="testnet 308 kB / 2 MB, loaded hours", shape="247 B and 506 B, the same one-input transaction with two metadata sizes, 318 B on average, no scripts"),
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


def leads(path):
    """The lines of a saved output that are not table rows: one lead line per table, in order."""
    return [l.strip() for l in open(path) if l.strip() and not l.startswith("|")] if os.path.exists(path) else []


def class_cell(lead):
    """The EB class and count of a validation_shape.md lead line (the selection is in the caption)."""
    m = re.match(r"EBs of ([\d,]+) to ([\d,]+) transactions(?:, certified closures [^,]*)?, ([\d,]+) EBs", lead)
    return "%s to %s transactions, %s EBs" % (m.group(1), m.group(2), m.group(3)) if m else lead


TENTATIVE = re.compile(r"^(.*?) \(([^)]*)\) tentative$")
TENTATIVE_LEAD = "a host cell resting on fewer than %d EBs is marked tentative"


def blank(cell):
    """A tentative cell (a reading on fewer than 10 EBs on some host of the class) reads "too few
    EBs": the report shows no cost that rests on so few EBs; the expanded form keeps it."""
    return "too few EBs" if TENTATIVE.match(cell) else cell


def compact_lead(lead):
    m = re.search(TENTATIVE_LEAD.replace("%d", r"(\d+)"), lead)
    return lead.replace(m.group(0), "a host cell resting on fewer than %s EBs reads too few" % m.group(1)) if m else lead


def shape(outputs, names, full=False):
    """One block per testnet window: the lead line and the table of validation_shape.md, the hosts by
    class and the operators' quartiles under the two selections (chained and old-input closures) side
    by side; the cluster runs, uniform hosts, as one block with a row per run (no selection: the runs'
    transactions spend genesis outputs, almost never reused: the old-input case throughout). By
    default a tentative cell is reduced to its EB count; full=True prints the instrument's cells."""
    letters = iter("abcdefgh")
    cluster = [n for n in names if WINDOWS[n].get("cluster")]
    for name in names:
        w = WINDOWS[name]
        if w.get("cluster"):
            continue
        path = os.path.join(outputs, name, "validation_shape.md")
        t, ld = tables(path), leads(path)
        if not t:
            print("%s: n/a\n" % w["label"])
            continue
        # the report's form drops the last column (the EBs of the class each host validated) with the tentative costs
        print("**Table 7.2%s.** %s (%s): %s\n" % (next(letters), w["label"], w["shape"], ld[0] if full else compact_lead(ld[0])))
        head = t[0][0] if full else t[0][0][:-1]
        print("| " + " | ".join(head) + " |")
        print("|---|" + "---|" * (len(head) - 1))
        for row in t[0][1:]:
            print("| " + " | ".join(row if full else [blank(c) for c in row[:-1]]) + " |")
        print()
    if cluster:
        print("**Table 7.3.** the cluster runs, c5d.2xlarge at two capabilities, every node: the lower quartile, median and upper quartile node of the run's most common EB size class.\n")
        print("| run | EBs | per applied transaction, milliseconds | per reapplied transaction, microseconds |" + (" EBs validated per node |" if full else ""))
        print("|---|---|---|---|" + ("---|" if full else ""))
        for name in cluster:
            w = WINDOWS[name]
            path = os.path.join(outputs, name, "validation_shape.md")
            t, ld = tables(path), leads(path)
            if not t:
                print("| %s | n/a | | |" % w["label"] + (" |" if full else ""))
                continue
            row = t[0][1]
            print("| %s (%s) | %s | %s | %s |" % (w["label"], w["shape"], class_cell(ld[0]), row[2], row[3]) + (" %s |" % row[4] if full else ""))
        print()


def kind(outputs, names):
    """The within-kind check: one window's closures of one transaction size by their same-block input
    share (validation_shape_kind.md, one table per band), the hosts by class."""
    print("| population | EB class | same-block share of the closure's inputs | host class (instance, vCPU, generation) | hosts | per applied transaction, milliseconds (EBs per host) | per reapplied transaction, microseconds (EBs per host) |")
    print("|---|---|---|---|---|---|---|")
    for name in names:
        w = WINDOWS[name]
        path = os.path.join(outputs, name, "validation_shape_kind.md")
        for lead, tab in zip(leads(path), tables(path)):
            m = re.search(r"in which (.*?) of the inputs", lead)
            for row in tab[1:]:
                if not row[0].startswith("operators"):
                    print("| %s | %s | %s | %s | %s | %s | %s |" % (w["label"], class_cell(lead), m.group(1) if m else "", row[0], row[1], row[2], row[3]))


def series(outputs, names):
    """The size series (validation_shape_series.md): the chained closures of one transaction size
    across the EB size classes on the testnet, and the classes the cluster runs populate, one row per
    population, class and host class with both costs; read in 7.2's and 7.3's prose, not a table of
    the report."""
    print("| population | EB class | host class (instance, vCPU, generation) | hosts | per applied transaction, milliseconds (EBs per host) | per reapplied transaction, microseconds (EBs per host) | EBs validated per host |")
    print("|---|---|---|---|---|---|---|")
    for name in names:
        w = WINDOWS[name]
        path = os.path.join(outputs, name, "validation_shape_series.md")
        for lead, tab in zip(leads(path), tables(path)):
            for row in tab[1:]:
                if not row[0].startswith("operators"):
                    print("| %s | %s | %s | %s | %s | %s | %s |" % (w["label"], class_cell(lead), row[0], row[1], row[2], row[3], row[4]))


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
    ap.add_argument("table", choices=["bins", "shape", "series", "kind", "resources", "unseen", "speed"])
    ap.add_argument("windows", nargs="+", metavar="WINDOW")
    ap.add_argument("--outputs", default=OUTPUTS)
    ap.add_argument("--full", action="store_true", help="shape: the expanded tables (the tentative cells' costs and the EBs validated per host)")
    a = ap.parse_args()
    bad = [w for w in a.windows if w not in WINDOWS]
    if bad:
        sys.exit("unknown window %s" % ", ".join(bad))
    if a.table == "shape":
        shape(a.outputs, a.windows, a.full)
        return
    {"bins": bins, "series": series, "kind": kind, "resources": resources, "unseen": unseen, "speed": speed}[a.table](a.outputs, a.windows)


if __name__ == "__main__":
    main()
