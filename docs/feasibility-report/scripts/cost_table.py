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
         speed     the cluster records repriced on faster hosts and with the loop's cost
                   removed (host_speed.md, first table), runs side by side;
                   section 8, Table 8.4
         combined  the loop's cost removed combined with each host generation
                   on a cluster run (host_speed_combined.md); Table 8.5
         hardware  the testnet records repriced by host class to a certification
                   rate under a calibrated quorum (a testnet window's
                   host_speed.md), one table per window; no longer a table of
                   the report, kept for the saved outputs
         capacity  the transactions a voter applies in 2, 3 and 4 s at each
                   host class's apply cost, with the loop's cost and with it
                   removed, from the costs the drivers take (no window); Table 8.6
         votes     the testnet votes repriced by host class, the pessimistic
                   rebuild and the loop's cost removed, read per vote (a
                   testnet window's voter_reprice.md): one table per window and
                   the first window's by-EB-size table; Tables 8.3a to 8.3c
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


SPEED_COLS = "certification | kB/s | tx/s | quorum voter validated at, s: p50 / p90"


def speed(outputs, names, path="host_speed.md"):
    """The cluster repricing (host_speed.md, section 8): one row per lever, the runs given side by side, with the
    certification, the throughput at the run's transaction size and the time at which the voter completing
    the quorum has validated (the saved output's last column, the transactions that voter could have
    validated by the deadline, is not printed: the repricing keeps the reapplied counts, so it misreads)."""
    runs = []
    for name in names:
        t = tables(os.path.join(outputs, name, path))
        if t:
            runs.append((WINDOWS[name]["label"], t[0]))
    if not runs:
        return
    print("| voters' speed | " + " | ".join("%s: %s" % (label, SPEED_COLS) for label, _ in runs) + " |")
    print("|---|" + "---|" * (4 * len(runs)))
    rows = {}
    order = []
    for label, tab in runs:
        for row in tab[1:]:
            if row[0] not in rows:
                rows[row[0]] = {}
                order.append(row[0])
            rows[row[0]][label] = row[4:8]
    for key in order:
        cells = []
        for label, _ in runs:
            cells.extend(rows[key].get(label, ["-"] * 4))
        print("| %s | %s |" % (key, " | ".join(cells)))


def combined(outputs, names):
    """The loop's cost removed combined with each host generation's measured costs (host_speed_combined.md)."""
    speed(outputs, names, path="host_speed_combined.md")


def hardware(outputs, names):
    """The testnet repricing (host_speed.md of a testnet window, section 8): one table per window, the rows as
    recorded, hardware alone, and the pessimistic rebuild at each host class, with the loop-fix column group."""
    letters = iter("abcdefgh")
    for name in names:
        w = WINDOWS[name]
        t = tables(os.path.join(outputs, name, "host_speed.md"))
        if not t:
            print("%s: n/a\n" % w["label"])
            continue
        print("**Table 8.3%s.** %s (%s).\n" % (next(letters), w["label"], w["shape"]))
        print("| voters' speed and closures | %s | with the loop's cost removed: %s |" % (SPEED_COLS, SPEED_COLS))
        print("|---|" + "---|" * 10)
        for row in t[0][1:]:
            print("| %s | %s | %s |" % (row[0], " | ".join(row[2:7]), " | ".join(row[8:13])))
        print()


def votes(outputs, names, size_bin="4,000 to 6,000"):
    """The testnet votes repriced (voter_reprice.md of a testnet window, section 8): per window the per-vote table,
    rows as recorded, hardware alone, the rebuilt rows and the chained rows (Tables 8.3a, 8.3b), with the window's
    lead line as the caption's figures; then the first window's table for the EB size bin named (Table 8.3c)."""
    letters = iter("abcdefgh")
    first = None
    for name in names:
        w = WINDOWS[name]
        path = os.path.join(outputs, name, "voter_reprice.md")
        t, lead = tables(path), leads(path)
        if not t:
            print("%s: n/a\n" % w["label"])
            continue
        print("**Table 8.3%s.** %s (%s).\n" % (next(letters), w["label"], w["shape"]))
        print("| " + " | ".join(t[0][0]) + " |")
        print("|---|" + "---|" * (len(t[0][0]) - 1))
        for row in t[0][1:]:
            print("| " + " | ".join(row) + " |")
        print("\nCaption, %s: %s\n" % (name, lead[0]))
        if first is None:
            first = (name, w, t, lead)
    if first:
        name, w, t, lead = first
        for i, l in enumerate(lead[1:], 1):
            if l.startswith("EBs of %s transactions" % size_bin) and i < len(t):
                print("**Table 8.3%s.** %s (%s), the EBs of %s transactions.\n" % (next(letters), w["label"], w["shape"], size_bin))
                print("| " + " | ".join(t[i][0]) + " |")
                print("|---|" + "---|" * (len(t[i][0]) - 1))
                for row in t[i][1:]:
                    print("| " + " | ".join(row) + " |")
                print("\nCaption, %s: %s\n" % (name, l))


# the apply cost per transaction by host class, ms, with the loop's cost (old-input closures, Table 7.2b and the
# c5d reading of Table 7.3 scaled by the hardware factors, as the 2 MB windows' repricing takes them) and with it
# removed (the chained cost of Table 7.2b)
CAPACITY = [("c5d", 1.85, 0.35), ("c6id", 1.57, 0.31), ("current generation", 1.11, 0.20)]


def capacity(outputs, names, budgets=(2.0, 3.0, 4.0)):
    """The transactions a voter applies in a budget of seconds at each host class's apply cost, every
    transaction applied (the worst case), with the loop's cost and with it removed (section 8.2)."""
    print("| host class, apply cost per transaction | " + " | ".join("in %g s" % b for b in budgets) + " |")
    print("|---|" + "---|" * len(budgets))
    for cls, old, chained in CAPACITY:
        for label, cost in (("with the loop's cost (%.2f ms)" % old, old), ("the loop's cost removed (%.2f ms)" % chained, chained)):
            print("| %s, %s | %s |" % (cls, label, " | ".join("{:,}".format(int(round(b * 1000.0 / cost, -2))) for b in budgets)))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("table", choices=["bins", "shape", "series", "kind", "resources", "unseen", "speed", "combined", "hardware", "votes", "capacity"])
    ap.add_argument("windows", nargs="*", metavar="WINDOW")
    ap.add_argument("--outputs", default=OUTPUTS)
    ap.add_argument("--full", action="store_true", help="shape: the expanded tables (the tentative cells' costs and the EBs validated per host)")
    ap.add_argument("--size-bin", default="4,000 to 6,000",
                    help="votes: the EB size bin of Table 8.3c, as the instrument labels it (default '4,000 to 6,000')")
    a = ap.parse_intermixed_args()
    bad = [w for w in a.windows if w not in WINDOWS]
    if bad:
        sys.exit("unknown window %s" % ", ".join(bad))
    if a.table == "shape":
        shape(a.outputs, a.windows, a.full)
        return
    if a.table == "votes":
        votes(a.outputs, a.windows, a.size_bin)
        return
    if a.table == "capacity":
        capacity(a.outputs, a.windows)
        return
    if not a.windows:
        sys.exit("a window is needed")
    {"bins": bins, "series": series, "kind": kind, "resources": resources, "unseen": unseen, "speed": speed, "combined": combined, "hardware": hardware}[a.table](a.outputs, a.windows)


if __name__ == "__main__":
    main()
