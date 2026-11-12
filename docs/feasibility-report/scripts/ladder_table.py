#!/usr/bin/env python3
"""The throughput ladder (report section 4, table a) of one parameter set,
printed as Markdown from the ladder exports of chain.py ceiling, one column
per population and window.

    ladder_table.py [--outputs DIR] WINDOW [WINDOW ...]

WINDOW     a key of LADDERS below (testnet windows and cluster runs)
--outputs  the saved outputs folder (default: outputs/ in this repository),
           holding <WINDOW>/ladder.jsonl

Each export is a ladder.jsonl written by `instruments/ladder.py ceiling --export`: one
JSON object per range with the rungs under "ladder" (level, note, kbs, tps)
and the factors (p_model, p_obs, s_full, s_all, f_observed, tx_size,
announce_share, eb_fullness, rb_fullness). The table shows kB/s per rung
with the rung's annotation (seconds per RB and p observed; s_full or s_all;
the three load factors) in a second line of the cell, as agreed for the
report on 2026-10-30. Rungs a window does not have (the "mix" rung when
full and mix agree) print as a dash.
"""
import argparse, json, os

LADDERS = {
    "f1-high": "testnet 40 kB / 260 kB, loaded hours",
    "f2-high": "testnet 308 kB / 2 MB, loaded hours",
    "1kb": "testnet 308 kB / 2 MB, 1 kB transactions",
    "cluster-40k260k": "cluster 40 kB / 260 kB, 200 B",
    "cluster-100k1m": "cluster 100 kB / 1 MB, 200 B",
    "cluster-100k1m-374": "cluster 100 kB / 1 MB, 374 B",
    "cluster-100k1m-374-patched": "cluster 100 kB / 1 MB, 374 B, changed build",
}
OUTPUTS = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "outputs"))
RUNGS = ["parameter ceiling", "workload ceiling", "observed spacing", "voting-adjusted, mix", "voting-adjusted, full", "load-adjusted", "measured"]
# rungs that assume one transaction size (the binding cap and the "full EB" threshold at the measured size, the EB fullness),
# left out (printed as a dash) where two sizes coexisted in the window
OMIT = {"1kb": {"workload ceiling", "voting-adjusted, full", "load-adjusted"}}


def annotate(level, d, rung):
    if level == "parameter ceiling":
        return "p = %.3f" % d["p_model"]
    if level == "workload ceiling":
        return "%s at %.0f B/tx" % (d["binds"], d["tx_size"])
    if level == "observed spacing":
        return "1 RB / %.1f s, p = %.3f" % (1 / d["f_observed"], d["p_obs"])
    if level == "voting-adjusted, mix":
        return "s_all = %.3f" % d["s_all"]
    if level == "voting-adjusted, full":
        return "s_full = %.3f" % d["s_full"]
    if level == "load-adjusted":
        return "announcing %.2f, EB %.2f, plain RB %.2f" % (d["announce_share"], d["eb_fullness"], d["rb_fullness"])
    return ""


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("windows", nargs="+", choices=sorted(LADDERS))
    ap.add_argument("--outputs", default=OUTPUTS)
    a = ap.parse_args()
    cols = []
    for name in a.windows:
        label = LADDERS[name]
        with open(os.path.join(a.outputs, name, "ladder.jsonl")) as f:
            d = json.loads(f.readline())
        cols.append((label, d, {r["level"]: r for r in d["ladder"] if r["level"] not in OMIT.get(name, set())}))
    print("| rung, kB/s | " + " | ".join(c[0] for c in cols) + " |")
    print("|---|" + "---|" * len(cols))
    for level in RUNGS:
        if not any(level in c[2] for c in cols):
            continue
        cells = []
        for label, d, rungs in cols:
            r = rungs.get(level)
            if r is None:
                cells.append("-")
                continue
            note = annotate(level, d, r)
            cells.append("%.1f%s" % (r["kbs"], (" (" + note + ")") if note else ""))
        print("| %s | %s |" % (level, " | ".join(cells)))
    for label, d, _ in cols:
        print("\n%s: %s; tx/s at the measured size (%.0f B): %.1f." % (label, d["scope"], d["tx_size"], [r for r in d["ladder"] if r["level"] == "measured"][0]["tps"] or 0))


if __name__ == "__main__":
    main()
