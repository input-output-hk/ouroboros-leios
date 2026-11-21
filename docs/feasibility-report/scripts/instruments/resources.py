#!/usr/bin/env python3
"""Memory and CPU of the nodes over a window or run (report section 6.4),
as distributions across nodes, no node named except the IOG and PIR hosts
by instance class. Printed as Markdown.

Testnet window:
    resources.py testnet --db archive/f2-high-merged.duckdb --t0 '2026-10-24 12:00:00' --t1 '2026-10-26 13:00:00' \
        --mimir grafana/archive/mimir/f2-high --hosts <repo>/data/hosts.csv > resources.md
  reads the operators' metric scrapes in the period database (one row per
  scrape: cardano_node_metrics_Mem_resident_int, RTS_gcLiveBytes_int,
  Stat_cputicks_int, RTS_gcticks_int, RTS_mutticks_int) and the IOG and PIR
  hosts' per-minute series pulled from the IOG monitoring (DATA.md): the
  same node metrics plus the host's total memory, memory utilisation and
  CPU busy fraction (a five-minute rate across all cores).
Cluster run:
    resources.py cluster --resources raw/Resources.db > resources.md
  reads the nodes' resource traces (one row per node and second: RSS, Heap,
  Live, CentiCpu, CentiGC, CentiMut, NetRd, NetWr).

Per node: the resident set at the median and the peak sample, the GC live
data at its peak, the process CPU as cores (differences of the cumulative
tick counters over the sampling interval; its median and 90th-percentile
interval), the GC share of CPU time; then the distribution of each across
the nodes. The series average over a minute (testnet) or a second
(cluster) and across all cores, so they show the sustained load and the
memory, not whether a core was saturated during a validation.
"""
import argparse, csv, glob, json, os, sqlite3, subprocess, statistics as st
from collections import defaultdict


def q(v, p):
    v = sorted(v)
    i = (len(v) - 1) * p
    lo = int(i)
    return v[lo] + (v[min(lo + 1, len(v) - 1)] - v[lo]) * (i - lo)


def per_node(series):
    """series: dict metric -> sorted list of (t seconds, value). Returns the node's summary or None."""
    rss = [v for _, v in series.get("rss", [])]
    if not rss:
        return None
    out = {"rss_p50": q(rss, .5) / 1e9, "rss_max": max(rss) / 1e9, "gc_live_max": max([v for _, v in series.get("live", [])] or [0]) / 1e9}
    # CPU rate over intervals of at least 60 s: the tick counters advance coarsely (the cluster's every ~10 s,
    # the scrapes every minute), so shorter intervals quantise to 0 or to a whole burst
    cpu = series.get("cpu", [])
    rates, last = [], None
    for t, v in cpu:
        if last is None:
            last = (t, v)
            continue
        if t - last[0] >= 60:
            d = v - last[1]
            if 0 <= d < 100 * 64 * (t - last[0]):   # a reset or a bogus counter is skipped
                rates.append((d / 100.0) / (t - last[0]))
            last = (t, v)
    out["cores_p50"] = q(rates, .5) if rates else None
    out["cores_p90"] = q(rates, .9) if rates else None
    if out["cores_p50"] is not None and out["cores_p50"] > 32:   # a counter in another unit; not a core count
        out["cores_p50"] = out["cores_p90"] = None
    gc, tot = series.get("gc", []), cpu
    if gc and tot:
        pos = lambda s: sum(b[1] - a[1] for a, b in zip(s, s[1:]) if 0 <= b[1] - a[1] < 100 * 64 * max(b[0] - a[0], 1))
        dg, dt = pos(gc), pos(tot)
        out["gc_share"] = dg / dt if dt > 0 and dg <= dt else None
    else:
        out["gc_share"] = None
    return out


def table(title, nodes, extra=None):
    print("| %s, %d nodes | p10 | median | p90 | max |" % (title, len(nodes)))
    print("|---|---|---|---|---|")
    rows = [("resident set at the node's median sample, GB", "rss_p50", "%.1f"), ("resident set at the node's peak sample, GB", "rss_max", "%.1f"),
            ("GC live data at the peak, GB", "gc_live_max", "%.1f"), ("process CPU, cores, the node's median interval", "cores_p50", "%.2f"),
            ("process CPU, cores, the node's 90th-percentile interval", "cores_p90", "%.2f"), ("GC share of the process CPU time", "gc_share", "%.2f")]
    for label, k, fmt in rows:
        v = [n[k] for n in nodes if n.get(k) is not None]
        if v:
            print("| %s | %s | %s | %s | %s |" % (label, fmt % q(v, .1), fmt % q(v, .5), fmt % q(v, .9), fmt % max(v)))
    if extra:
        for label, v in extra:
            print("| %s | %s |" % (label, v))


def testnet(a):
    sql = """set timezone = 'UTC';
    select agent, name, epoch(t) t, value from metric
    where name in ('cardano_node_metrics_Mem_resident_int', 'cardano_node_metrics_RTS_gcLiveBytes_int', 'cardano_node_metrics_Stat_cputicks_int', 'cardano_node_metrics_RTS_gcticks_int')
      and t >= '%s' and t < '%s' order by agent, name, t;""" % (a.t0, a.t1)
    res = subprocess.run(["duckdb", "-readonly", "-csv", a.db, "-c", sql], capture_output=True, text=True, check=True)
    key = {"cardano_node_metrics_Mem_resident_int": "rss", "cardano_node_metrics_RTS_gcLiveBytes_int": "live",
           "cardano_node_metrics_Stat_cputicks_int": "cpu", "cardano_node_metrics_RTS_gcticks_int": "gc"}
    series = defaultdict(lambda: defaultdict(list))
    for r in csv.DictReader(res.stdout.splitlines()):
        series[r["agent"]][key[r["name"]]].append((float(r["t"]), float(r["value"])))
    hosts = {r["agent"]: r for r in csv.DictReader(open(a.hosts, newline=""))} if a.hosts else {}
    ops = [per_node(s) for ag, s in series.items() if ag not in hosts]
    ops = [n for n in ops if n]
    print("Operators' nodes, from their telemetry scrapes (about one per minute), %s to %s UTC." % (a.t0, a.t1))
    print()
    table("operator nodes", ops)
    if a.mimir:
        t0, t1 = [st.mean([0]) for _ in range(2)]
        import datetime as dt
        t0 = dt.datetime.fromisoformat(a.t0).replace(tzinfo=dt.timezone.utc).timestamp()
        t1 = dt.datetime.fromisoformat(a.t1).replace(tzinfo=dt.timezone.utc).timestamp()
        ms = defaultdict(lambda: defaultdict(list))
        for path in sorted(glob.glob(os.path.join(a.mimir, "*.jsonl.zst"))):
            p = subprocess.Popen(["zstd", "-dc", path], stdout=subprocess.PIPE)
            for line in p.stdout:
                r = json.loads(line)
                if t0 <= r["ts"] < t1:
                    ms[r["instance"]][r["metric"]].append((r["ts"], r["value"]))
            p.wait()
        mkey = {"cardano_node_metrics_Mem_resident_int": "rss", "cardano_node_metrics_RTS_gcLiveBytes_int": "live",
                "cardano_node_metrics_Stat_cputicks_int": "cpu", "cardano_node_metrics_RTS_gcticks_int": "gc"}
        cls = defaultdict(list)
        for inst, m in ms.items():
            s = {mkey[k]: sorted(v) for k, v in m.items() if k in mkey}
            n = per_node(s)
            if not n:
                continue
            n["mem_total"] = q([v for _, v in m.get("node_memory_MemTotal_bytes", [])], .5) / 1e9 if m.get("node_memory_MemTotal_bytes") else None
            n["host_cpu_p50"] = q([v for _, v in m.get("instance:node_cpu_utilisation:rate5m", [])], .5) if m.get("instance:node_cpu_utilisation:rate5m") else None
            n["host_cpu_max"] = max([v for _, v in m.get("instance:node_cpu_utilisation:rate5m", [])] or [0])
            h = hosts.get(inst, {"instance": inst, "vcpu": "", "generation": "", "deployment": "", "host": inst})
            cls[(h["instance"], h["vcpu"], h["generation"], h["deployment"])].append((h["host"], n))
        print()
        print("IOG and PIR hosts, from the per-minute series of the IOG monitoring, by instance class.")
        print()
        print("| host class | hosts | host memory, GB | resident set, median / peak, GB | GC live peak, GB | process CPU, cores, median / p90 interval | GC share | host CPU busy, median / peak (all cores, 5-minute rate) |")
        print("|---|---|---|---|---|---|---|---|")
        rng = lambda xs, fmt: "-" if not xs else ((fmt % xs[0]) if len(xs) == 1 or min(xs) == max(xs) else (fmt % min(xs)) + " to " + (fmt % max(xs)))
        for (inst, vcpu, gen, dep), hs in sorted(cls.items(), key=lambda kv: kv[0]):
            ns = [n for _, n in hs]
            g = lambda k: [n[k] for n in ns if n.get(k) is not None]
            print("| %s, %s vCPU | %s | %s | %s / %s | %s | %s / %s | %s | %s / %s |" % (
                inst, vcpu, ", ".join(sorted(h for h, _ in hs)), rng(g("mem_total"), "%.0f"), rng(g("rss_p50"), "%.1f"), rng(g("rss_max"), "%.1f"),
                rng(g("gc_live_max"), "%.1f"), rng(g("cores_p50"), "%.2f"), rng(g("cores_p90"), "%.2f"), rng(g("gc_share"), "%.2f"),
                rng(g("host_cpu_p50"), "%.2f"), rng(g("host_cpu_max"), "%.2f")))


def cluster(a):
    db = sqlite3.connect("file:%s?mode=ro" % a.resources, uri=True)
    series = defaultdict(lambda: defaultdict(list))
    for f, t, rss, live, cpu, gc in db.execute('select file, at_ns / 1e9, "data.RSS", "data.Live", "data.CentiCpu", "data.CentiGC" from "Resources" order by file, at_ns'):
        s = series[f]
        s["rss"].append((t, rss)); s["live"].append((t, live)); s["cpu"].append((t, cpu)); s["gc"].append((t, gc))
    nodes = [n for n in (per_node(s) for s in series.values()) if n]
    print("Cluster nodes, from their resource traces (one sample per second); the hosts are c5d.2xlarge with 15.2 GiB.")
    print()
    table("cluster nodes", nodes)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    t = sub.add_parser("testnet")
    t.add_argument("--db", required=True); t.add_argument("--t0", required=True); t.add_argument("--t1", required=True)
    t.add_argument("--mimir"); t.add_argument("--hosts")
    t.set_defaults(fn=testnet)
    c = sub.add_parser("cluster")
    c.add_argument("--resources", required=True)
    c.set_defaults(fn=cluster)
    a = ap.parse_args()
    a.fn(a)


if __name__ == "__main__":
    main()
