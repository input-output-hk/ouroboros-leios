#!/usr/bin/env python3
"""Per-node EB reception table for a period, from a telemetry DuckDB.

One row per reporting node (agent, pool): how many EBs it received from
peers, the chosen percentiles of the arrival age (seconds after the EB's
slot) of the chosen stage (--stage closure, the default: all transactions
present; or --stage body: the EB's reference list arrived), the share of its
EBs with that stage complete before each chosen moment, the share never
completed, and how many upstream peers delivered announcements. Optionally a
cause column from a CSV you maintain by hand.

    python3 diffusion_nodes.py --db archive/f2-high-merged.duckdb \
        --from 2026-10-24T12:00:00 --to 2026-10-26T13:00:00 \
        --percentiles 90,95,99 --before 3,4,5,7 --sort p90 \
        --exclude 2026-10-24T13:00:00,2026-10-24T14:00:00 ... --out diffusion.md --csv diffusion.csv
(the driver testnet_window.sh builds this call from the window's file)

Inputs: a period database built by archive/archive.sql (table `trace`), the
`duckdb` CLI on PATH, and optionally a pool_id,ticker CSV (--tickers) for
the ticker column. Pairs whose announcement age exceeds --max-ann (60 s) are dropped:
a re-syncing node accepts hours-old announcements and the age then measures
its lag, not diffusion. Only EBs the node received (not its own forge).

Sort keys: any output column name (agent, ticker, upstream, ebs, p<N>,
slowest, lt<S>, never, cause). Default: p50 descending (worst first).
"""
import argparse
import csv
import io
import os
import statistics
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.normpath(os.path.join(HERE, "..", "..", ".."))  # the data folder (DATA.md): the parent of the report repository
TICKERS = os.path.join(DATA, "chain-2026-10-18", "tickers.csv")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--db", required=True, help="period DuckDB with the trace table")
    ap.add_argument("--from", dest="from_", required=True, help="UTC start, YYYY-MM-DD[THH:MM:SS]")
    ap.add_argument("--to", required=True, help="UTC end (exclusive)")
    ap.add_argument("--stage", choices=["closure", "body"], default="closure",
                    help="which arrival to measure: closure (BlockTxsAcquired, closureAgeSeconds; default) or body (BlockAcquired, bodyAgeSeconds)")
    ap.add_argument("--percentiles", default="50,90,95,99", help="closure age percentiles to show (default 50,90,95,99); the max is always added as 'slowest'")
    ap.add_argument("--before", default="3,4,5,7", help="moments in seconds after the slot: share of EBs with closure complete before each (default 3,4,5,7)")
    ap.add_argument("--min-ebs", type=int, default=50, help="drop nodes with fewer received EBs (default 50)")
    ap.add_argument("--max-ann", type=float, default=60, help="drop pairs whose announcement age exceeds this (default 60 s)")
    ap.add_argument("--sort", default="p50", help="column to sort by (default p50)")
    ap.add_argument("--asc", action="store_true", help="ascending sort (default descending)")
    ap.add_argument("--causes", help="CSV with columns agent,cause (optional pool column for agents shared by several pools)")
    ap.add_argument("--chain", default=os.path.join(DATA, "chain-2026-10-18", "blocks.sqlite"),
                    help="the chain cache, used to map a vote's announcing RB to its EB (default chain-2026-10-18/blocks.sqlite "
                         "in the data folder); 'none' disables the vote columns")
    ap.add_argument("--out", help="write the markdown table here (default: print)")
    ap.add_argument("--csv", help="also write the same rows as CSV (raw values, bucket counts as n_* columns)")
    ap.add_argument("--exclude", action="append", default=[], metavar="START,END",
                    help="UTC window to leave out, as START,END (repeatable), e.g. 2026-10-15T11:42:14,2026-10-15T12:17:12; "
                         "an EB is left out by the time of its slot (see --slot0)")
    ap.add_argument("--tickers", default=TICKERS,
                    help="CSV with pool_id,ticker columns for the ticker column (default chain-2026-10-18/tickers.csv in the data folder)")
    ap.add_argument("--slot0", type=int, default=1792281600,
                    help="unix time of slot 0 of the chain the traces come from (default 1792281600 = 2026-10-18 00:00 UTC, the "
                         "restarted testnet's genesis; a cluster run's is its logged system start); used by --exclude only")
    a = ap.parse_args()

    stage_ns, stage_field = {"closure": ("Consensus.LeiosKernel.BlockTxsAcquired", "closureAgeSeconds"),
                             "body": ("Consensus.LeiosKernel.BlockAcquired", "bodyAgeSeconds")}[a.stage]
    pcts = [int(x) for x in a.percentiles.split(",") if x]
    befores = [float(x) for x in a.before.split(",") if x]
    t0, t1 = norm(a.from_), norm(a.to)
    votes = a.chain != "none" and os.path.exists(a.chain)
    if a.chain != "none" and not votes:
        print(f"note: chain cache {a.chain} not found, vote columns skipped", file=sys.stderr)

    pct_sql = ", ".join(f"round(quantile_cont(c,{p/100}),2) as p{p}" for p in pcts)
    before_sql = ", ".join(f"round(100.0*count(c) filter (where c<{s})/count(*),1) as lt{fmt(s)}" for s in befores)
    # vote rate on eligible EBs per closure-arrival bucket: [-inf,b0), [b0,b1), ..., [b_last, inf) with never in the last
    edges = [None] + befores + [None]
    buckets = []
    for lo, hi in zip(edges[:-1], edges[1:]):
        name = "v_lt" + fmt(hi) if lo is None else ("v_ge" + fmt(lo) if hi is None else f"v_{fmt(lo)}_{fmt(hi)}")
        cond = f"c < {hi}" if lo is None else (f"(c >= {lo} or c is null)" if hi is None else f"c >= {lo} and c < {hi}")
        buckets.append((name, cond))
    vote_sql = ""
    if votes:
        vote_sql = ", count(*) filter (where not tip_refused) as eligible, round(100.0*count(*) filter (where voted)/nullif(count(*) filter (where not tip_refused),0),1) as vote_pct"
        for name, cond in buckets:
            vote_sql += f", round(100.0*count(*) filter (where voted and {cond})/nullif(count(*) filter (where not tip_refused and {cond}),0),1) as {name}, count(*) filter (where not tip_refused and {cond}) as n_{name[2:]}"
    tick_join = f"left join (select pool_id, any_value(ticker) ticker from read_csv('{a.tickers}') group by 1) tk on tk.pool_id = p.pool" if os.path.exists(a.tickers) else ""
    tick_col = "coalesce(any_value(tk.ticker), '')" if tick_join else "''"
    attach = f"attach '{a.chain}' as chain (type sqlite, read_only);" if votes else ""
    vote_ctes = f"""
, voted as (
  select v.agent, v.pool, b.eb_announcement_hash eb
  from (select agent, pool, data->>'$.vote.rbHash' rb from trace where ns = 'Consensus.LeiosKernel.Voted'
        and t >= timestamptz '{t0}+00' and t < timestamptz '{t1}+00') v
  join chain.block b on b.hash = v.rb where b.eb_announcement_hash is not null group by all),
refused as (
  -- extract first, then filter on the extracted value: a filter on data->>x straight on trace
  -- makes DuckDB cast other namespaces' payloads and fail
  select agent, pool, eb from (
    select agent, pool, data->>'$.ebHash' eb, data->>'$.reason' reason from trace
    where ns = 'Consensus.LeiosKernel.NotVoted' and t >= timestamptz '{t0}+00' and t < timestamptz '{t1}+00')
  where reason = 'chainTipDoesNotAnnounce' group by all)""" if votes else ""
    vote_flags = ("exists (select 1 from voted v where v.agent = p.agent and v.pool = p.pool and v.eb = p.eb) as voted, "
                  "exists (select 1 from refused r where r.agent = p.agent and r.pool = p.pool and r.eb = p.eb) as tip_refused") if votes else "false as voted, false as tip_refused"
    # validation cost: txs the node applied in full (not already validated through its mempool) vs reapplied
    val_cte = f""",
val as (
  select agent, pool, data->>'$.ebHash' eb,
         max(try_cast(data->>'$.applied' as bigint)) applied, max(try_cast(data->>'$.reapplied' as bigint)) reapplied
  from trace where ns = 'Consensus.LeiosKernel.EbValidated'
    and t >= timestamptz '{t0}+00' and t < timestamptz '{t1}+00' group by all)"""
    val_cols = (", round(100.0*sum(val.applied)/nullif(sum(val.applied + val.reapplied),0),1) as applied_pct, "
                "count(val.eb) as validated")
    # excluded windows, applied to the EB's slot time (slot 0 = 1788739200)
    excl = []
    for w in a.exclude:
        s, e = (norm(x) for x in w.split(","))
        excl.append((s, e))
    excl_sql = "".join(f" and not ({a.slot0} + p.slot >= epoch(timestamptz '{s}+00') and {a.slot0} + p.slot < epoch(timestamptz '{e}+00'))" for s, e in excl)
    sql = f"""{attach}
with ev as (
  select agent, pool, ns, data->>'$.ebHash' eb,
         coalesce(try_cast(data->>'$.ebSlot' as bigint), try_cast(data->>'$.electionSlot' as bigint)) slot,
         try_cast(data->>'$.announcementAgeSeconds' as double) ann,
         try_cast(data->>'$.{stage_field}' as double) clo, data->>'$.source' src
  from trace
  where ns in ('Consensus.LeiosKernel.AnnouncementAccepted','{stage_ns}')
    and t >= timestamptz '{t0}+00' and t < timestamptz '{t1}+00'),
pair0 as (
  select eb, agent, pool, min(slot) slot,
         min(ann) filter (where ns like '%AnnouncementAccepted') a,
         min(clo) filter (where ns = '{stage_ns}') c
  from ev where eb is not null group by all
  having bool_or(ns like '%AnnouncementAccepted' and src <> 'forgedLocally')),
up as (
  select agent, pool, count(distinct data->>'$.peer.connectionId') ups
  from trace where ns = 'Consensus.LeiosPeer.Announcement'
    and t >= timestamptz '{t0}+00' and t < timestamptz '{t1}+00' group by 1, 2){vote_ctes}{val_cte},
pair as (select p.*, {vote_flags} from pair0 p)
select p.agent, p.pool, {tick_col} as ticker, coalesce(any_value(up.ups), 0) as upstream, count(*) as ebs,
       {pct_sql}, round(max(c),1) as slowest,
       {before_sql},
       round(100.0*count(*) filter (where c is null)/count(*),1) as never{vote_sql}{val_cols}
from pair p left join up using (agent, pool) {tick_join}
left join val on val.agent = p.agent and val.pool = p.pool and val.eb = p.eb
where a is not null and a <= {a.max_ann}{excl_sql}
group by p.agent, p.pool having count(*) >= {a.min_ebs}
"""
    res = subprocess.run(["duckdb", "-readonly", a.db, "-csv"], input=sql, capture_output=True, text=True)
    if res.returncode != 0:
        sys.exit(res.stderr)
    rows = list(csv.DictReader(io.StringIO(res.stdout)))
    if not rows:
        sys.exit("no rows: check the period and the database")

    causes = {}
    if a.causes:
        for r in csv.DictReader(open(a.causes)):
            causes[(r["agent"], r.get("pool", "") or "")] = r["cause"]
        for r in rows:
            r["cause"] = causes.get((r["agent"], r["pool"][:12])) or causes.get((r["agent"], "")) or ""

    vote_cols = (["eligible", "vote_pct"] + [name for name, _ in buckets]) if votes else []
    cols = ["agent", "ticker", "upstream", "ebs"] + [f"p{p}" for p in pcts] + ["slowest"] + [f"lt{fmt(s)}" for s in befores] + ["never"] + vote_cols + ["applied_pct", "validated"] + (["cause"] if a.causes else [])
    if a.sort not in cols:
        sys.exit(f"--sort must be one of {', '.join(cols)}")
    numeric = a.sort not in ("agent", "ticker", "cause")
    rows.sort(key=lambda r: (r["agent"], r["pool"]))  # tie-break, so reruns give the same order
    rows.sort(key=(lambda r: float(r[a.sort] or 0)) if numeric else (lambda r: r[a.sort]), reverse=not a.asc)

    out = []
    out.append(f"Period {t0} to {t1} UTC" + (", leaving out " + "; ".join(f"{s} to {e}" for s, e in excl) if excl else "")
               + f", database `{os.path.basename(a.db)}`, stage {a.stage}, {len(rows)} nodes with at least {a.min_ebs} received EBs, "
               f"sorted by {a.sort} {'ascending' if a.asc else 'descending'}. Ages in seconds after the EB's slot, measured at the "
               f"{'closure completion (all transactions present)' if a.stage == 'closure' else 'EB body arrival (the reference list, before the transactions)'}; "
               f"lt<S> = share of the node's EBs with the {a.stage} before S s; never = announced but no {a.stage}."
               + (" Vote columns: eligible = received EBs minus those refused because the announcing RB was not the chain tip; "
                  "vote% = votes / eligible; the bucketed vote% columns are the same rate restricted to EBs whose closure arrived "
                  "in that interval of seconds (never-completed closures fall in the last bucket), with the eligible count in parentheses."
                  if votes else ""))
    out.append("")
    head = ["#"] + [pretty(c) for c in cols]
    out.append("| " + " | ".join(head) + " |")
    out.append("|" + "---|" * len(head))
    for i, r in enumerate(rows, 1):
        vals = []
        for c in cols:
            v = r.get(c, "")
            if v == "NULL":
                v = ""
            if c.startswith("lt") or c == "never":
                v = f"{float(v):.1f}%" if v != "" else "-"
            elif c in ("vote_pct", "applied_pct"):
                v = f"{float(v):.0f}%" if v != "" else "-"
            elif c.startswith("v_"):
                n = r.get("n_" + c[2:], "0")
                v = (f"{float(v):.0f}% ({n})" if v != "" else f"- ({n})")
            vals.append(str(v))
        out.append(f"| {i} | " + " | ".join(vals) + " |")
    out.append("")
    out.append(f"Nodes by the share of the EBs each node received (announced to it, not forged by it) whose {a.stage} was complete before each moment:")
    out.append("")
    out.append(f"| {a.stage} complete | on 90%+ of EBs | on 75%+ | on half or more | below half | median node |")
    out.append("|---|---|---|---|---|---|")
    for s in befores:
        v = [float(r[f"lt{fmt(s)}"]) for r in rows if r.get(f"lt{fmt(s)}", "") not in ("", "NULL")]  # a node with no completed closure has NULL shares
        out.append(f"| before {fmt(s)} s | {sum(1 for x in v if x >= 90)} | {sum(1 for x in v if x >= 75)} | {sum(1 for x in v if x >= 50)} | {sum(1 for x in v if x < 50)} | {statistics.median(v):.0f}% |")
    text = "\n".join(out) + "\n"
    if a.csv:
        csv_cols = ["agent", "pool"] + cols[1:]
        if votes:
            csv_cols += ["n_" + name[2:] for name, _ in buckets]
        with open(a.csv, "w", newline="") as f:
            w = csv.writer(f)
            w.writerow(csv_cols)
            for r in rows:
                w.writerow([("" if r.get(c, "") == "NULL" else r.get(c, "")) for c in csv_cols])
        print(f"wrote {a.csv}")
    if a.out:
        with open(a.out, "w") as f:
            f.write(text)
        print(f"wrote {a.out} ({len(rows)} nodes)")
    else:
        print(text)


def norm(s):
    return s if "T" in s else s + "T00:00:00"


def fmt(s):
    return str(int(s)) if float(s).is_integer() else str(s).replace(".", "_")


def pretty(c):
    if c.startswith("lt"):
        return "< " + c[2:].replace("_", ".") + " s"
    if c.startswith("v_lt"):
        return "vote% < " + c[4:].replace("_", ".") + " s"
    if c.startswith("v_ge"):
        return "vote% ≥ " + c[4:].replace("_", ".") + " s or never"
    if c.startswith("v_"):
        lo, hi = c[2:].rsplit("_", 1)
        return f"vote% {lo.replace('_', '.')} to {hi.replace('_', '.')} s"
    return {"ebs": "EBs", "upstream": "upstream", "vote_pct": "vote%", "eligible": "eligible",
            "applied_pct": "applied%", "validated": "validated"}.get(c, c)


if __name__ == "__main__":
    main()
