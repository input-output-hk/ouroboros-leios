#!/usr/bin/env python3
"""The throughput ladder and the size percentiles of a window or a cluster
run, from a chain cache alone (report section 2.3 and the ladder tables of
section 4). This is the read-only part of the analysis folder's chain tool
(`chain.py ceiling` and `chain.py sizes`), without its fetch command; the
computation is the same line for line.

    ladder.py ceiling --chain blocks.sqlite (--windows FILE | --from T --to T [--all]) [--gap 14] [--rb-bytes 90112]
                      [--ref-cap B --payload-cap B] [--tx-size B] [--export ladder.jsonl]
    ladder.py sizes   --chain blocks.sqlite (--windows FILE | --from T --to T) [--gap 14]

--chain      the chain cache (the testnet's, or a cluster run's reconstructed one)
--committee  committee.sqlite with the Leios parameters per epoch (default: next
             to the chain cache); gives the caps when --ref-cap/--payload-cap are
             not passed (a cluster run has no committee file: pass the caps)
--windows    a file of `start end` pairs (UTC, one per line, `#` comments) pooled
             as the range; --from/--to the range otherwise, whole (--all) or its
             busy 10-minute bins only (10+ announced EBs per bin)
--gap        the certification gap in slots (14 on the 2026-10-18 chain and the
             later cluster runs, 15 on the first cluster run)
--rb-bytes   a full plain RB in bytes (the Praos block limit, 90,112)

Rungs, each dropping one assumption:
  parameter ceiling      every RB announces a full EB at the payload cap, perfect
                         voting, modelled spacing p = (1-f)^(G-1)
  workload ceiling       EB payload limited by the cap that binds at the measured
                         transaction size
  observed spacing       the measured RB rate and gap share instead of the model
  voting-adjusted, mix   p times the survival of all eligible EBs, with the p90
                         size of the ones that survived (only when it differs from
                         the full-EB survival by 2 points or more)
  voting-adjusted, full  p times the measured survival of full EBs (99 % of the
                         binding capacity)
  load-adjusted          what the load actually fed: share of RBs announcing an
                         EB, EB payload over its cap, plain RB size over the limit
  measured               what the chain carried
Times are UTC: YYYY-MM-DD or YYYY-MM-DDTHH:MM[:SS].
"""
import argparse, json, math, os, sqlite3
from datetime import datetime, timezone
from pathlib import Path

EXT = """
with ext as (
  select b.*,
         n.has_leios_cert as certified,
         n.slot_no - b.slot_no as gap_slots,
         n.tx_count as certified_txs
  from block b left join block n on n.block_no = b.block_no + 1
)
"""


def parse_time(s):
    if s is None:
        return None
    for fmt in ("%Y-%m-%dT%H:%M:%S", "%Y-%m-%dT%H:%M", "%Y-%m-%d"):
        try:
            return datetime.strptime(s, fmt).replace(tzinfo=timezone.utc)
        except ValueError:
            pass
    raise SystemExit(f"cannot parse time {s!r}; use YYYY-MM-DD or YYYY-MM-DDTHH:MM")


def iso(t):
    return t.strftime("%Y-%m-%dT%H:%M:%SZ")


def read_windows(path):
    windows = []
    for line in Path(path).read_text().splitlines():
        line = line.split("#", 1)[0].strip()
        if line:
            a, b = line.split()
            windows.append((parse_time(a), parse_time(b)))
    if not windows:
        raise SystemExit(f"no windows in {path}")
    return windows


def scope_clause(args):
    """(where, params, windows or None, scope label)."""
    if args.windows:
        windows = read_windows(args.windows)
        where = "(" + " or ".join("(time >= ? and time < ?)" for _ in windows) + ")"
        params = tuple(x for a, b in windows for x in (iso(a), iso(b)))
        return where, params, windows, f"{len(windows)} windows from {Path(args.windows).name}"
    t0, t1 = parse_time(args.from_), parse_time(args.to)
    if t0 is None or t1 is None:
        raise SystemExit("--windows or --from and --to are required")
    return "time >= ? and time < ?", (iso(t0), iso(t1)), None, f"{iso(t0)} .. {iso(t1)}"


def caps_for_range(args, db, where, params):
    """The EB caps in force: the flags if given, else the Leios parameters per
    epoch in the committee file for the range's first epoch, else the
    pre-change values."""
    if args.ref_cap and args.payload_cap:
        return args.ref_cap, args.payload_cap, "from flags"
    committee = Path(args.committee) if args.committee else Path(args.chain).with_name("committee.sqlite")
    epoch = db.execute(f"select min(epoch_no) from block where {where}", params).fetchone()[0]
    if epoch is not None and committee.exists():
        cm = sqlite3.connect(committee)
        row = cm.execute("select refs_cap, txs_cap from params where epoch = ?", (epoch,)).fetchone()
        cm.close()
        if row:
            return args.ref_cap or row[0], args.payload_cap or row[1], f"{committee.name}, epoch {epoch}"
    return args.ref_cap or 100_000, args.payload_cap or 1_000_000, "defaults (no committee row for the range)"


def cmd_ceiling(args):
    db = sqlite3.connect(f"file:{args.chain}?mode=ro", uri=True)
    where, params, windows, scope = scope_clause(args)
    if windows:
        args.all = True
    step = args.minutes * 60
    bin_filter = "" if args.all else f"""
      and (strftime('%s', time) / {step}) * {step} in (
        select (strftime('%s', time) / {step}) * {step} from block where {where}
        group by 1 having sum(eb_announcement_hash is not null) >= {args.min_ebs})"""
    ref_cap, payload_cap, cap_source = caps_for_range(args, db, where, params)
    q = EXT + f"""
    select count(*) blocks,
           count(distinct (strftime('%s', time) / {step}) * {step}) bins,
           sum(eb_announcement_hash is not null) announced,
           sum(eb_announcement_hash is not null and gap_slots >= {args.gap}) eligible,
           sum(certified = 1) certified,
           avg(case when eb_announcement_hash is not null then eb_announcement_size end) avg_ref,
           sum(case when certified = 1 then eb_closure_size end) eb_bytes,
           sum(case when certified = 1 then certified_txs end) eb_txs,
           sum(case when has_leios_cert = 0 then size end) rb_bytes,
           sum(case when has_leios_cert = 0 then tx_count end) rb_txs,
           sum(has_leios_cert = 0) plain_blocks
    from ext where {where} {bin_filter}"""
    qparams = params if args.all else params + params
    (blocks, bins, announced, eligible, certified,
     avg_ref, eb_bytes, eb_txs, rb_bytes, rb_txs, plain_blocks) = db.execute(q, qparams).fetchone()
    if not blocks or not announced:
        print("no announced EBs in range")
        return
    if windows:
        secs = sum((b - a).total_seconds() for a, b in windows)
    elif args.all:
        t0, t1 = db.execute(f"select min(time), max(time) from block where {where}", params).fetchone()
        secs = max((parse_time(t1[:19]) - parse_time(t0[:19])).total_seconds(), 1)
    else:
        secs = bins * step
    f_obs = blocks / secs
    f = args.active_slot_coeff
    G = args.gap
    # Geometric gap: an RB in each slot with probability f, so P(next RB >= G slots away) = (1-f)^(G-1).
    p_model = (1 - f) ** (G - 1)
    p_obs = eligible / announced
    s_all = certified / eligible if eligible else float("nan")
    tx_size = args.tx_size if args.tx_size else (eb_bytes / eb_txs if eb_txs else 204.0)
    E_txs_ref = ref_cap / 36.0
    E_bytes_workload = min(payload_cap, E_txs_ref * tx_size)
    binds = "payload cap" if payload_cap < E_txs_ref * tx_size else "reference cap"
    E_txs_workload = E_bytes_workload / tx_size
    # an EB is as full as the cap that binds; "full" is 99 % of that capacity in reference bytes
    full_ref_bytes = args.full_bytes if args.full_bytes else 0.99 * E_txs_workload * 36
    eligible_full, certified_full = db.execute(EXT + f"""
        select sum(eb_announcement_hash is not null and gap_slots >= {args.gap} and eb_announcement_size >= {full_ref_bytes}),
               sum(certified = 1 and eb_announcement_size >= {full_ref_bytes})
        from ext where {where} {bin_filter}""", qparams).fetchone()
    s_full = certified_full / eligible_full if eligible_full else float("nan")
    announce_share = announced / blocks
    fullness = avg_ref / (E_txs_workload * 36)
    rb_fullness = (rb_bytes / plain_blocks / args.rb_bytes) if plain_blocks else 1.0
    R_B = args.rb_bytes
    R_T = args.rb_txs if args.rb_txs else R_B / tx_size

    def row(p, E_b, E_t, fill_eb=1.0, fill_rb=1.0, ann=1.0, rate=None):
        rate = f if rate is None else rate
        q_ = ann * p
        kbs = rate * (q_ * E_b * fill_eb + (1 - q_) * R_B * fill_rb) / 1000
        tps = rate * (q_ * E_t * fill_eb + (1 - q_) * R_T * fill_rb) if E_t else None
        return kbs, tps

    measured_kbs = ((eb_bytes or 0) + (rb_bytes or 0)) / secs / 1000
    measured_tps = ((eb_txs or 0) + (rb_txs or 0)) / secs
    cert_sizes = [r[0] for r in db.execute(EXT + f"""
        select eb_closure_size from ext where {where} {bin_filter} and certified = 1 and eb_closure_size is not null
        order by eb_closure_size""", qparams)]
    cert_p90_bytes = cert_sizes[min(len(cert_sizes) - 1, int(0.9 * len(cert_sizes)))] if cert_sizes else float("nan")
    ladder = [
        ("parameter ceiling", f"payload cap {payload_cap / 1e6:g} MB, f = {f:g} (1 RB / {1 / f:.0f} s), p = (1-f)^(G-1) = {p_model:.3f}", row(p_model, payload_cap, None)),
        ("workload ceiling", f"{binds} binds at {tx_size:.0f} B/tx ({'given' if args.tx_size else 'measured'}): E = {E_bytes_workload / 1000:.0f} KB, {E_txs_workload:,.0f} txs", row(p_model, E_bytes_workload, E_txs_workload)),
        ("observed spacing", f"observed 1 RB / {1 / f_obs:.1f} s and p observed = {p_obs:.3f}", row(p_obs, E_bytes_workload, E_txs_workload, rate=f_obs)),
    ]
    if not math.isnan(s_all) and not math.isnan(s_full) and abs(s_all - s_full) >= 0.02:
        ladder.append(("voting-adjusted, mix", f"x s_all = {s_all:.3f} (certified/eligible of all EBs; certified closure p90 = {cert_p90_bytes / 1000:,.0f} KB, {cert_p90_bytes / tx_size:,.0f} txs)",
                       row(p_obs * s_all, E_bytes_workload, E_txs_workload, rate=f_obs)))
    ladder += [
        ("voting-adjusted, full", f"x s_full = {s_full:.3f} (certified/eligible of full EBs; cap at sustained full load)", row(p_obs * s_full, E_bytes_workload, E_txs_workload, rate=f_obs)),
        ("load-adjusted", f"x s_all = {s_all:.3f} (actual mix); RBs announcing {announce_share:.3f}; EB payload {fullness:.3f} of its cap; plain RB {rb_fullness:.3f} of the block limit", row(p_obs * s_all, E_bytes_workload, E_txs_workload, fullness, rb_fullness, announce_share, rate=f_obs)),
        ("measured", "", (measured_kbs, measured_tps)),
    ]
    if windows:
        scope = f"{len(windows)} windows from {Path(args.windows).name}, {secs / 3600:.0f} h"
    elif args.all:
        scope = "whole range"
    else:
        scope = f"{bins} busy bins of {args.minutes} min (>= {args.min_ebs} announced EBs)"
    print(f"range {params[0]} .. {params[-1]}, {scope}")
    print(f"RBs {blocks} (observed 1 RB / {1 / f_obs:.1f} s; nominal f = {f:g}), G = {G} slots, EBs announced {announced}, eligible {eligible}, certified {certified}")
    print(f"caps: references {ref_cap:,} B, payload {payload_cap:,} B ({cap_source}); "
          f"full EB = reference list >= {full_ref_bytes / 1000:.0f} KB (99 % of the binding capacity)")
    print()
    tps_hdr = f"TPS@{tx_size:.0f}B"
    print(f"{'level':22} {'tx KB/s':>8} {tps_hdr:>10}   assumption")
    for name, note, (kbs, tps) in ladder:
        tps_s = f"{tps:10.1f}" if tps is not None else f"{'-':>10}"
        print(f"{name:22} {kbs:8.2f} {tps_s}   {note}")
    if args.export:
        clean = lambda x: None if isinstance(x, float) and math.isnan(x) else x
        rec = {"from": params[0], "to": params[-1], "scope": scope, "f": f, "f_observed": f_obs, "G": G, "p_model": p_model, "p_obs": p_obs,
               "s_full": clean(s_full), "s_all": clean(s_all), "tx_size": tx_size, "announce_share": announce_share,
               "eb_fullness": fullness, "rb_fullness": rb_fullness,
               "ref_cap": ref_cap, "payload_cap": payload_cap, "binds": binds,
               "ladder": [{"level": n, "note": t, "kbs": k, "tps": tp} for n, t, (k, tp) in ladder]}
        path = Path(args.export)
        kept = []
        if path.exists():
            for line in path.read_text().splitlines():
                if not line.strip():
                    continue
                old = json.loads(line)
                if not (old.get("from") == rec["from"] and old.get("to") == rec["to"] and old.get("scope") == rec["scope"]):
                    kept.append(line)
        kept.append(json.dumps(rec))
        path.write_text("\n".join(kept) + "\n")
        print(f"\nwritten to {Path(args.export).name} ({len(kept)} range(s))")


def cmd_sizes(args):
    """Percentiles of EB size over a range: transactions for every eligible EB
    (reference bytes / 36), closure bytes and bytes per transaction for the
    certified ones."""
    db = sqlite3.connect(f"file:{args.chain}?mode=ro", uri=True)
    where, params, _, scope = scope_clause(args)
    rows = db.execute(EXT + f"""
        select eb_announcement_size / 36, certified, eb_closure_size, certified_txs
        from ext where {where} and eb_announcement_hash is not null and gap_slots >= {args.gap}""", params).fetchall()
    if not rows:
        print("no eligible EBs in range")
        return
    pcts = [10, 25, 50, 75, 90]

    def pct(values, p):
        values = sorted(values)
        return values[min(len(values) - 1, int(p / 100 * len(values)))]

    def line(label, values, fmt):
        cells = " ".join(f"{fmt(pct(values, p)):>10}" for p in pcts) + f" {fmt(max(values)):>10}"
        print(f"{label:34} {len(values):6} {cells}")

    elig = [r[0] for r in rows]
    cert = [r for r in rows if r[1] == 1 and r[2] is not None and r[3]]
    fail = [r[0] for r in rows if r[1] == 0]
    print(f"range {scope}: eligible EBs {len(elig)}, certified {len(cert)}, failed {len(fail)} ({100.0 * len(cert) / len(elig):.0f} % certified)")
    print(f"{'population':34} {'n':>6} " + " ".join(f"{'p' + str(p):>10}" for p in pcts) + f" {'max':>10}")
    n = lambda v: f"{v:,.0f}"
    kb = lambda v: f"{v / 1000:,.0f} KB"
    line("eligible EBs, txs", elig, n)
    line("certified EBs, txs", [r[3] for r in cert], n)
    line("certified EBs, closure", [r[2] for r in cert], kb)
    line("certified EBs, B/tx", [r[2] / r[3] for r in cert], n)
    if fail:
        line("failed EBs, txs", fail, n)
    print("(txs from the reference list, 36 B each; closure bytes exist on chain for certified EBs only)")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name, fn in (("ceiling", cmd_ceiling), ("sizes", cmd_sizes)):
        p = sub.add_parser(name)
        p.add_argument("--chain", required=True)
        p.add_argument("--committee")
        p.add_argument("--windows")
        p.add_argument("--from", dest="from_")
        p.add_argument("--to")
        p.add_argument("--gap", type=int, default=14)
        p.set_defaults(fn=fn)
        if name == "ceiling":
            p.add_argument("--all", action="store_true")
            p.add_argument("--minutes", type=int, default=10)
            p.add_argument("--min-ebs", type=int, default=10)
            p.add_argument("--active-slot-coeff", type=float, default=0.05)
            p.add_argument("--ref-cap", type=int)
            p.add_argument("--payload-cap", type=int)
            p.add_argument("--full-bytes", type=int)
            p.add_argument("--rb-bytes", type=int, default=90_112)
            p.add_argument("--rb-txs", type=int)
            p.add_argument("--tx-size", type=float)
            p.add_argument("--export")
    args = ap.parse_args()
    args.fn(args)


if __name__ == "__main__":
    main()
