-- Per (node, EB) validation record over the loaded hours of a testnet period:
-- applied and reapplied counts (EbValidated), closure arrival
-- (BlockTxsAcquired), the validated time, and the EB's slot time. Duration =
-- validated - max(closure, slot + 3 s), as in the F1 fit. Written to CSV for
-- the regression (fit_validation.py) and for the stage table's validation
-- row (p90 per node, median node).
--
-- Variables: t0, t1 the period's bounds (UTC, 'YYYY-MM-DD HH:MM:SS'), win a
-- windows file of `start end` pairs (the loaded hours; an EB counts by the
-- time of its slot), slot0 (default 1792281600, the 2026-10-18 chain). The
-- CSV is validation_pairs.csv in the current directory.
--
--   duckdb -readonly archive/f2-high-merged.duckdb \
--     -c "set variable t0 = '2026-10-24 12:00:00'; set variable t1 = '2026-10-26 13:00:00'; set variable win = 'windows-f2-high.txt';" \
--     -f validation_pairs.sql
set timezone = 'UTC';
create temp table p as
  select getvariable('t0')::timestamptz t0, getvariable('t1')::timestamptz t1,
         coalesce(getvariable('slot0'), 1792281600)::bigint slot0;
create temp table win as
  select epoch(s::timestamp) s, epoch(e::timestamp) e
  from read_csv(getvariable('win'), delim = ' ', header = false, columns = {'s': 'varchar', 'e': 'varchar'}, ignore_errors = true)
  where s not like '#%';
-- extract first, then filter: a filter on data->>x straight on trace makes DuckDB cast other namespaces' payloads
create temp table ev as
  select agent, pool, data->>'$.ebHash' eb, t validated_t,
         try_cast(data->>'$.applied' as bigint) applied, try_cast(data->>'$.reapplied' as bigint) reapplied,
         try_cast(data->>'$.ebSlot' as bigint) eb_slot
  from trace, p where ns = 'Consensus.LeiosKernel.EbValidated' and t >= p.t0 and t < p.t1;
create temp table cl as
  select agent, data->>'$.ebHash' eb, min(t) closure_t
  from trace, p where ns = 'Consensus.LeiosKernel.BlockTxsAcquired' and t >= p.t0 and t < p.t1
  group by 1, 2;
create temp table rec as
  select ev.agent, ev.pool, ev.eb, ev.eb_slot, ev.applied, ev.reapplied,
         epoch(ev.validated_t) - (p.slot0 + ev.eb_slot) validated_s,
         epoch(cl.closure_t) - (p.slot0 + ev.eb_slot) closure_s,
         epoch(ev.validated_t) - greatest(epoch(cl.closure_t), p.slot0 + ev.eb_slot + 3) duration_s
  from ev join cl on cl.agent = ev.agent and cl.eb = ev.eb, p
  where ev.applied is not null and ev.reapplied is not null
    and exists (select 1 from win w where p.slot0 + ev.eb_slot >= w.s and p.slot0 + ev.eb_slot < w.e);
copy rec to 'validation_pairs.csv' (header, delimiter ',');
-- the per-node summary the stage table reads (validation_nodes.csv): records, p90 of the duration, applied and reapplied sums;
-- the per-pair file above is the input of the regression and stays outside the report repository
copy (select agent, count(*) records, quantile_cont(duration_s, 0.9) p90, sum(applied) applied, sum(reapplied) reapplied from rec group by 1 order by 1)
  to 'validation_nodes.csv' (header, delimiter ',');
select count(*) records, count(distinct agent) agents, count(distinct eb) ebs from rec;
-- the stage table's row: p90 of the duration per node (100+ records), median and quartiles across nodes
select count(*) nodes, round(median(p90), 2) p90_median_node, round(quantile_cont(p90, 0.25), 2) p90_q1, round(quantile_cont(p90, 0.75), 2) p90_q3,
       round(median(applied_pct), 1) applied_pct_median_node
from (select agent, quantile_cont(duration_s, 0.9) p90, 100.0 * sum(applied) / sum(applied + reapplied) applied_pct
      from rec group by 1 having count(*) >= 100);
