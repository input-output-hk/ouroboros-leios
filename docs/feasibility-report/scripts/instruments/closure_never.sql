-- What the "never completed" closures of the stage table are: per (reporting
-- node, EB heard announced within 60 s), whether the closure
-- (BlockTxsAcquired) and the body (BlockAcquired) ever arrived, split by the
-- EB's fate on the chain: certified, eligible but failed (next RB 14+ slots
-- later, no certificate), superseded within the gap (next RB under 14 slots),
-- or off the chain (the announcing RB lost its fork). Shares are of node-EB
-- pairs; the stage table's never-completed share is the same quantity at the
-- median node over the loaded hours, here over the whole period.
--
-- Variables: t0, t1 (period bounds, UTC), gap (default 14), chain (default
-- chain-2026-10-18/blocks.sqlite under the working directory, the data folder).
--
--   duckdb -readonly -markdown archive/f2-high-merged.duckdb \
--     -c "set variable t0 = '2026-10-24 12:00:00'; set variable t1 = '2026-10-26 13:00:00';" -f closure_never.sql
set timezone = 'UTC';
create temp table p as
  select getvariable('t0')::timestamptz t0, getvariable('t1')::timestamptz t1, coalesce(getvariable('gap'), 14)::int gap;
-- extract first, then filter: a filter on data->>x straight on trace makes DuckDB cast other namespaces' payloads
create temp table ev as
  select agent, ns, data->>'$.ebHash' eb, data->>'$.source' src, try_cast(data->>'$.announcementAgeSeconds' as double) ann
  from trace, p where ns in ('Consensus.LeiosKernel.AnnouncementAccepted', 'Consensus.LeiosKernel.BlockTxsAcquired', 'Consensus.LeiosKernel.BlockAcquired')
    and t >= p.t0 and t < p.t1;
create temp table pair as
  select eb, agent, bool_or(ns like '%BlockAcquired') body, bool_or(ns like '%BlockTxsAcquired') closure
  from ev where eb is not null group by 1, 2
  having bool_or(ns like '%AnnouncementAccepted' and src <> 'forgedLocally') and min(ann) filter (where ns like '%AnnouncementAccepted') <= 60;
create temp table chainblk as
  select b.eb_announcement_hash eb, b.eb_announcement_size / 36 txs, n.slot_no - b.slot_no gap, n.has_leios_cert certified
  from sqlite_scan(coalesce(getvariable('chain'), 'chain-2026-10-18/blocks.sqlite'), 'block') b
  join sqlite_scan(coalesce(getvariable('chain'), 'chain-2026-10-18/blocks.sqlite'), 'block') n on n.block_no = b.block_no + 1
  where b.eb_announcement_hash is not null;
select case when c.eb is null then 'd off chain (orphaned RB)'
            when c.gap >= p.gap and c.certified = 1 then 'a certified'
            when c.gap >= p.gap then 'b eligible, not certified'
            else 'c superseded within the gap' end eb_fate,
       count(*) pairs, round(100.0 * count(*) / (select count(*) from pair), 1) share_of_pairs,
       round(100.0 * sum((not closure)::int) / count(*), 1) closure_never_pct,
       round(100.0 * sum((not body)::int) / count(*), 1) body_never_pct
from pair q left join chainblk c using (eb), p group by 1 order by 1;
select 'all node-EB pairs' what, count(*) pairs, round(100.0 * sum((not closure)::int) / count(*), 1) closure_never_pct from pair;
select case when txs < 2000 then 'a under 2,000 txs' when txs < 4000 then 'b 2,000-4,000' when txs < 6000 then 'c 4,000-6,000' else 'd 6,000 and up' end eb_txs,
       count(*) pairs, round(100.0 * sum((not closure)::int) / count(*), 1) closure_never_pct
from pair join chainblk c using (eb), p where c.gap >= p.gap group by 1 order by 1;
