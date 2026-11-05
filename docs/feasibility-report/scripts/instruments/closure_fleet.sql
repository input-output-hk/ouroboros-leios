-- The per-EB view of closure diffusion for under the stage table (the tail):
-- for each eligible EB over the loaded hours of a testnet period, the age
-- (seconds after its slot) by which 90 % and 95 % of the reporting nodes
-- that received it (announcement age <= 60 s, 40+ nodes) held its closure
-- (BlockTxsAcquired.closureAgeSeconds; a node that never completed counts
-- as infinite, shown as 1e9), then the distribution of those ages over EBs,
-- the share of EBs whose closure 90 % of the nodes held by 3 s and by 7 s,
-- and the same by EB size (transactions = reference bytes / 36) with the
-- certified closures' median bytes. The per-EB rows are written to
-- closure_fleet_per_eb.csv in the current directory.
--
-- Variables as in validation_pairs.sql: t0, t1, win, gap (default 14), slot0
-- (default 1792281600), chain (default chain-2026-10-18/blocks.sqlite under the
-- working directory, the data folder).
--
--   duckdb -readonly -markdown archive/f2-high-merged.duckdb \
--     -c "set variable t0 = '2026-10-24 12:00:00'; set variable t1 = '2026-10-26 13:00:00'; set variable win = 'windows-f2-high.txt';" \
--     -f closure_fleet.sql
set timezone = 'UTC';
create temp table p as
  select getvariable('t0')::timestamptz t0, getvariable('t1')::timestamptz t1,
         coalesce(getvariable('slot0'), 1792281600)::bigint slot0, coalesce(getvariable('gap'), 14)::int gap;
create temp table win as
  select epoch(s::timestamp) s, epoch(e::timestamp) e
  from read_csv(getvariable('win'), delim = ' ', header = false, columns = {'s': 'varchar', 'e': 'varchar'}, ignore_errors = true)
  where s not like '#%';
create temp table chainblk as
  select block_no, slot_no, hash, eb_announcement_hash, eb_announcement_size, eb_closure_size, has_leios_cert
  from sqlite_scan(coalesce(getvariable('chain'), 'chain-2026-10-18/blocks.sqlite'), 'block');
create temp table ebs as
  select b.eb_announcement_hash eb, b.slot_no slot, b.eb_announcement_size / 36 txs, b.eb_closure_size closure, n.has_leios_cert certified
  from chainblk b join chainblk n on n.block_no = b.block_no + 1, p
  where b.eb_announcement_hash is not null and n.slot_no - b.slot_no >= p.gap
    and exists (select 1 from win w where p.slot0 + b.slot_no >= w.s and p.slot0 + b.slot_no < w.e);
-- extract first, then filter: a filter on data->>x straight on trace makes DuckDB cast other namespaces' payloads
create temp table ev as
  select agent, ns, data->>'$.ebHash' eb, try_cast(data->>'$.closureAgeSeconds' as double) age,
         try_cast(data->>'$.announcementAgeSeconds' as double) ann
  from trace, p where ns in ('Consensus.LeiosKernel.AnnouncementAccepted', 'Consensus.LeiosKernel.BlockTxsAcquired')
    and t >= p.t0 and t < p.t1 + interval 1 hour;
create temp table pair as
  select eb, agent,
         min(age) filter (where ns = 'Consensus.LeiosKernel.BlockTxsAcquired') closure_s,
         min(ann) filter (where ns = 'Consensus.LeiosKernel.AnnouncementAccepted') ann_s
  from ev where eb in (select eb from ebs) group by 1, 2 having
         min(ann) filter (where ns = 'Consensus.LeiosKernel.AnnouncementAccepted') <= 60;
create temp table per_eb as
  select eb, txs, closure, certified, count(*) nodes,
         quantile_cont(coalesce(closure_s, 1e9), 0.9) t90, quantile_cont(coalesce(closure_s, 1e9), 0.95) t95
  from pair join ebs using (eb) group by 1, 2, 3, 4 having count(*) >= 40;
copy (select * from per_eb order by eb) to 'closure_fleet_per_eb.csv' (header, delimiter ',');
select 'EBs' what, count(*) n, round(100.0 * avg(certified)) pct_certified,
       round(quantile_cont(t90, 0.5), 2) t90_p50, round(quantile_cont(t90, 0.9), 2) t90_p90,
       round(quantile_cont(t95, 0.5), 2) t95_p50, round(quantile_cont(t95, 0.9), 2) t95_p90,
       round(100.0 * sum(t90 < 3) / count(*)) pct_ebs_t90_lt3, round(100.0 * sum(t90 < 7) / count(*)) pct_ebs_t90_lt7,
       round(100.0 * sum(t95 < 7) / count(*)) pct_ebs_t95_lt7
from per_eb;
select case when txs < 2000 then 'a under 2,000 txs' when txs < 4000 then 'b 2,000-4,000' when txs < 6000 then 'c 4,000-6,000' else 'd 6,000 and up' end eb_txs,
       count(*) ebs, round(100.0 * avg(certified)) pct_certified,
       round(quantile_cont(closure, 0.5) filter (where certified = 1) / 1e3) closure_kB_certified_p50,
       round(quantile_cont(t90, 0.5), 2) t90_p50, round(quantile_cont(t90, 0.9), 2) t90_p90,
       round(100.0 * sum(t90 < 7) / count(*)) pct_ebs_t90_lt7, round(100.0 * sum(t95 < 7) / count(*)) pct_ebs_t95_lt7
from per_eb group by 1 order by 1;
