-- The adoption path of an RB at the reporting nodes, by RB kind, for the
-- Praos section of the report: for each (node, RB on the final chain) in the
-- loaded windows, seconds after the RB's slot start at which the body
-- arrived (BlockFetch CompletedBlockFetch), chain selection started
-- (ChainDB PoppedBlockFromQueue) and the RB was adopted (AddedToCurrentChain
-- or SwitchedToAFork), and the validation inside chain selection as a
-- duration (ValidCandidate minus PoppedBlockFromQueue; on the F2 pulls equal
-- to the chain-sel-add-block call). The cluster counterpart is
-- cluster_adoption_path.sql. Kinds: certifying by the closure it certifies
-- (the parent's EB closure), plain by size. Slot 0 = 1792281600.
--
-- Variables t0, t1 (UTC 'YYYY-MM-DD HH:MM:SS'), win (a windows file; without
-- it the whole period), chain (the chain cache, default
-- chain-2026-10-18/blocks.sqlite under the working directory, the data folder):
--   duckdb -readonly -markdown archive/f2-high-merged.duckdb \
--     -c "set variable t0 = '2026-10-24 12:00:00'; set variable t1 = '2026-10-26 13:00:00'; set variable win = '<repo>/data/windows/windows-f2-high.txt';" \
--     -f <repo>/scripts/instruments/adoption_path.sql > <repo>/outputs/f2-high/adoption_path.md
set timezone = 'UTC';
create temp table p as
  select getvariable('t0')::timestamptz t0, getvariable('t1')::timestamptz t1, 1792281600::bigint slot0;
create temp table chainblk as
  select * from sqlite_scan(coalesce(getvariable('chain'), 'chain-2026-10-18/blocks.sqlite'), 'block') where slot_no is not null;
create temp table win as
  select epoch(s::timestamp) s, epoch(e::timestamp) e
  from read_csv(coalesce(getvariable('win'), '/dev/null'), delim = ' ', header = false, columns = {'s': 'varchar', 'e': 'varchar'}, ignore_errors = true)
  where s not like '#%';
create temp table rb as
  select b.hash, b.slot_no, b.has_leios_cert certifies, b.size, b.tx_count, pr.eb_closure_size closure, p.slot0 + b.slot_no t_slot
  from chainblk b left join chainblk pr on pr.block_no = b.block_no - 1, p
  where p.slot0 + b.slot_no >= epoch(p.t0) and p.slot0 + b.slot_no < epoch(p.t1)
    and (not exists (select 1 from win) or exists (select 1 from win w where p.slot0 + b.slot_no >= w.s and p.slot0 + b.slot_no < w.e));
create temp table ev as
  select agent, hash, min(t) filter (where k = 'fetch') t_fetch, min(t) filter (where k = 'pop') t_pop,
         min(t) filter (where k = 'valid') t_valid, min(t) filter (where k = 'adopt') t_adopt
  from (
    select agent, data->>'$.block' hash, 'fetch' k, epoch(t) t from trace, p where ns = 'BlockFetch.Client.CompletedBlockFetch' and t >= p.t0 and t < p.t1 + interval 1 hour
    union all
    select agent, data->'$.block'->>'$.hash', 'pop', epoch(t) from trace, p where ns = 'ChainDB.AddBlockEvent.PoppedBlockFromQueue' and t >= p.t0 and t < p.t1 + interval 1 hour
    union all
    select agent, split_part(data->>'$.block', '@', 1), 'valid', epoch(t) from trace, p where ns = 'ChainDB.AddBlockEvent.AddBlockValidation.ValidCandidate' and t >= p.t0 and t < p.t1 + interval 1 hour
    union all
    select agent, split_part(data->>'$.newtip', '@', 1), 'adopt', epoch(t) from trace, p where ns in ('ChainDB.AddBlockEvent.AddedToCurrentChain', 'ChainDB.AddBlockEvent.SwitchedToAFork') and t >= p.t0 and t < p.t1 + interval 1 hour
  ) group by 1, 2;
create temp table d as
  select r.*, e.agent, e.t_fetch - r.t_slot body, e.t_pop - r.t_slot popped, e.t_valid - e.t_pop validation, e.t_adopt - r.t_slot adopted
  from rb r join ev e using (hash);
select case when certifies = 1 and closure >= 1500000 then 'd certifies, closure 1.5-2 MB'
            when certifies = 1 and closure >= 1000000 then 'c certifies, closure 1-1.5 MB'
            when certifies = 1 and closure >= 500000 then 'b certifies, closure 0.5-1 MB'
            when certifies = 1 then 'a certifies, closure < 0.5 MB'
            when size >= 80000 then 'f plain RB, 80-88 kB' else 'e plain RB, < 80 kB' end kind,
       count(distinct hash) rbs, count(*) node_rbs, count(distinct agent) nodes,
       round(quantile_cont(closure, 0.5)) closure_p50, round(quantile_cont(tx_count, 0.5)) txs_p50,
       round(quantile_cont(body, 0.5), 2) body_p50, round(quantile_cont(body, 0.9), 2) body_p90,
       round(quantile_cont(validation, 0.5), 3) validation_p50, round(quantile_cont(validation, 0.9), 3) validation_p90,
       round(quantile_cont(adopted, 0.5), 2) adopted_p50, round(quantile_cont(adopted, 0.9), 2) adopted_p90,
       round(100.0 * sum(case when adopted <= 1 then 1 else 0 end) / count(*), 1) within_1s_pct
from d where adopted between -5 and 120 and (validation is null or validation between 0 and 60) group by 1 order by 1;
