-- Adoption delay of RBs across the reporting nodes: for each (node, RB on
-- the final chain) the time from the RB's slot to the node's
-- ChainDB AddedToCurrentChain of it, by RB kind (certifying, with the size
-- of the closure it certifies = the parent's EB closure; plain, by size)
-- and by hour parity (even = loaded in the F2 period). Slot 0 = 1792281600.
-- The test that the adoption delay of a certifying RB is set by its closure
-- and not by the hosts' load (ANALYSIS-2026-10-24-F2.md, Praos section).
--
-- Run from the data folder (DATA.md), as the driver testnet_window.sh does:
--   duckdb -readonly -markdown archive/f1-high-merged.duckdb -c "set variable t0 = '2026-10-21 12:00:00'; set variable t1 = '2026-10-22 01:00:00'; set variable win = '<repo>/data/windows/windows-f1-high.txt';" -f <repo>/scripts/instruments/adoption_delay.sql
-- Variables t0, t1 (UTC 'YYYY-MM-DD HH:MM:SS') bound the period; without win the rows split by hour
-- parity (even = loaded, which holds for the F2 period and the 1 kB window); with win (a windows
-- file) the RBs are restricted to the loaded windows and all rows are labelled "loaded", which is
-- the report's reading for every window.
-- The chain cache is the variable chain (default chain-2026-10-18/blocks.sqlite under the working directory).
set timezone = 'UTC';
create temp table p as
  select coalesce(getvariable('t0'), '2026-10-24 12:00:00')::timestamptz t0, coalesce(getvariable('t1'), '2026-10-26 12:00:00')::timestamptz t1;
create temp table chainblk as
  select * from sqlite_scan(coalesce(getvariable('chain'), 'chain-2026-10-18/blocks.sqlite'), 'block') where slot_no is not null;
create temp table win as
  select epoch(s::timestamp) s, epoch(e::timestamp) e
  from read_csv(coalesce(getvariable('win'), '/dev/null'), delim = ' ', header = false, columns = {'s': 'varchar', 'e': 'varchar'}, ignore_errors = true)
  where s not like '#%';

create temp table adopt as
  select agent, split_part(data->>'$.newtip', '@', 1) hash, min(t) t
  from trace, p where ns = 'ChainDB.AddBlockEvent.AddedToCurrentChain'
    and t >= p.t0 and t < p.t1 group by 1, 2;

create temp table rb as
  select b.hash, b.slot_no, b.has_leios_cert certifies, b.size, pr.eb_closure_size closure,
         case when exists (select 1 from win) then true else cast(substr(b.time, 12, 2) as int) % 2 = 0 end loaded
  from chainblk b left join chainblk pr on pr.block_no = b.block_no - 1, p
  where strptime(b.time, '%Y-%m-%dT%H:%M:%SZ')::timestamptz >= p.t0 and strptime(b.time, '%Y-%m-%dT%H:%M:%SZ')::timestamptz < p.t1
    and (not exists (select 1 from win) or exists (select 1 from win w where 1792281600 + b.slot_no >= w.s and 1792281600 + b.slot_no < w.e));

create temp table d as
  select r.*, a.agent, epoch(a.t) - (1792281600 + r.slot_no) delay from rb r join adopt a using (hash);

-- leader slots of the reporting hosts in the period: every NodeIsLeader should have its ForgedBlock
-- (a missed slot would show as a leader slot without a forged RB); the hosts outside the reporting
-- set are not observable here
select 'leadership of reporting hosts' what,
       count(*) filter (where ns = 'Forge.Loop.NodeIsLeader') leader_slots,
       count(*) filter (where ns = 'Forge.Loop.ForgedBlock') forged,
       count(*) filter (where ns = 'Forge.Loop.NodeIsLeader') - count(*) filter (where ns = 'Forge.Loop.ForgedBlock') leader_slots_not_forged,
       count(distinct agent) filter (where ns = 'Forge.Loop.NodeIsLeader') hosts
from trace, p where ns in ('Forge.Loop.NodeIsLeader', 'Forge.Loop.ForgedBlock') and t >= p.t0 and t < p.t1
  and (not exists (select 1 from win) or exists (select 1 from win w where epoch(t) >= w.s and epoch(t) < w.e));

select case when loaded then 'loaded' else 'trickle' end period,
  case when certifies = 1 and closure >= 1500000 then 'd certifies, closure 1.5-2 MB'
       when certifies = 1 and closure >= 1000000 then 'c certifies, closure 1-1.5 MB'
       when certifies = 1 and closure >= 500000 then 'b certifies, closure 0.5-1 MB'
       when certifies = 1 then 'a certifies, closure < 0.5 MB'
       when size >= 80000 then 'f plain RB, 80-88 kB' else 'e plain RB, < 80 kB' end kind,
  count(distinct hash) rbs, count(*) node_adoptions,
  round(quantile_cont(delay, 0.5), 2) delay_p50, round(quantile_cont(delay, 0.9), 2) delay_p90,
  round(100.0 * sum(delay <= 1) / count(*), 1) within_1s_pct, round(100.0 * sum(delay <= 2) / count(*), 1) within_2s_pct
from d where delay between -5 and 120 group by 1, 2 order by 1, 2;
