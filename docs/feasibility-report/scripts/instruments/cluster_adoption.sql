-- Adoption delay of the final chain's RBs across the cluster's nodes: for
-- each (node, RB) the time from the RB's slot to the node's
-- AddedToCurrentChain or SwitchedToAFork of it (raw/ChainDB.db), by RB kind:
-- certifying, binned by the closure it certifies (the parent's EB closure),
-- or plain, full (80 kB and up) or small. Then the fork-switch reasons and
-- the leadership counts (NodeIsLeader / ForgedBlock / AdoptedBlock /
-- DidntAdoptBlock) and the LeiosCertRbWithoutCandidate events. Slot 0
-- derived from the chain cache.
--
--   cd cluster/<run> && duckdb -markdown -f <repo>/scripts/instruments/cluster_adoption.sql
attach 'raw/ChainDB.db' as cd (type sqlite, read_only);
attach 'raw/Forge.db' as f (type sqlite, read_only);
attach 'blocks.sqlite' as ch (type sqlite, read_only);

create temp table params as
  select min(epoch(strptime(time, '%Y-%m-%dT%H:%M:%SZ')) - slot_no) slot0 from ch.block where slot_no is not null;

create temp table a as
  select node, hash, min(t) t from (
    select file node, split_part("data.newtip", '@', 1) hash, at_ns / 1e9 t from cd."ChainDB.AddBlockEvent.AddedToCurrentChain"
    union all
    select file, split_part("data.newtip", '@', 1), at_ns / 1e9 from cd."ChainDB.AddBlockEvent.SwitchedToAFork") group by 1, 2;

create temp table rb as
  select b.hash, b.slot_no, b.has_leios_cert certifies, b.size, p.eb_closure_size closure
  from ch.block b left join ch.block p on p.block_no = b.block_no - 1 where b.slot_no is not null;

with d as (select r.*, a.node, a.t - ((select slot0 from params) + r.slot_no) delay from rb r join a using (hash))
select 'adoption delay by RB kind' what,
       case when certifies = 1 and closure >= 1000000 then 'c3 certifies, closure 1 MB and up'
            when certifies = 1 and closure >= 500000 then 'c2 certifies, closure 500 kB to 1 MB'
            when certifies = 1 and closure >= 300000 then 'c1 certifies, closure 300-500 kB'
            when certifies = 1 then 'c0 certifies, closure under 300 kB'
            when size >= 80000 then 'p1 plain RB, full (80 kB and up)' else 'p0 plain RB, small' end kind,
       count(distinct hash) rbs, count(*) adoptions, round(quantile_cont(delay, 0.5), 2) delay_p50, round(quantile_cont(delay, 0.9), 2) delay_p90,
       round(100.0 * sum(case when delay <= 1 then 1 else 0 end) / count(*), 1) within_1s_pct,
       round(100.0 * sum(case when delay <= 1.5 then 1 else 0 end) / count(*), 1) within_1_5s_pct,
       round(100.0 * sum(case when delay <= 2 then 1 else 0 end) / count(*), 1) within_2s_pct
from d where delay between -5 and 120 group by 1, 2 order by 2;

select 'switch reasons' what, "data.reason.reason" reason, count(*) n
from cd."ChainDB.AddBlockEvent.SwitchedToAFork" group by 1, 2 order by 3 desc limit 6;

select 'leadership' what,
       (select count(*) from f."Forge.Loop.NodeIsLeader") leader_slots,
       (select count(*) from f."Forge.Loop.ForgedBlock") forged,
       (select count(*) from f."Forge.Loop.AdoptedBlock") adopted,
       (select count(*) from f."Forge.Loop.DidntAdoptBlock") didnt_adopt,
       (select count(*) from (select l.file, l."data.slot" from f."Forge.Loop.NodeIsLeader" l
                              left join f."Forge.Loop.ForgedBlock" b on b.file = l.file and b."data.slot" = l."data.slot" where b.file is null)) leader_slots_not_forged;

select 'LeiosCertRbWithoutCandidate' what, count(*) events, count(distinct file) nodes, count(distinct "data.blockHash") rbs,
       min("data.blockSlot" - "data.predecessorSlot") gap_min, round(avg("data.blockSlot" - "data.predecessorSlot"), 1) gap_avg
from cd."ChainDB.AddBlockEvent.AddBlockLeiosEvent.LeiosCertRbWithoutCandidate";
