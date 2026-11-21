-- Forks of a cluster run: every forged RB (Forge.Loop.ForgedBlock) that is
-- not on the final chain, against its competitor at the same height, by
-- slot distance (orphan earlier / same slot / orphan later) and by whether
-- the competitor certifies an EB; the orphan carrying a certificate is read
-- from its size (a certifying RB on these runs is under 5 kB, a plain one
-- 80-88 kB; an orphan without an AdoptedBlock trace has no size and is
-- counted as plain, coalesce(size, 99999)); then the consecutive-slot
-- leader pairs: those that stayed on
-- the chain (the leader of slot s+1 extended the RB of slot s) against
-- those that forked (it did not; the pair is "orphan earlier, d = 1" when
-- the RB of slot s lost the tiebreak and "orphan later, d = 1" when the RB
-- of slot s+1 lost), both split by whether the first RB of the pair, the
-- one of slot s, certifies an EB. Run it in each run folder to compare.
--
--   cd cluster/<run> && duckdb -markdown -f <repo>/scripts/instruments/cluster_forks.sql
attach 'raw/Forge.db' as f (type sqlite, read_only);
attach 'blocks.sqlite' as ch (type sqlite, read_only);

create temp table forged as
  select "data.block" hash, try_cast("data.blockNo" as bigint) block_no, try_cast("data.slot" as bigint) slot, "data.blockPrev" prev, file node
  from f."Forge.Loop.ForgedBlock";
create temp table adopted as
  select "data.blockHash" hash, try_cast("data.blockSize" as bigint) size from f."Forge.Loop.AdoptedBlock";
create temp table orphans as
  select o.*, a.size, c.slot_no comp_slot, c.has_leios_cert comp_certifies, c.size comp_size,
         p.eb_closure_size parent_closure, p.slot_no parent_slot
  from forged o left join adopted a using (hash)
  join ch.block c on c.block_no = o.block_no and c.slot_no is not null
  left join ch.block p on p.block_no = o.block_no - 1
  where o.hash not in (select hash from ch.block where slot_no is not null);

select 'orphans total' what, count(*) forged_rbs_off_chain, count(distinct block_no) heights,
       (select count(*) from ch.block where slot_no is not null) rbs_on_chain
from orphans;

select 'forks by slot distance' what,
       case when slot < comp_slot then 'a orphan earlier' when slot = comp_slot then 'b same slot' else 'c orphan later' end kind,
       abs(slot - comp_slot) d, count(*) forks, sum(case when size < 5000 then 1 else 0 end) orphan_carries_cert,
       sum(case when comp_certifies = 1 then 1 else 0 end) comp_certifies,
       round(avg(size)) orphan_size_avg, round(avg(comp_size)) comp_size_avg, round(avg(parent_closure) / 1000) parent_closure_kb
from orphans group by 1, 2, 3 order by 2, 3;

with b as (select block_no, slot_no, has_leios_cert, slot_no - lag(slot_no) over (order by block_no) gap,
                  lag(has_leios_cert) over (order by block_no) prev_cert
           from ch.block where slot_no is not null)
select 'consecutive-slot leader pairs' what,
       sum(case when gap = 1 then 1 else 0 end) on_chain_no_fork,
       sum(case when gap = 1 and prev_cert = 1 then 1 else 0 end) on_chain_first_certifies,
       sum(case when gap = 1 and prev_cert = 0 then 1 else 0 end) on_chain_first_plain,
       (select count(*) from orphans where abs(comp_slot - slot) = 1) forked,
       (select count(*) from orphans where comp_slot - slot = 1) forked_first_rb_lost,
       (select count(*) from orphans where slot - comp_slot = 1) forked_second_rb_lost,
       (select count(*) from orphans where comp_slot - slot = 1 and coalesce(size, 99999) < 5000) + (select count(*) from orphans where slot - comp_slot = 1 and comp_certifies = 1) forked_first_certifies,
       (select count(*) from orphans where comp_slot - slot = 1 and coalesce(size, 99999) >= 5000) + (select count(*) from orphans where slot - comp_slot = 1 and comp_certifies = 0) forked_first_plain
from b;
