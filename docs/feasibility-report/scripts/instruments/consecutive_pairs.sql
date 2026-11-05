-- Consecutive-slot leader pairs and how many of them fork, for the Praos
-- section of the report: on the chain, two RBs one slot apart (no fork), split
-- by whether the first of the two certifies an EB; forked, an RB adopted by
-- two or more reporting nodes (ChainDB AddedToCurrentChain newtip) that is
-- not on the final chain and whose competitor on the chain at the same height
-- sits exactly one slot before or after it (the second leader had not adopted
-- the first RB within a second; either RB may lose the tiebreak), split by
-- whether the FIRST RB of the pair certifies: read from the chain when the
-- first RB won, and from the orphan's fetched size (BlockFetch
-- CompletedBlockFetch; a certifying RB on the testnet carries no transactions
-- and fetches at about 1 kB, a plain one under load at 88 kB) when it lost.
-- Same counting as cluster_forks.sql. Also the orphan count by slot distance,
-- as in fork_cases.sql. Forks seen by fewer than two nodes are left out (a
-- node on its own stale chain).
--
-- Variables: t0, t1 (UTC 'YYYY-MM-DD HH:MM:SS'), slot0 (default 1792281600),
-- chain (default chain-2026-10-18/blocks.sqlite under the working directory,
-- the data folder); win optional, a windows file restricting the pairs to the
-- loaded hours (by the slot of the pair's first RB).
--
--   duckdb -readonly -markdown archive/f2-high-merged.duckdb \
--     -c "set variable t0 = '2026-10-24 12:00:00'; set variable t1 = '2026-10-26 13:00:00'; set variable win = 'windows-f2-high.txt';" \
--     -f consecutive_pairs.sql
set timezone = 'UTC';
create temp table p as
  select getvariable('t0')::timestamptz t0, getvariable('t1')::timestamptz t1, coalesce(getvariable('slot0'), 1792281600)::bigint slot0;
create temp table win as
  select epoch(s::timestamp) s, epoch(e::timestamp) e
  from read_csv(coalesce(getvariable('win'), '/dev/null'), delim = ' ', header = false, columns = {'s': 'varchar', 'e': 'varchar'}, ignore_errors = true)
  where s not like '#%';
create temp table chainblk as
  select block_no, slot_no, hash, size, has_leios_cert
  from sqlite_scan(coalesce(getvariable('chain'), 'chain-2026-10-18/blocks.sqlite'), 'block') where slot_no is not null;
-- a slot is in scope when it is inside the period and, if a windows file is given, inside one of its windows
create temp table scope as
  select b.block_no, b.slot_no from chainblk b, p
  where p.slot0 + b.slot_no >= epoch(p.t0) and p.slot0 + b.slot_no < epoch(p.t1)
    and (not exists (select 1 from win) or exists (select 1 from win w where p.slot0 + b.slot_no >= w.s and p.slot0 + b.slot_no < w.e));
create temp table added as
  select agent, split_part(data->>'$.newtip', '@', 1) hash, try_cast(split_part(data->>'$.newtip', '@', 2) as bigint) slot,
         try_cast(data->'$.newSuffixSelectView'->>'$.blockNo' as bigint) block_no
  from trace, p where ns = 'ChainDB.AddBlockEvent.AddedToCurrentChain' and t >= p.t0 and t < p.t1 + interval 1 hour;
create temp table fetched as
  select data->>'$.block' fhash, min(try_cast(data->>'$.size' as bigint)) size
  from trace, p where ns = 'BlockFetch.Client.CompletedBlockFetch' and t >= p.t0 and t < p.t1 + interval 1 hour group by 1;
create temp table orphans as
  select s.hash, s.slot, s.block_no, c.slot_no comp_slot, s.slot - c.slot_no d_slots, c.has_leios_cert comp_certifies, s.agents,
         f.size orphan_size, case when f.size < 5000 then 1 else 0 end orphan_certifies
  from (select hash, any_value(slot) slot, any_value(block_no) block_no, count(distinct agent) agents from added group by 1) s
  join chainblk c on c.block_no = s.block_no left join fetched f on f.fhash = s.hash, p
  where s.hash not in (select hash from chainblk) and s.agents >= 2
    and p.slot0 + s.slot >= epoch(p.t0) and p.slot0 + s.slot < epoch(p.t1)
    and (not exists (select 1 from win) or exists (select 1 from win w where p.slot0 + s.slot >= w.s and p.slot0 + s.slot < w.e));
-- forked consecutive-slot pairs, with the kind of the pair's first RB
create temp table forked as
  select d_slots, case when d_slots = -1 then orphan_certifies else comp_certifies end first_certifies, orphan_size
  from orphans where abs(d_slots) = 1;
-- pairs on the chain: consecutive blocks one slot apart
create temp table chain_pairs as
  select a.slot_no first_slot, a.has_leios_cert first_certifies
  from chainblk a join chainblk b on b.block_no = a.block_no + 1
  where b.slot_no - a.slot_no = 1 and a.slot_no in (select slot_no from scope);
select 'consecutive-slot leader pairs' what,
       (select count(*) from chain_pairs) on_chain_no_fork,
       (select count(*) from chain_pairs where first_certifies = 1) on_chain_first_certifies,
       (select count(*) from chain_pairs where first_certifies = 0) on_chain_first_plain,
       (select count(*) from forked) forked,
       (select count(*) from forked where d_slots = -1) forked_first_rb_lost,
       (select count(*) from forked where d_slots = 1) forked_second_rb_lost,
       (select count(*) from forked where first_certifies = 1) forked_first_certifies,
       (select count(*) from forked where first_certifies = 0) forked_first_plain,
       (select count(*) from forked where orphan_size is null) orphan_size_unknown,
       round(100.0 * (select count(*) from forked) / ((select count(*) from chain_pairs) + (select count(*) from forked)), 1) fork_share_pct;
select case when d_slots < -1 then 'a orphan 2+ slots before the competitor' when d_slots = -1 then 'b orphan one slot before (consecutive-slot pair, first RB lost)'
            when d_slots = 0 then 'c same slot (slot battle)' when d_slots = 1 then 'd orphan one slot after (consecutive-slot pair, second RB lost)'
            when d_slots <= 5 then 'e orphan 2-5 slots after (competitor arrived late)' else 'f orphan 6+ slots after' end kind,
       count(*) forks, sum(orphan_certifies) orphan_certifies, sum(comp_certifies) competitor_certifies
from orphans group by 1 order by 1;
