-- The "vote tally reaches the quorum" row of the stage table on a cluster
-- run: per (node, eligible EB) the age after the EB's slot at which the
-- node's own tally for the announcing RB first reached the quorum
-- (raw/Consensus.db, Consensus.LeiosKernel.VoteAcquired, data.tally; quorum
-- 0.75 of the stake, 39 of 51 equal votes), then per node the p90 over the
-- EBs where its tally got there and the spread of that p90 across nodes.
-- Second result: eligible EBs, how many had a quorum at some node, how many
-- certified. Slot 0 derived from the chain cache; the certification gap is
-- the variable gap (15 on the 40 kB / 260 kB run, 14 on the w42 runs).
--
--   cd cluster/<run> && duckdb -markdown -c "set variable gap = 14;" -f <repo>/scripts/instruments/cluster_tally_quorum.sql
attach 'raw/Consensus.db' as cs (type sqlite, read_only);
attach 'blocks.sqlite' as ch (type sqlite, read_only);

create temp table params as
  select min(epoch(strptime(time, '%Y-%m-%dT%H:%M:%SZ')) - slot_no) slot0 from ch.block where slot_no is not null;

create temp table ebs as
  select b.hash rb, b.slot_no slot, n.has_leios_cert certified
  from ch.block b join ch.block n on n.block_no = b.block_no + 1
  where b.eb_announcement_hash is not null and n.slot_no - b.slot_no >= coalesce(getvariable('gap'), 14)::int;

create temp table q as
  select v.file node, e.rb, min(v.at_ns) / 1e9 - ((select slot0 from params) + any_value(e.slot)) quorum_s
  from cs."Consensus.LeiosKernel.VoteAcquired" v join ebs e on e.rb = v."data.vote.rbHash"
  where v."data.tally" >= 0.75 group by 1, 2;

-- the per-node and per-EB views behind the two results, for the stage-table script (written in the run folder)
copy (select node agent, count(*) ebs_with_quorum, quantile_cont(quorum_s, 0.9) p90 from q group by 1 order by 1)
  to 'tally_quorum_nodes.csv' (header, delimiter ',');
copy (select rb, slot, certified, rb in (select rb from q) quorum_somewhere from ebs order by slot)
  to 'tally_quorum_ebs.csv' (header, delimiter ',');

select 'nodes reaching the quorum, per node p90 over EBs' what, count(*) nodes,
       round(median(p90), 2) p90_median_node, round(quantile_cont(p90, 0.25), 2) p90_q1, round(quantile_cont(p90, 0.75), 2) p90_q3,
       round(median(ebs_with_quorum), 0) ebs_median_node
from (select node, count(*) ebs_with_quorum, quantile_cont(quorum_s, 0.9) p90 from q group by 1 having count(*) >= 50);

select 'eligible EBs' what, count(*) n, count(*) filter (where rb in (select rb from q)) quorum_somewhere,
       count(*) filter (where certified = 1) certified,
       count(*) filter (where certified = 1 and rb in (select rb from q)) certified_with_quorum
from ebs;
