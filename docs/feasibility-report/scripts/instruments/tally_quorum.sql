-- The "vote tally reaches the quorum" row of the stage table: per (reporting
-- node, eligible EB) over the loaded hours of a testnet period, the age after
-- the EB's slot at which the node's own tally for the announcing RB first
-- reached the quorum (Consensus.LeiosKernel.VoteAcquired, field tally; quorum
-- 0.75), then per node the p90 over the EBs where its tally got there, and
-- the spread of that p90 across nodes (nodes with 50+ such EBs). Second
-- result: eligible EBs, how many had a quorum at some reporting node, how
-- many certified, how many of those with a quorum seen.
--
-- Variables as in validation_pairs.sql: t0, t1 (period bounds, UTC), win (the
-- windows file; an EB counts by the time of its slot), gap (default 14),
-- slot0 (default 1792281600), chain (default chain-2026-10-18/blocks.sqlite
-- under the working directory, the data folder).
--
--   duckdb -readonly -markdown archive/f2-high-merged.duckdb \
--     -c "set variable t0 = '2026-10-24 12:00:00'; set variable t1 = '2026-10-26 13:00:00'; set variable win = 'windows-f2-high.txt';" \
--     -f tally_quorum.sql
set timezone = 'UTC';
create temp table p as
  select getvariable('t0')::timestamptz t0, getvariable('t1')::timestamptz t1,
         coalesce(getvariable('slot0'), 1792281600)::bigint slot0, coalesce(getvariable('gap'), 14)::int gap;
create temp table win as
  select epoch(s::timestamp) s, epoch(e::timestamp) e
  from read_csv(getvariable('win'), delim = ' ', header = false, columns = {'s': 'varchar', 'e': 'varchar'}, ignore_errors = true)
  where s not like '#%';
create temp table chainblk as
  select block_no, slot_no, hash, eb_announcement_hash, has_leios_cert
  from sqlite_scan(coalesce(getvariable('chain'), 'chain-2026-10-18/blocks.sqlite'), 'block');
create temp table ebs as
  select b.hash rb, b.slot_no slot, b.eb_announcement_hash eb, n.has_leios_cert certified
  from chainblk b join chainblk n on n.block_no = b.block_no + 1, p
  where b.eb_announcement_hash is not null and n.slot_no - b.slot_no >= p.gap
    and exists (select 1 from win w where p.slot0 + b.slot_no >= w.s and p.slot0 + b.slot_no < w.e);
-- extract first, then filter: a filter on data->>x straight on trace makes DuckDB cast other namespaces' payloads
create temp table v as
  select agent, data->>'$.vote.rbHash' rb, try_cast(data->>'$.tally' as double) tally, t
  from trace, p where ns = 'Consensus.LeiosKernel.VoteAcquired' and t >= p.t0 and t < p.t1 + interval 1 hour;
create temp table q as
  select v.agent, e.rb, min(epoch(v.t)) - ((select slot0 from p) + any_value(e.slot)) quorum_s
  from v join ebs e using (rb) where v.tally >= 0.75 group by 1, 2;
-- the per-node and per-EB views behind the two results, for the stage-table script (rename per window)
copy (select agent, count(*) ebs_with_quorum, quantile_cont(quorum_s, 0.9) p90 from q group by 1 order by 1)
  to 'tally_quorum_nodes.csv' (header, delimiter ',');
copy (select rb, eb, slot, certified, rb in (select rb from q) quorum_somewhere from ebs order by slot)
  to 'tally_quorum_ebs.csv' (header, delimiter ',');
select 'nodes reaching the quorum, per node p90 over EBs' what, count(*) nodes,
       round(median(p90), 2) p90_median_node, round(quantile_cont(p90, 0.25), 2) p90_q1, round(quantile_cont(p90, 0.75), 2) p90_q3,
       round(median(ebs_with_quorum), 0) ebs_median_node
from (select agent, count(*) ebs_with_quorum, quantile_cont(quorum_s, 0.9) p90 from q group by 1 having count(*) >= 50);
select 'eligible EBs' what, count(*) n, count(*) filter (where rb in (select rb from q)) quorum_somewhere,
       count(*) filter (where certified = 1) certified,
       count(*) filter (where certified = 1 and rb in (select rb from q)) certified_with_quorum
from ebs;
