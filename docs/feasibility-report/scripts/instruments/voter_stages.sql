-- Per (voter, EB) stage record over the loaded hours of a testnet period, for
-- voter_stages.py: every vote the node scheduled, with the closure's arrival,
-- the validation and the vote's outcome, so that each EB can be read as
-- shares of the voters that should have validated it rather than of the
-- validations that happened. A voter that refused the EB because its own
-- chain tip did not announce it (NotVoted chainTipDoesNotAnnounce) or that
-- found itself off the committee (notOnCommittee) is not a voter of that EB
-- and is left out.
--
-- Columns: agent, pool, eb, eb_slot, txs (the EB's transaction count as the
-- body hits report it), closure_s (seconds after the slot the closure was
-- complete, empty if never), validated_s (empty if never), duration_s
-- (validated - max(closure, slot + 3 s), as validation_pairs.sql), applied,
-- reapplied, outcome ('voted', 'tooLate', or the NotVoted reason).
--
-- Variables as validation_pairs.sql: t0, t1 the period's bounds (UTC), win a
-- windows file of `start end` pairs (the loaded hours; an EB counts by the
-- time of its slot; one line spanning the run for a cluster run), slot0
-- (default 1792281600, the 2026-10-18 chain; a cluster run's is its logged
-- system start), and sched_ns, the event that makes a node a voter of an EB:
-- 'Consensus.LeiosKernel.VoteScheduled' (default, the testnet builds) or
-- 'Consensus.LeiosKernel.AnnouncementAccepted' for the cluster's w42 build,
-- which has no vote-scheduled event and where every node is a committee
-- member. The EB's transaction count is the body hits' txsInEb where that
-- event exists, else the EB's body size over 36 B per reference. The CSV is
-- voter_stages_pairs.csv in the current directory.
--
--   duckdb -readonly archive/f2-high-merged.duckdb \
--     -c "set variable t0 = '2026-10-24 12:00:00'; set variable t1 = '2026-10-26 13:00:00'; set variable win = 'windows-f2-high.txt';" \
--     -f voter_stages.sql
set timezone = 'UTC';
create temp table p as
  select getvariable('t0')::timestamptz t0, getvariable('t1')::timestamptz t1,
         coalesce(getvariable('slot0'), 1792281600)::bigint slot0,
         coalesce(getvariable('sched_ns'), 'Consensus.LeiosKernel.VoteScheduled') sched_ns;
create temp table win as
  select epoch(s::timestamp) s, epoch(e::timestamp) e
  from read_csv(getvariable('win'), delim = ' ', header = false, columns = {'s': 'varchar', 'e': 'varchar'}, ignore_errors = true)
  where s not like '#%';
-- extract first, then filter: a filter on data->>x straight on trace makes DuckDB cast other namespaces' payloads
create temp table sch as
  select agent, pool, data->>'$.ebHash' eb,
         coalesce(try_cast(data->>'$.ebSlot' as bigint), try_cast(data->>'$.electionSlot' as bigint)) eb_slot,
         min(t) scheduled_t, max(try_cast(data->>'$.ebBodySize' as bigint)) body_size
  from trace, p where ns = p.sched_ns and t >= p.t0 and t < p.t1
  group by 1, 2, 3, 4;
create temp table hits as
  select agent, data->>'$.ebHash' eb, max(try_cast(data->>'$.txsInEb' as bigint)) txs
  from trace, p where ns = 'Consensus.LeiosKernel.BodyHits' and t >= p.t0 and t < p.t1
  group by 1, 2;
create temp table cl as
  select agent, data->>'$.ebHash' eb, min(t) closure_t
  from trace, p where ns = 'Consensus.LeiosKernel.BlockTxsAcquired' and t >= p.t0 and t < p.t1
  group by 1, 2;
create temp table ev as
  select agent, data->>'$.ebHash' eb, min(t) validated_t,
         max(try_cast(data->>'$.applied' as bigint)) applied, max(try_cast(data->>'$.reapplied' as bigint)) reapplied
  from trace, p where ns = 'Consensus.LeiosKernel.EbValidated' and t >= p.t0 and t < p.t1
  group by 1, 2;
create temp table nv as
  select agent, data->>'$.ebHash' eb, min(data->>'$.reason') reason
  from trace, p where ns = 'Consensus.LeiosKernel.NotVoted' and t >= p.t0 and t < p.t1
  group by 1, 2;
create temp table rec as
  select sch.agent, sch.pool, sch.eb, sch.eb_slot,
         coalesce(hits.txs, sch.body_size // 36, ev.applied + ev.reapplied) txs,
         epoch(cl.closure_t) - (p.slot0 + sch.eb_slot) closure_s,
         epoch(ev.validated_t) - (p.slot0 + sch.eb_slot) validated_s,
         epoch(ev.validated_t) - greatest(epoch(cl.closure_t), p.slot0 + sch.eb_slot + 3) duration_s,
         ev.applied, ev.reapplied,
         coalesce(nv.reason, 'voted') outcome
  from sch
  left join hits on hits.agent = sch.agent and hits.eb = sch.eb
  left join cl on cl.agent = sch.agent and cl.eb = sch.eb
  left join ev on ev.agent = sch.agent and ev.eb = sch.eb
  left join nv on nv.agent = sch.agent and nv.eb = sch.eb, p
  where coalesce(nv.reason, '') not in ('chainTipDoesNotAnnounce', 'notOnCommittee')
    and exists (select 1 from win w where p.slot0 + sch.eb_slot >= w.s and p.slot0 + sch.eb_slot < w.e);
copy rec to 'voter_stages_pairs.csv' (header, delimiter ',');
select count(*) voter_ebs, count(distinct agent) voters, count(distinct eb) ebs,
       sum(case when outcome = 'voted' then 1 else 0 end) voted, sum(case when outcome = 'tooLate' then 1 else 0 end) too_late
from rec;
