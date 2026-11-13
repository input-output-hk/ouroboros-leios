-- Per (node, eligible EB) validation record of a cluster run, for
-- fit_validation.py (cost per applied / reapplied transaction) and
-- cluster_counterfactual.py (vote-deadline levers): applied and reapplied
-- counts (EbValidated), closure arrival (BlockTxsAcquired), validated time
-- after the EB slot, duration = validated - max(closure, 3 s) as in the
-- testnet fits (validation_pairs.sql). Slot 0 derived from the chain cache.
-- Writes validation_pairs.csv in the run folder.
--
--   cd cluster/<run> && duckdb -readonly cluster.duckdb -f <repo>/scripts/instruments/cluster_validation_pairs.sql
-- (the regression and the counterfactual over validation_pairs.csv, fit_validation.py and
-- cluster_counterfactual.py, are analysis-folder tools and not part of the report's tables)
set timezone = 'UTC';
attach 'blocks.sqlite' as ch (type sqlite, read_only);

create temp table params as
  select min(epoch(strptime(time, '%Y-%m-%dT%H:%M:%SZ')) - slot_no) slot0 from ch.block where slot_no is not null;

create temp table ebs as
  select b.hash rb, b.eb_announcement_hash eb, b.slot_no slot, n.has_leios_cert = 1 certified, n.slot_no - b.slot_no gap
  from ch.block b join ch.block n on n.block_no = b.block_no + 1 where b.eb_announcement_hash is not null;

create temp table c as
  select agent, eb, min(closure_s) closure_s from (
    select agent, data->>'$.ebHash' eb, try_cast(data->>'$.closureAgeSeconds' as double) closure_s
    from trace where ns = 'Consensus.LeiosKernel.BlockTxsAcquired') group by 1, 2;

create temp table val as
  select agent, eb, min(t_s) - ((select slot0 from params) + any_value(slot)) validated_s,
         any_value(applied) applied, any_value(reapplied) reapplied
  from (select agent, data->>'$.ebHash' eb, epoch(t) t_s, try_cast(data->>'$.ebSlot' as bigint) slot,
               try_cast(data->>'$.applied' as bigint) applied, try_cast(data->>'$.reapplied' as bigint) reapplied
        from trace where ns = 'Consensus.LeiosKernel.EbValidated') group by 1, 2;

copy (
  select c.agent, c.agent pool, e.eb, e.slot eb_slot, val.applied, val.reapplied, val.validated_s, c.closure_s,
         val.validated_s - greatest(c.closure_s, 3) duration_s
  from ebs e join c on c.eb = e.eb join val on val.eb = e.eb and val.agent = c.agent
  where e.gap >= 14
) to 'validation_pairs.csv' (header);
-- the per-node summary the stage table reads (as validation_pairs.sql)
copy (select agent, count(*) records, quantile_cont(duration_s, 0.9) p90, sum(applied) applied, sum(reapplied) reapplied
      from read_csv_auto('validation_pairs.csv') group by 1 order by 1) to 'validation_nodes.csv' (header, delimiter ',');

select 'validation records written' what, count(*) n from read_csv_auto('validation_pairs.csv');
