-- The adoption path on a cluster run, measured as on the testnet: for each
-- (node, RB on the final chain) the interval from the node's
-- PoppedBlockFromQueue to its AddedToCurrentChain / SwitchedToAFork of the
-- same RB (raw/ChainDB.db). On the testnet F2 pulls that interval equals
-- the `chain-sel-add-block` call duration RB by RB (ratio 1.00 at the
-- median, 1.07 at p90, IOG1 and PIR7), so the two populations are read with
-- one instrument. By RB kind: certifying, binned by the closure it
-- certifies (the parent's EB closure; its tx_count in the cache is the
-- closure's), or plain, full (80 kB and up) or small. Per closure
-- transaction: the median interval over the median count, and the marginal
-- cost between closure bins (interval difference over count difference),
-- which leaves the per-closure fixed part out.
--
--   cd cluster/<run> && duckdb -markdown -f <repo>/scripts/instruments/cluster_adoption_path.sql >adoption_path.out.md
attach 'raw/ChainDB.db' as cd (type sqlite, read_only);
attach 'blocks.sqlite' as ch (type sqlite, read_only);

create temp table pop as
  select file node, "data.block.hash" hash, min(at_ns) / 1e9 t
  from cd."ChainDB.AddBlockEvent.PoppedBlockFromQueue" group by 1, 2;

create temp table a as
  select node, hash, min(t) t from (
    select file node, split_part("data.newtip", '@', 1) hash, at_ns / 1e9 t from cd."ChainDB.AddBlockEvent.AddedToCurrentChain"
    union all
    select file, split_part("data.newtip", '@', 1), at_ns / 1e9 from cd."ChainDB.AddBlockEvent.SwitchedToAFork") group by 1, 2;

create temp table rb as
  select b.hash, b.has_leios_cert certifies, b.size, b.tx_count, p.eb_closure_size closure
  from ch.block b left join ch.block p on p.block_no = b.block_no - 1 where b.slot_no is not null;

create temp table d as
  select r.*, pop.node, a.t - pop.t dur,
         case when certifies = 1 and closure >= 900000 then 'c3 certifying, closure 0.9-1 MB'
              when certifies = 1 and closure >= 500000 then 'c2 certifying, closure 0.5-0.9 MB'
              when certifies = 1 and closure >= 200000 then 'c1 certifying, closure 0.2-0.5 MB'
              when certifies = 1 then 'c0 certifying, closure under 0.2 MB'
              when size >= 80000 then 'p1 plain, full (80 kB+)' else 'p0 plain, small' end kind
  from rb r join a using (hash) join pop using (node, hash) where a.t >= pop.t;

select 'pop to adopted by RB kind' what, kind, count(*) node_rbs, count(distinct node) nodes,
       round(median(closure)) closure_B_p50, round(median(tx_count)) txs_p50,
       round(quantile_cont(dur, 0.5), 3) dur_p50_s, round(quantile_cont(dur, 0.9), 3) dur_p90_s,
       round(1e6 * quantile_cont(dur, 0.5) / nullif(median(tx_count), 0)) us_per_tx
from d group by 1, 2 order by 2;

-- marginal cost per closure transaction between the two most populated certifying bins
with b as (
  select kind, median(tx_count) txs, quantile_cont(dur, 0.5) dur, count(*) n from d where certifies = 1 group by 1
  order by n desc limit 2)
select 'marginal us per closure tx (top two certifying bins)' what,
       max(kind) bin_a, min(kind) bin_b,
       round(1e6 * (max(dur) - min(dur)) / nullif(max(txs) - min(txs), 0)) us_per_tx,
       round(max(dur) - 1e-6 * round(1e6 * (max(dur) - min(dur)) / nullif(max(txs) - min(txs), 0)) * max(txs), 3) fixed_s
from b;

-- the testnet's convention: certifying RB minus a full plain RB, over the closure's transactions
with c as (select quantile_cont(dur, 0.5) dur, median(tx_count) txs from d where certifies = 1),
     p as (select quantile_cont(dur, 0.5) dur from d where kind = 'p1 plain, full (80 kB+)')
select 'certifying minus plain full, per closure tx' what,
       round(c.dur, 3) certifying_p50_s, round(p.dur, 3) plain_full_p50_s, round(c.txs) closure_txs,
       round(1e6 * (c.dur - p.dur) / c.txs) us_per_tx
from c, p;

-- per node, certifying RBs: median interval and per-transaction cost
select 'per node, certifying RBs' what, node, count(*) rbs, round(quantile_cont(dur, 0.5), 3) dur_p50_s,
       round(1e6 * quantile_cont(dur, 0.5) / nullif(median(tx_count), 0)) us_per_tx
from d where certifies = 1 group by 1, 2 order by 5, 2;
