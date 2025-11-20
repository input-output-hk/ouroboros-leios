
drop table if exists block_times;

create temporary table block_times (
  logged     timestamp without time zone not null
, block_hash char(64)                    not null
, slot_no    word63type                  not null
);

\copy block_times from 'block_times.tsv' csv header delimiter E'\t'


drop table if exists tx_times;

create temporary table tx_times (
  logged timestamp without time zone not null
, tx_hash8 char(8)                   not null
);

\copy tx_times from 'tx_times.tsv' csv header delimiter E'\t'


drop table if exists mempool_vs_blocks;

create temporary table mempool_vs_blocks as
select
    xref.slot_no
  , xref.block_hash
  , xref.tx_hash
  , xref.tx_hash8
  , xref.time as slot_time
  , block_times.logged as block_logged
  , tx_times.logged as tx_logged
  , extract(epoch from (tx_times.logged - xref.time)) as mempool_minus_slot
  , extract(epoch from (block_times.logged - xref.time)) as block_minus_slot
  , coalesce(tx_times.logged < block_times.logged, false) as tx_seen_first
  from (
    select
        slot_no
      , time
      , encode(block.hash, 'hex') as block_hash
      , encode(tx.hash, 'hex') as tx_hash
      , left(encode(tx.hash, 'hex'), 8) as tx_hash8
      from block
      inner join tx
        on tx.block_id = block.id
      where block.slot_no >= (select min(slot_no) from block_times)
  ) xref
  inner join block_times
    using (block_hash)
  left join tx_times
    using (tx_hash8)
order by 1, 6
;

\copy mempool_vs_blocks to 'mempool_vs_blocks.tsv' csv header delimiter E'\t'


drop table if exists mempool_history;

create temporary table mempool_history as
select
    slot_no
  , tx_seen_first
  , count(*) as tx_count
  from mempool_vs_blocks
  group by slot_no, tx_seen_first
order by 1, 2
;

\copy mempool_history to 'mempool_history.tsv' csv header delimiter E'\t'


drop table if exists mempool_hourly;

create temporary table mempool_hourly as
select
    hour
  , tx_seen_first
  , tx_count
  , cast( tx_count as real) / tx_total
  from (
    select
        date_trunc('hour', block_logged) as hour
      , tx_seen_first
      , count(*) as tx_count
      from mempool_vs_blocks
      group by date_trunc('hour', block_logged), tx_seen_first
  ) a
  inner join (
    select
        date_trunc('hour', block_logged) as hour
      , count(*) as tx_total
      from mempool_vs_blocks
      group by date_trunc('hour', block_logged)
  ) b
    using (hour)
order by 1, 2
;

\copy mempool_hourly to 'mempool_hourly.tsv' csv header delimiter E'\t'


select
    tx_seen_first
  , count(*) as "count"
  , (count(*) + 0.0) / (select count(*) from mempool_vs_blocks where block_logged >= now() - interval '2 hours') as "fraction"
  from mempool_vs_blocks
  where block_logged >= now() - interval '2 hours'
  group by tx_seen_first
;

