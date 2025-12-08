
drop table if exists block_times;

create temporary table block_times (
  region     varchar(30)                 not null
, logged     timestamp without time zone not null
, block_hash char(64)                    not null
, slot_no    word63type                  not null
);

\copy block_times from 'block-times.tsv' csv header delimiter E'\t'


drop table if exists tx_times;

create temporary table tx_times (
  region     varchar(30)             not null
, logged timestamp without time zone not null
, tx_hash8 char(8)                   not null
);

\copy tx_times from 'tx-times.tsv' csv header delimiter E'\t'


drop table if exists slot_range;

create temporary table slot_range as
select
    min(slot_no) as min_slot_no
  , max(slot_no) as max_slot_no
  from block_times
;


drop table if exists mempool_vs_blocks;

create temporary table mempool_vs_blocks as
select
    block_times.region
  , xref.slot_no
  , xref.block_hash
  , xref.tx_hash
  , xref.tx_hash8
  , xref.time as slot_time
  , block_times.logged as block_logged
  , tx_times.logged as tx_logged
  , extract(epoch from (tx_times.logged - xref.time)) as mempool_minus_slot
  , extract(epoch from (block_times.logged - xref.time)) as block_minus_slot
  , case when coalesce(tx_times.logged < block_times.logged, false) then 'TRUE' else 'FALSE' end as tx_seen_first
  from slot_range
  inner join (
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
    on xref.slot_no between slot_range.min_slot_no and slot_range.max_slot_no
  left join block_times
    using (block_hash)
  left join tx_times
    using (region, tx_hash8)
order by 1, 2, 7
;

\copy mempool_vs_blocks to 'mempool-vs-blocks.tsv' csv header delimiter E'\t'


drop table if exists mempool_history;

create temporary table mempool_history as
select
    region
  , slot_no
  , tx_seen_first
  , count(*) as tx_count
  from mempool_vs_blocks
  where region is not null
  group by region, slot_no, tx_seen_first
order by 1, 2, 3
;

\copy mempool_history to 'mempool-history.tsv' csv header delimiter E'\t'


drop table if exists mempool_hourly;

create temporary table mempool_hourly as
select
    region
  , hour
  , tx_seen_first
  , tx_count
  , cast( tx_count as real) / tx_total as tx_fraction
  from (
    select
        region
      , date_trunc('hour', block_logged) as hour
      , tx_seen_first
      , count(*) as tx_count
      from mempool_vs_blocks
      where region is not null
      group by region, date_trunc('hour', block_logged), tx_seen_first
  ) a
  inner join (
    select
        region
      , date_trunc('hour', block_logged) as hour
      , count(*) as tx_total
      from mempool_vs_blocks
      where region is not null
      group by region, date_trunc('hour', block_logged)
  ) b
    using (region, hour)
order by 1, 2, 3
;

\copy mempool_hourly to 'mempool-hourly.tsv' csv header delimiter E'\t'


drop table if exists canary;

create temporary table canary as
select 
    tx_out.address
  , encode(tx.hash, 'hex') as tx_hash
  , cast(tx_metadata.json ->> 'absolute_slot' as word63type) as sub_slot_no
  , block.slot_no - cast(tx_metadata.json ->> 'absolute_slot' as word63type) as delay 
  from tx_out                                        
  inner join tx_in
    on tx_out.tx_id = tx_in.tx_out_id
  inner join tx
    on (tx.id, tx_in.tx_out_index) = (tx_in.tx_in_id, tx_out.index)
  inner join block
    on tx.block_id = block.id
  inner join slot_range
    on block.slot_no between slot_range.min_slot_no and slot_range.max_slot_no
  inner join tx_metadata
    on tx_metadata.tx_id = tx.id
    and tx_out.address in (
          'addr1vy0zwnn5yj4h3s25xuere4h38np4z6gcng2mdgxg0mapxagl6x66d'
        , 'addr1vxpvhtj5vvcqmf9td3vlvv4vza9nnuqrmkc42cnd42dg7fsz0v99d'
        , 'addr1vx7gvyvy2r7mycya22f3x88wlgra2552uxm8xz2g0v3g6yccgyydv'
        , 'addr1vx2uvrm53dak4x3u0txy98r2jpg2nhy0n82vk8a6v9wmk4s8up888'
        )
order by time
;

\copy canary to 'canary.tsv' csv header delimiter E'\t'


select
    region
  , tx_seen_first
  , count(*) as "count"
  , (count(*) + 0.0)
    /
    (select count(*) from mempool_vs_blocks z where z.region = mempool_vs_blocks.region and slot_no >= 172210527) as "fraction"
  from mempool_vs_blocks
  where region is not null and slot_no >= 172210527
  group by region, tx_seen_first
order by 1
;

