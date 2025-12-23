
drop table if exists blk_redeemers;

create temporary table blk_redeemers as
select
    block_no
  , coalesce(unit_mem, 0) as unit_mem
  , coalesce(unit_steps, 0) as unit_steps
  from block
  left join (
    select
        block_id
      , sum(unit_mem) as unit_mem
      , sum(unit_steps) as unit_steps
    from tx
    inner join redeemer
      on redeemer.tx_id = tx.id
    group by block_id
  ) tx
    on tx.block_id = block.id
;

create index idx_blk_redeemers
  on blk_redeemers (block_no)
;


drop table if exists block_utilization;

create table block_utilization as
select
    encode(hash, 'hex') as block_hash
  , block_no
  , epoch_no
  , slot_no
  , time
  , tx_count
  , size as block_size
  , max_block_size as max_size
  , unit_mem as block_mem
  , max_block_ex_mem as max_mem
  , unit_steps as block_steps
  , max_block_ex_steps as max_steps
  from block
  inner join blk_redeemers
    using (block_no)
  inner join epoch_param
    using (epoch_no)
order by block_no
;

\copy block_utilization to 'block-utilization.tsv' csv header delimiter E'\t'
