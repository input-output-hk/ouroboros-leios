
drop table if exists blk_ins;

create temporary table blk_ins as
select tx_id, coalesce(tx_ins, 0) as tx_ins
  from block
  left join (
    select block_id, tx.id as tx_id, count(*) as tx_ins
      from tx
      inner join tx_in
        on tx_in.tx_in_id = tx.id 
      group by tx.id
  ) tx
    on tx.block_id = block.id
  where block.epoch_no >= 350
;

create index idx_blk_ins
  on blk_ins (tx_id)
;


drop table if exists blk_outs;

create temporary table blk_outs as
select tx_id, coalesce(tx_outs, 0) as tx_outs
  from block
  left join (
    select block_id, tx.id as tx_id, count(*) as tx_outs
      from tx
      inner join tx_out
        on tx_out.id = tx.id
      group by tx.id
  ) tx
    on tx.block_id = block.id
  where block.epoch_no >= 350
;

create index idx_blk_outs
  on blk_outs (tx_id)
;


drop table if exists blk_redeemers;

create temporary table blk_redeemers as
select tx_id, coalesce(unit_mem, 0) as unit_mem, coalesce(unit_steps, 0) as unit_steps
  from block
  left join (
    select block_id, tx.id as tx_id, sum(unit_mem) as unit_mem, sum(unit_steps) as unit_steps
    from tx
    inner join redeemer
      on redeemer.tx_id = tx.id
    group by tx.id
  ) tx
    on tx.block_id = block.id
  where block.epoch_no >= 350
;

create index idx_blk_redeemers
  on blk_redeemers (tx_id)
;


drop table if exists blk_txs;

create temporary table blk_txs as
select
    slot_no
  , block_no
  , epoch_no
  , encode(tx.hash, 'hex') as tx_hash
  , tx_ins
  , tx_outs
  , tx.size as tx_size
  , coalesce(unit_mem, 0) as unit_mem
  , coalesce(unit_steps, 0) as unit_steps
  from block
  inner join tx
    on block.id = tx.block_id
  inner join blk_ins
    on tx.id = blk_ins.tx_id
  inner join blk_outs
    on tx.id = blk_outs.tx_id
  left join blk_redeemers
    on tx.id = blk_redeemers.tx_id
;

\copy blk_txs to 'txs.csv' header csv

