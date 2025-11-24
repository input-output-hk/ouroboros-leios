
drop table if exists ledger_ops_apply;

create temporary table ledger_ops_apply (
  slot            int    not null
, slotGap         int    not null
, totalTime       int    not null
, mut             int    not null
, gc              int    not null
, majGcCount      int    not null
, minGcCount      int    not null
, allocatedBytes  bigint not null
, mut_forecast    int    not null
, mut_headerTick  int    not null
, mut_headerApply int    not null
, mut_blockTick   int    not null
, mut_blockApply  int    not null
, blockBytes      int    not null
, txs             int    not null
, txs_size        int    not null
, txs_steps       bigint not null
);

\copy ledger_ops_apply from 'ledger-ops-apply-65836843.csv' header


drop table if exists ledger_ops_reapply;

create temporary table ledger_ops_reapply (
  slot            int    not null
, slotGap         int    not null
, totalTime       int    not null
, mut             int    not null
, gc              int    not null
, majGcCount      int    not null
, minGcCount      int    not null
, allocatedBytes  bigint not null
, mut_forecast    int    not null
, mut_headerTick  int    not null
, mut_headerApply int    not null
, mut_blockTick   int    not null
, mut_blockApply  int    not null
, blockBytes      int    not null
, txs             int    not null
, txs_size        int    not null
, txs_steps       bigint not null
);

\copy ledger_ops_reapply from 'ledger-ops-reapply-65836843.csv' header


drop table if exists blk_ins;

create temporary table blk_ins as
select block_no, coalesce(tx_ins, 0) as tx_ins
  from block
  left join (
    select block_id, count(*) as tx_ins
      from tx
      inner join tx_in
        on tx_in.tx_in_id = tx.id 
      group by block_id
  ) tx
    on tx.block_id = block.id
;

create index idx_blk_ins
  on blk_ins (block_no)
;


drop table if exists blk_outs;

create temporary table blk_outs as
select block_no, coalesce(tx_outs, 0) as tx_outs
  from block
  left join (
    select block_id, count(*) as tx_outs
      from tx
      inner join tx_out
        on tx_out.id = tx.id
      group by block_id
  ) tx
    on tx.block_id = block.id
;

create index idx_blk_outs
  on blk_outs (block_no)
;


drop table if exists blk_redeemers;

create temporary table blk_redeemers as
select block_no, coalesce(unit_mem, 0) as unit_mem, coalesce(unit_steps, 0) as unit_steps
  from block
  left join (
    select block_id, sum(unit_mem) as unit_mem, sum(unit_steps) as unit_steps
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


drop table if exists ledger_ops;

create temporary table ledger_ops as
select
    slot_no
  , block_no
  , epoch_no
  , epoch_slot_no
  , encode(block.hash, 'hex') as block_hash
  , ledger_ops_apply.mut as apply_mut
  , ledger_ops_apply.mut_forecast as apply_mut_forecast
  , ledger_ops_apply.mut_headerTick as apply_mut_headerTick
  , ledger_ops_apply.mut_headerApply as apply_mut_headerApply
  , ledger_ops_apply.mut_blockTick as apply_mut_blockTick
  , ledger_ops_apply.mut_blockApply as apply_mut_blockApply
  , ledger_ops_reapply.mut as reapply_mut
  , ledger_ops_reapply.mut_forecast as reapply_mut_forecast
  , ledger_ops_reapply.mut_headerTick as reapply_mut_headerTick
  , ledger_ops_reapply.mut_headerApply as reapply_mut_headerApply
  , ledger_ops_reapply.mut_blockTick as reapply_mut_blockTick
  , ledger_ops_reapply.mut_blockApply as reapply_mut_blockApply
  , ledger_ops_apply.txs as txs
  , ledger_ops_apply.txs_size as txs_size
  , tx_ins
  , tx_outs
  , unit_mem
  , unit_steps
  from block
  inner join ledger_ops_apply
    on ledger_ops_apply.slot = block.slot_no
  inner join ledger_ops_reapply
    on ledger_ops_reapply.slot = block.slot_no
  inner join blk_ins
    using (block_no)
  inner join blk_outs
    using (block_no)
  inner join blk_redeemers
    using (block_no)
;

\copy ledger_ops to 'ledger-ops-65836843.csv' header csv

