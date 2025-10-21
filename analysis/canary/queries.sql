
drop table if exists canary;

create temporary table canary as
select 
    block.time
  , tx_metadata.json
  , block.slot_no
  , cast(tx_metadata.json ->> 'absolute_slot' as word63type) as sub_slot_no
  , block.slot_no - cast(tx_metadata.json ->> 'absolute_slot' as word63type) as delay 
  from tx_out                                        
  inner join tx_in
    on tx_out.tx_id = tx_in.tx_out_id
  inner join tx
    on (tx.id, tx_in.tx_out_index) = (tx_in.tx_in_id, tx_out.index)
  inner join block
    on tx.block_id = block.id
  inner join tx_metadata
    on tx_metadata.tx_id = tx.id
  where block.slot_no > 129832246
    and tx_out.address in (
          'addr1vy0zwnn5yj4h3s25xuere4h38np4z6gcng2mdgxg0mapxagl6x66d'
        , 'addr1vxpvhtj5vvcqmf9td3vlvv4vza9nnuqrmkc42cnd42dg7fsz0v99d'
        , 'addr1vx7gvyvy2r7mycya22f3x88wlgra2552uxm8xz2g0v3g6yccgyydv'
        , 'addr1vx2uvrm53dak4x3u0txy98r2jpg2nhy0n82vk8a6v9wmk4s8up888'
        )
order by time
;

create index idx_canary_slot_no
  on canary (slot_no)
;

create index idx_canary_sub_slot_no
  on canary (sub_slot_no)
;

\copy canary to 'canary.csv' csv header


drop table if exists canary_slots;

create temporary table canary_txs as
select
    time
  , delay
  , json
  , round(avg(delay) over (order by time rows between 4 preceding and current row), 1) as avg_delay_1h
  , round(avg(delay) over (order by time rows between 24 preceding and current row), 1) as avg_delay_6h
  from canary
order by time desc
;

\copy canary_txs to 'canary-txs.csv' csv header


drop table if exists canary_blocks;

create temporary table canary_blocks as
select
    canary.time
  , count(block.block_no) as block_delay
  from canary
  join block
    on block.slot_no <= canary.slot_no and block.slot_no >= canary.sub_slot_no 
  group by canary.time
order by canary.time desc
;

\copy canary_blocks to 'canary-blocks.csv' csv header

