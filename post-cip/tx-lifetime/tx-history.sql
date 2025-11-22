
drop table if exists utxo_creation;

create temporary table utxo_creation as
select
    encode(tx.hash, 'hex') || '#' || tx_out.index as utxo_id
  , coalesce(block.slot_no, 0) as slot_created
  from block
  inner join tx
    on tx.block_id = block.id
  inner join tx_out
    on tx_out.tx_id = tx.id
  where tx.valid_contract
;

create index ix_creation
  on utxo_creation (utxo_id)
;


drop table if exists utxo_spending;

create temporary table utxo_spending as
select
    encode(tx_create.hash, 'hex') || '#' || tx_in.tx_out_index as utxo_id
  , block.slot_no as slot_spent
  from tx_in
  inner join tx tx_spend
    on tx_spend.id = tx_in.tx_in_id
  inner join block
    on block.id = tx_spend.block_id
  inner join tx tx_create
    on tx_create.id = tx_in.tx_out_id
  where tx_create.valid_contract and tx_spend.valid_contract
;

create index ix_spending
  on utxo_spending (utxo_id)
;


drop table if exists utxo_history;

create temporary table utxo_history as
select
    utxo_id
  , slot_created
  , slot_spent
  from utxo_creation
  left join utxo_spending
    using (utxo_id)
order by 2, 3
;

\copy utxo_history to 'utxo-history.tsv' csv header delimiter E'\t'


drop table if exists utxo_lifetime;

create temporary table utxo_lifetime as
select
    slot_spent - slot_created as lifetime
  , count(*) as utxo_count
  from utxo_history
  where slot_spent is not null
  group by slot_spent - slot_created
order by 1
;

\copy utxo_lifetime to 'utxo-lifetime.tsv' csv header delimiter E'\t'


drop table if exists utxo_delta;

create temporary table utxo_delta as
select
    slot
  , sum(utxo_delta) as utxo_delta
  from (
    select
        slot_created as slot
      , 1 as utxo_delta
      from utxo_history
    union all
    select
        slot_spent as slot
      , -1
      from utxo_history
      where slot_spent is not null
  ) s
  group by slot
  having sum(utxo_delta) != 0
order by 1
;


drop table if exists utxo_set;

create temporary table utxo_set as
select
    slot
  , sum(utxo_delta) over (
      order by slot
    ) as utxo_set_size
  from utxo_delta
order by 1
;

\copy utxo_set to 'utxo-set.tsv' csv header delimiter E'\t'

