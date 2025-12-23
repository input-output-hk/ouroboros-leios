
drop table if exists utxo_creation;

create temporary table utxo_creation as
select
    encode(tx.hash, 'hex') || '#' || tx_out.index as utxo_id
  , tx.id as tx_create_id
  , coalesce(block.slot_no, 0) as slot_created
  , coalesce(block.block_no, 0) as block_created
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
  , tx_create.id as tx_create_id
  , block.slot_no as slot_spent
  , block.block_no as block_spent
  , tx_spend.id as tx_spend_id
  from tx_in
  inner join tx tx_spend
    on tx_spend.id = tx_in.tx_in_id
  inner join block
    on block.id = tx_spend.block_id
  inner join tx tx_create
    on tx_create.id = tx_in.tx_out_id
  where tx_create.valid_contract
    and tx_spend.valid_contract
;

create index ix_spending
  on utxo_spending (utxo_id)
;


drop table if exists utxo_history;

create temporary table utxo_history as
select
    utxo_id
  , utxo_creation.tx_create_id
  , utxo_spending.tx_spend_id
  , utxo_creation.slot_created
  , utxo_spending.slot_spent
  , utxo_creation.block_created
  , utxo_spending.block_spent
  from utxo_creation
  left join utxo_spending
    using (utxo_id)
order by 4, 5
;

\copy utxo_history to 'utxo-history.tsv' csv header delimiter E'\t'


drop table if exists utxo_creation;
drop table if exists utxo_spending;


drop table if exists utxo_lifetime;

create temporary table utxo_lifetime as
select
    slot_spent - slot_created as slot_lifetime
  , block_spent - block_created as block_lifetime
  , count(*) as utxo_count
  from utxo_history
  where slot_spent is not null or block_spent is not null
  group by slot_spent - slot_created, block_spent - block_created
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


drop table if exists utxo_ephemeral;

create temporary table utxo_ephemeral as
select
    utxo_id
  , tx_create_id
  , tx_spend_id
  , slot_created
  , slot_spent
  , block_created
  , block_spent
  from utxo_history
  where block_spent - block_created between 0 and 0
order by 4, 5, 1
;

create index ix_ephemeral on
  utxo_ephemeral (utxo_id)
;

create index ix_ephemeral_create on
  utxo_ephemeral (tx_create_id)
;

create index ix_ephemeral_spend on
  utxo_ephemeral (tx_spend_id)
;

\copy utxo_ephemeral to 'utxo-ephemeral.tsv' csv header delimiter E'\t'


drop table if exists component_edges;

create temporary table component_edges as
select
    utxo_id
  , least(tx_create_id, tx_spend_id) as component
  from utxo_ephemeral
;
create index ix_component_edges on
  component_edges (utxo_id)
;

-- Repeat the following queries until the result stops changing.
DO $$ 
DECLARE 
component_count numeric;
component_sum numeric;
BEGIN 
FOR i IN 1..175 LOOP

drop table if exists component_nodes;
create temporary table component_nodes as
select
    tx_id
  , min(component) as component
  from ( 
    select
        tx_create_id as tx_id
      , component
      from utxo_ephemeral
      inner join component_edges
        using (utxo_id)
    union
    select
        tx_spend_id
      , component
      from utxo_ephemeral
      inner join component_edges
        using (utxo_id)
  ) items
  group by tx_id
;
create index ix_component_nodes on
  component_nodes (tx_id)
;
drop table if exists component_edges;
create temporary table component_edges as
select
    utxo_id
  , least(c.component, s.component) as component
  from utxo_ephemeral e
  inner join component_nodes c
    on c.tx_id = e.tx_create_id
  inner join component_nodes s
    on s.tx_id = e.tx_spend_id
;
create index ix_component_edges on
  component_edges (utxo_id)
;

select
  into component_count, component_sum
    count(distinct component) :: numeric as component_count
  , sum(component :: numeric) as component_sum
  from component_edges
;
RAISE NOTICE 'Components: %; Sum: %.', component_count, component_sum;
END LOOP;
END $$;

-- Continue after convergence.

drop table if exists utxo_components;

create temporary table utxo_components as
select
    utxo_id
  , tx_create_id
  , tx_spend_id
  , slot_created
  , slot_spent
  , block_created
  , block_spent
  , component
  from utxo_ephemeral
  inner join component_edges
    using (utxo_id)
order by 8, 4, 5
;

\copy utxo_components to 'utxo-ephemeral.tsv' csv header delimiter E'\t'

