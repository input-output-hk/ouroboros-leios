
drop table if exists leios_tx;

create temporary table leios_tx as
select
    case
      when id between 118811946 and 118812014 then 'RB' :: char(2)
      else 'EB'
    end as block_type
  , id as tx_id
  , encode(hash, 'hex') as tx_hash
  , size as tx_size
  from tx
  where id between 118811946 and 118822448
order by tx_id
;


select
    block_type
  , sum(tx_size) as block_size
  from leios_tx
  group by block_type
order by block_type desc
;


drop table if exists leios_txin;

create temporary table leios_txin as
select
    block_type
  , tx_hash
  , tx_in_id as tx_id
  , tx_size
  , encode(tx.hash, 'hex') as tx_in_hash
  , tx_in.tx_out_index as tx_in_index
  , coalesce(redeemer.unit_steps :: numeric, 0) / 1000 as ksteps
  from leios_tx
  inner join tx_in
    on tx_in.tx_in_id = leios_tx.tx_id
  inner join tx
    on tx.id = tx_in.tx_out_id
  left join redeemer
    on redeemer.id = tx_in.redeemer_id
;


drop table if exists leios_dag;

create temporary table leios_dag as
select
    json_build_object(
      left(tx_in_hash, 8)
    , json_build_object(
        'type', 'LG'
      )
    ) as tx
  from (
    select tx_in_hash from leios_txin
    except
    select tx_hash from leios_tx
  ) ledger
union all
select
  json_build_object(
    left(tx_hash, 8)
  , json_build_object(
      'type', block_type
    , 'arrival_delay', round(10000 + (2000000 - 10000) * random())
    , 'cost_verify', 2000
    , 'cost_apply', 3000
    , 'inputs', json_agg(left(tx_in_hash, 8))
    )
  ) as tx
  from leios_txin
  group by tx_hash, block_type
;


