
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
--where id between 118811946 and 118822448 -- 12MB scenario
--where id between 118811946 and 118813600 -- 2MB scenario
order by tx_id
;

select
    block_type
  , count(*) as block_txs
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
  , coalesce(redeemer.unit_steps :: numeric, 0) as steps
  from leios_tx
  inner join tx_in
    on tx_in.tx_in_id = leios_tx.tx_id
  inner join tx
    on tx.id = tx_in.tx_out_id
  left join redeemer
    on redeemer.id = tx_in.redeemer_id
;


drop table if exists leios_scenario;

create temporary table leios_scenario as
select
    json_build_object(
      'parameters', json_build_object(
        'n_cpu', 4
      , 'delta_rh', round(500000 + 1000000 * random())
      , 'delta_rb', round(500000 + 1500000 * random())
      , 'delta_eh', round(500000 + 2000000 * random())
      , 'cost_vote', 300000
    )
    , 'dag', json_object_agg(tx_hash8, tx_info)
  ) as scenario
  from (
    select
        left(tx_in_hash, 8) as tx_hash8
      , json_build_object('type', 'LG') as tx_info
      from (
        select tx_in_hash from leios_txin
        except
        select tx_hash from leios_tx
      ) ledger
    union all
    select
        left(tx_hash, 8) as tx_hash8
      , json_build_object(
          'type', block_type
        , 'arrival_delay', case when block_type = 'RB' then 0 else round(10000 + (2000000 - 10000) * random()) end
        , 'cost_verify' , round((0.2e8 +                        1.0e3 * count(*)                      ) / 1e6)
        , 'cost_apply'  , round((1.0e8 + 4.7e4 * avg(tx_size) + 7.0e3 * count(*) + 0.61e0 * sum(steps)) / 1e6)
        , 'cost_reapply', round((3.5e7 + 2.8e3 * avg(tx_size) + 5.2e6 * count(*)                      ) / 1e6)
        , 'inputs', json_agg(left(tx_in_hash, 8))
        ) as tx_info
      from leios_txin
      group by tx_hash, block_type
  ) t
;

\copy leios_scenario TO 'scenario.json' WITH (FORMAT text)

