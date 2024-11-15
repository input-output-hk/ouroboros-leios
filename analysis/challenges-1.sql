
drop table if exists block_production;

create temporary table block_production as
select
    epoch_no           as "Epoch"
  , block_no           as "Block"
  , slot_no            as "Slot"
  , block.size         as "Size [B]"
  , tx_count           as "Transactions"
  , sum(fee) / 1000000 as "Fee [ADA]"
  from block
  inner join tx
    on tx.block_id = block.id
  where epoch_no >= 335
  group by epoch_no, block_no, slot_no, block.size, tx_count
;

\copy block_production to 'block_production.csv' csv header


drop table if exists reward_earned;

create temporary table reward_earned as
select
    earned_epoch          as "Epoch Earned"
  , spendable_epoch       as "Epoch Spendable"
  , type                  as "Party"
  , sum(amount) / 1000000 as "Reward [ADA]"
  from reward
  where earned_epoch >= 335
    and type <> 'refund'
  group by earned_epoch, spendable_epoch, type
;

\copy reward_earned to 'reward_earned.csv' csv header


drop table if exists reserve_amount;

create temporary table reserve_amount as
select
    epoch_no                          as "Epoch"
  , reserves / 1000000                as "Reserves [ADA]"
  , treasury / 1000000                as "Treasury [ADA]"
  , coalesce(withdrawal, 0) / 1000000 as "Treasury Withdrawal [ADA]"
  from ada_pots
  left outer join (
    select epoch_no + 1 as epoch_no, sum(treasury.amount) as withdrawal
      from treasury
      inner join tx
        on tx.id = treasury.tx_id
      inner join block
        on block.id = tx.block_id
      group by epoch_no
  ) tw
    using (epoch_no)
  where epoch_no >= 335
order by epoch_no
;

\copy reserve_amount to 'reserve_amount.csv' csv header

