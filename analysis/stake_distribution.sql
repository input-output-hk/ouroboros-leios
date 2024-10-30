
drop table if exists stake_distribution;

create temporary table stake_distribution as
select
    epoch_no                  as "Epoch"
  , encode(hash_raw, 'hex')   as "Pool"
  , sum(amount)               as "Stake [Lovelace]"
  , sum(amount) / total_stake as "Stake [Fraction]"
  from epoch_stake
  inner join pool_hash
    on epoch_stake.pool_id = pool_hash.id
  inner join (
    select epoch_no, sum(amount) as total_stake
      from epoch_stake
      group by epoch_no
  ) stake_total
    using (epoch_no)
  group by epoch_no, hash_raw, total_stake
;

\copy stake_distribution to 'stake_distribution.csv' csv header
