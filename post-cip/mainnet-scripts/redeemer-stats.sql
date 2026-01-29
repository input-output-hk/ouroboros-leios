
drop table if exists redeemer_stats;

create temporary table redeemer_stats as
select
    encode(script_hash, 'hex') as script_hash
  , purpose
  , count(*) as redeemer_count
  , avg(unit_mem) as mem_avg
  , avg(unit_steps) as steps_avg
  , count(*) / total_count as redeemer_fraction
  , sum(unit_mem) / total_mem as mem_fraction
  , sum(unit_steps) / total_steps as steps_fraction
  from redeemer
  cross join (
    select
        count(*) :: numeric as total_count
      , sum(unit_mem) as total_mem
      , sum(unit_steps) as total_steps
      from redeemer
  ) totals
  group by script_hash, purpose, total_count, total_mem, total_steps
order by redeemer_count desc
;

\copy redeemer_stats to 'redeemer-stats.csv' csv header

\copy (select * from redeemer_stats order by redeemer_count desc limit 100) to 'redeemer-stats-top100.csv' csv header
