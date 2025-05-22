-- DB Sync queries to measure the number of slots between consecutive blocks.

-- Tally gap distribution for past year.
select
    sum(case when gap_size > 5 * 60 then observations else 0 end) as "Gaps longer than 5 minutes"
  , sum(case when gap_size between 4 * 60 and 5 * 60 - 1 then observations else 0 end) as "Gaps between 4 and 5 minutes"
  , sum(case when gap_size between 3 * 60 and 4 * 60 - 1 then observations else 0 end) as "Gaps between 3 and 4 minutes"
  , sum(case when gap_size between 2 * 60 and 3 * 60 - 1 then observations else 0 end) as "Gaps between 2 and 3 minutes"
  , sum(case when gap_size between 1 * 60 and 2 * 60 - 1 then observations else 0 end) as "Gaps between 1 and 2 minutes"
  , sum(case when gap_size < 1 * 60 then observations else 0 end) as "Gaps less than 1 minute"
  from (
    select
        gap_size
      , count(*) as observations
      from (
        select
            slot_no
          , slot_no - lag(slot_no) over (order by slot_no) as gap_size
        from
            block
        where
            epoch_no between 550 - 365 / 5 and 550
      ) gaps
      group by gap_size
  ) histogram
;

-- List largest gaps in past year.
select
      slot_no
    , slot_no - lag(slot_no) over (order by slot_no) as gap_size
  from
      block
  where
      epoch_no between 550 - 365 / 5 and 550
order by gap_size desc
limit 10
;

-- List largest gaps ever.
select
      slot_no
    , slot_no - lag(slot_no) over (order by slot_no) as gap_size
  from
      block
order by gap_size desc
limit 10
;
