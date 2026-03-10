
drop table if exists block_util;

create temporary table block_util as
select
    epoch_no as epoch
  , block_no as height
  , time
  , slot_no as slot
  , size
  , tx_count
  , (size :: numeric) / max_block_size as util
  from block
  inner join epoch_param
    using (epoch_no)
  where time >= '2024-12-01 00:00:00'
order by 4
;

\copy block_util to 'block_util.csv' csv header

