-- query to obtain utilisation and tx count for all blocks in a given range

drop table if exists block_util;

create temporary table block_util as
select 
    epoch
  , height
  , time
  , slot
  , size
  , tx_count
  , (block.size :: real) / (epoch_param.max_block_size :: real) as util
from block
-- for the period 20241201 to 20251031
where time >= 1733011200 and time <= 1761955199

-- if possible: longer period, up to today
-- where time >= 1733011200

-- if necessary: shorter (6 months)
-- where time >= 1733011200 and time <= 1748735999

\copy block_util to 'block_util.csv' csv header

-- estimate of output size
--
-- 1.2 MB per epoch
-- 11 months ~ 335 days
-- 5 days per epoch
-- 67 epochs
-- total: around 81 MB