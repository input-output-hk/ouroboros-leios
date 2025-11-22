
drop table if exists active_slots;

create table active_slots as
select
    slot_no
  , cast(slot_no - lag(slot_no, 30, null) over (order by slot_no asc) as float)
    / (block_no - lag(block_no, 30, null) over (order by block_no asc))
    as slots_per_block
  , (block_no - lag(block_no, 30, null) over (order by block_no asc))
    / cast(slot_no - lag(slot_no, 30, null) over (order by slot_no asc) as float)
    as blocks_per_slot
  from block
  where block_no is not null
  order by block_no
  desc
;

\copy active_slots to 'active-slots.tsv' csv header delimiter E'\t'

