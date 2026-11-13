-- Reporting coverage of a testnet window (report section 3, Table 3.3, and
-- the stage-table captions): for each loaded window and each seat of the
-- committee of the epochs whose EBs fall in it, the seat's weight and
-- whether its pool is observed, which means the pool's own votes or vote
-- refusals (Consensus.LeiosKernel.Voted / NotVoted) are in the period
-- database. Written as voters.csv, the columns the stage-table script reads
-- (win, seat, pool_id, ticker, weight, reporting); the same selection as the
-- voters table of the causes pass.
--
-- Variables: t0, t1 (period bounds, UTC 'YYYY-MM-DD HH:MM:SS'), win (the
-- windows file), chain and committee (default chain-2026-10-18/blocks.sqlite
-- and committee.sqlite under the working directory, the data folder).
--
--   duckdb -readonly -markdown archive/f2-high-merged.duckdb \
--     -c "set variable t0 = '2026-10-24 12:00:00'; set variable t1 = '2026-10-26 13:00:00'; set variable win = '.../data/windows/windows-f2-high.txt';" \
--     -f .../scripts/instruments/coverage.sql
set timezone = 'UTC';
create temp table p as select getvariable('t0')::timestamptz t0, getvariable('t1')::timestamptz t1;
create temp table win as
  select row_number() over () win, s::timestamp s, e::timestamp e
  from read_csv(getvariable('win'), delim = ' ', header = false, columns = {'s': 'varchar', 'e': 'varchar'}, ignore_errors = true)
  where s not like '#%';
create temp table chainblk as
  select block_no, epoch_no, strptime(time, '%Y-%m-%dT%H:%M:%SZ') t, eb_announcement_hash
  from sqlite_scan(coalesce(getvariable('chain'), 'chain-2026-10-18/blocks.sqlite'), 'block') where slot_no is not null;
create temp table seat as select * from sqlite_scan(coalesce(getvariable('committee'), 'chain-2026-10-18/committee.sqlite'), 'seat');
create temp table pool as select * from sqlite_scan(coalesce(getvariable('committee'), 'chain-2026-10-18/committee.sqlite'), 'pool');
-- a pool is observed when its node voted or refused to vote anywhere in the period
create temp table reporting as
  select distinct pool from trace, p
  where ns in ('Consensus.LeiosKernel.Voted', 'Consensus.LeiosKernel.NotVoted') and t >= p.t0 and t < p.t1;
-- the committees in play per window: the epochs of the EBs announced inside it
create temp table epochs as
  select distinct w.win, b.epoch_no
  from chainblk b join win w on b.t >= w.s and b.t < w.e
  where b.eb_announcement_hash is not null;
copy (
  select e.win, s.seat, s.pool_id, any_value(pl.ticker) ticker, round(s.weight, 4) weight,
         s.pool_id in (select pool from reporting) reporting
  from epochs e join seat s on s.epoch = e.epoch_no left join pool pl on pl.pool_id = s.pool_id
  group by e.win, s.seat, s.pool_id, s.weight, s.epoch order by e.win, s.seat, s.epoch
) to 'voters.csv' (header, delimiter ',');
select win, count(*) seats, count(distinct pool_id) pools, round(sum(weight), 3) weight,
       round(sum(weight) filter (where reporting), 3) reporting_weight,
       round(sum(weight) filter (where reporting) / sum(weight), 3) reporting_share
from read_csv_auto('voters.csv') group by 1 order by 1;
