#!/usr/bin/env nix-shell
#!nix-shell -i bash -p postgresql wget jq

set -eo pipefail

psql --csv -h thelio mainnet << EOI > url.list
select
  'https://s3-us-west-2.amazonaws.com/data.pooltool.io/blockdata/'
    || floor(block_no / 1000)
    || '/C_'
    || encode(hash, 'hex')
    || '.json' as URL
  from (
    select
        epoch_no
      , percentile_disc(0.5) WITHIN GROUP (ORDER BY block_no) as block_no
      from block
      where epoch_no between 325 and 575
        and size = 4
      group by epoch_no
    ) sample
    inner join block
      using (epoch_no, block_no)
order by epoch_no desc
;
EOI

tail -n +2 url.list | \
while read url
do
  wget "$url"
  sleep 0.75s
done

(
echo $'Epoch\tSlot\tMilliseconds from slot time'
jq -r '.
| .epoch as $epoch
| .slot as $slot
| .rawtips.[]
| ($epoch | tostring) + "\t" + ($slot | tostring) + "\t" + (. | tostring)
' C_*.json
) > timings.tsv
