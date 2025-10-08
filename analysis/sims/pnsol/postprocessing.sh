#!/usr/bin/env bash

(
echo $'Time [s],RB,Parent,EB'
zcat sim.log.gz \
| grep '"RBGenerated"' \
| jq -r '
  select(.message.type == "RBGenerated")
| (.time_s | tostring) + "," + .message.id + "," + .message.parent.id + "," + (
    if .message.endorsement
    then .message.endorsement.eb.id
    else "NA"
    end
  )
'
) | gzip -9c > certified.csv.gz

(
echo $'Time [s],Kind,Block,Tx'
zcat sim.log.gz \
| grep -E '"(RB|EB)Generated"' \
| jq -r '
  select(.message.type == "RBGenerated" or .message.type == "EBGenerated")
| (.time_s | tostring) as $time_s
| .message.id as $block_id
| if .message.type == "RBGenerated"
  then
       .message.transactions[]
     | $time_s + ",RB," + $block_id + "," + .
  else
       .message.transactions[]
     | $time_s + ",EB," + $block_id + "," + .id
  end
'
) | gzip -9c > generated.csv.gz
