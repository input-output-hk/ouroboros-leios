#!/usr/bin/env nix-shell
#!nix-shell -i bash -p gnused gawk gzip jq

zcat sim.log.gz \
| grep -E '(RBGenerated|EBGenerated|EBReceived|ValEB)' \
| jq -r '
    if .message.type == "RBGenerated" then
      [
        .message.producer
      , .time_s
      , .message.type
      , .message.id
      , .message.endorsement.eb.id?
      ]
    elif .message.type == "EBGenerated" then
      [
        .message.producer
      , .time_s
      , .message.type
      , .message.id
      , null
      ]
    elif .message.type == "EBReceived" then
      [
        .message.recipient
      , .time_s
      , .message.type
      , .message.id
      , null
      ]
    else
      [
        .message.node
      , .time_s
      , .message.task_type
      , null
      , null
      ]
    end
  | @tsv
' \
| sort -t$'\t' -k1,1 -k2,2n \
| gawk '
BEGIN {
  FS="\t"
  OFS="\t"
  print "Node", "Time [s]", "Event", "EB", "Endorsement"
}
$3 == "EBReceived" {
  previousItem = $4
}
{
   print $1, $2, $3, ($4 == "" ? previousItem : $4), ($5 == "" ? "NA" : $5)
}
' \
| gzip -9c \
> eb-validation.tsv.gz

jq -r '
  .nodes
| to_entries
| .[]
| [
    .key
  , .value.stake
  ]
| @tsv
' ../../../../../data/simulation/pseudo-mainnet/topology-v2.yaml \
| sed -e '1iNode\tStake' \
| gzip -9c \
> node-stake.tsv.gz
