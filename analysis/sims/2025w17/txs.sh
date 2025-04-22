#!/usr/bin/env nix-shell
#!nix-shell -i bash -p jq dasel gawk gzip

jq -c '
  select(.message.type | match("(TX|IB|EB|RB)Generated$"))
| .message.id as $id
| .time_s as $time
| if .message.type == "TXGenerated" then
    [
      {
        event: "TX",
        tx: $id,
        time: .time_s,
        size: .message.size_bytes,
      }
    ]
  elif .message.type == "IBGenerated" then
    [
      .message.transactions.[] | {
        event: "TX2IB",
        tx: .,
        ib: $id,
        time: $time,
      }
    ]
  elif .message.type == "EBGenerated" then
    [
      .message.input_blocks.[] | {
        event: "IB2EB",
        ib: .id,
        eb: $id,
        time: $time,
      }
    ] + [
      .message.endorser_blocks.[] | {
        event: "EB2EB",
        eb: .id,
        parent: $id,
        time: $time,
      }
    ]
  elif .message.type == "RBGenerated" and .message.endorsement then
    [
      .message.transactions.[] | {
        event: "TX2RB",
        tx: .,
        rb: $id,
        time: $time,
      }
    ] + [
      {
        event: "EB2RB",
        eb: .message.endorsement.eb.id,
        rb: $id,
        time: $time,
      }
    ]
  elif .message.type == "RBGenerated" then
    [
      .message.transactions.[] | {
        event: "TX2RB",
        tx: .,
        rb: $id,
        time: $time,
      }
    ]
  else
    []
  end
| .[]
' "$1" \
| dasel -r json -w csv \
| sed -n -e '0~2p' \
| gawk '
BEGIN {
  FS = ","
  OFS=","
  na = "NA"
}
$1 == "TX" {
  tx = $2
  time = $3
  size = $4
  txGenerated[tx] = time
  txSize[tx] = size
  txIbCount[tx] = 0
  tx2Ib[tx] = "NA"
  txEbCount[tx] = 0
  tx2Eb[tx] = "NA"
  txRbCount[tx] = 0
  tx2Rb[tx] = "NA"
  txPraosCount[tx] = 0
  tx2Praos[tx] = "NA"
}
$1 == "TX2IB" {
  tx = $2
  ib = $3
  time = $4
  txIb[tx SUBSEP ib] = 1
  txIbCount[tx] += 1
  if (tx2Ib[tx] == na)
    tx2Ib[tx] = time - txGenerated[tx]
}
$1 == "IB2EB" {
  ib = $2
  eb = $3
  time = $4
  for (tx in txGenerated) {
    if ((tx SUBSEP ib) in txIb) {
      txEbCount[tx] += 1
      if (tx2Eb[tx] == na)
        tx2Eb[tx] = time - txGenerated[tx]
      txEb[tx SUBSEP eb] = 1
    }
  }
}
$1 == "EB2EB" {
  eb = $2
  parent = $3
  time = $4
  for (tx in txGenerated) {
    if ((tx SUBSEP eb) in txEb) {
      txEb[tx SUBSEP parent] = 1
    }
  }
}
$1 == "EB2RB" {
  eb = $2
  rb = $3
  time = $4
  for (tx in txGenerated) {
    if ((tx SUBSEP eb) in txEb) {
      txRbCount[tx] += 1
      if (tx2Rb[tx] == na)
        tx2Rb[tx] = time - txGenerated[tx]
    }
  }
}
$1 == "TX2RB" {
  tx = $2
  rb = $3
  time = $4
  txPraosCount[tx] += 1
  if (tx2Praos[tx] == na)
    tx2Praos[tx] = time - txGenerated[tx]
}
END {
  print "Tx", "Generated [s]", "Size [B]", "IB inclusions", "Time to IB [s]", "EB references", "Time to EB reference [s]", "RB references", "Time to RB reference [s]", "Praos inclusions", "Time to Praos inclusion [s]"
  for (tx in txGenerated) {
    print tx, txGenerated[tx], txSize[tx], txIbCount[tx], tx2Ib[tx], txEbCount[tx], tx2Eb[tx], txRbCount[tx], tx2Rb[tx], txPraosCount[tx], tx2Praos[tx]
  }
}
' \
| gzip -9c \
>"$2"
