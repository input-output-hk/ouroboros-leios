#!/usr/bin/env nix-shell
#!nix-shell -i bash -p jq dasel gnused gzip

jq -c '
  select(.message.type | match("Generated$"))
| .time_s as $time
| .message.id as $id
| .message.size_bytes as $size
| if .message.type == "TXGenerated" then
    [
      {
	time: $time
      , kind: "TX"
      , item: $id
      , size: $size
      , relation: "generated"
      , references: "NA"
      }
    ]
  elif .message.type == "IBGenerated" then
    [
      {
        time: $time
      , kind: "IB"
      , item: $id
      , size: $size
      , relation: "NA"
      , references: "NA"
      }      
    ] + [
      .message.transactions.[]
    | {
        time: $time
      , kind: "IB"
      , item: $id
      , size: $size
      , relation: "TX"
      , references: .
      }      
    ]
  elif .message.type == "EBGenerated" then
    [
      {
        time: $time
      , kind: "EB"
      , item: $id
      , size: $size
      , relation: "NA"
      , references: "NA"
      }      
    ] + [
      .message.input_blocks.[]
    | {
        time: $time
      , kind: "EB"
      , item: $id
      , size: $size
      , relationship: "IB"
      , references: .id
    }
    ] + [
      .message.endorser_blocks.[]
    | {
        time: $time
      , kind: "EB"
      , item: $id
      , size: $size
      , relationship: "EB"
      , references: .id
    }
    ]
  elif .message.type == "RBGenerated" and .message.endorsement then
    [
      {
        time: $time
      , kind: "RB"
      , item: $id
      , size: $size
      , relation: "NA"
      , references: "NA"
      }      
    ] + [
      {
        time: $time
      , kind: "RB"
      , item: $id
      , size: $size
      , relationship: "EB"
      , references: .message.endorsement.eb.id
      }
    ] + [
      .message.transactions.[]
    | {
        time: $time
      , kind: "RB"
      , item: $id
      , size: $size
      , relationship: "TX"
      , references: .
      }
    ]
  elif .message.type == "RBGenerated" then
    [
      {
        time: $time
      , kind: "RB"
      , item: $id
      , size: $size
      , relation: "NA"
      , references: "NA"
      }      
    ] + [
      .message.transactions.[]
    | {
        time: $time
      , kind: "RB"
      , item: $id
      , size: $size
      , relationship: "TX"
      , references: .
      }
    ]
  else
    []
  end
| .[]
' "$1" \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
| gawk '
BEGIN {
  FS=","
  OFS="\t"
}
$2 == "TX" {
  time = $1
  id = $3
  size = $4
  txSize[id] = size
  txTime[id] = time
  txCopied[id] = 0
  txIbTime[id] = "NA"
  txEbTime[id] = "NA"
  txRbTime[id] = "NA"
  txPraosTime[id] = "NA"
  txPraosCount[id] = 0
}
$2 == "IB" && $5 == "NA" {
  time = $1
  id = $3
  size = $4
  ibSize[id] = size
  ibTime[id] = time
  ibCopied[id] = 0
  ibEbTime[id] = "NA"
  ibRbTime[id] = "NA"
}
$2 == "IB" && $5 == "TX" {
  time = $1
  id = $3
  references = $6
  txCopied[references] += 1
  if (txIbTime[references] == "NA")
    txIbTime[references] = time
  txInIb[references SUBSEP id] = time
}
$2 == "EB" && $5 == "NA" {
  time = $1
  id = $3
  size = $4
  ebSize[id] = size
  ebTime[id] = time
  ebCopied[id] = 0
  ebRbTime[id] = "NA"
}
$2 == "EB" && $5 == "IB" {
  time = $1
  id = $3
  references = $6
  ibCopied[references] += 1
  if (ibEbTime[references] == "NA")
    ibEbTime[references] = time
  ibInEb[references SUBSEP id] = time
  for (i in txInIb) {
    split(i, txIb, SUBSEP)
    if (txIb[2] == references) {
      if (txEbTime[txIb[1]] == "NA")
	txEbTime[txIb[1]] = time
      txInEb[txIb[1] SUBSEP id] = time
    }
  }
}
$2 == "EB" && $5 == "EB" {
  time = $1
  id = $3
  references = $6
  ebCopied[references] += 1
  for (i in ibInEb) {
    split(i, ibEb, SUBSEP)
    if (ibEb[2] == references) {
      if (ibEbTime[ibEb[1]] == "NA")
	ibEbTime[ibEb[1]] = time
      ibInEb[ibEb[1] SUBSEP id] = time
    }
  }
  for (i in txInEb) {
    split(i, txEb, SUBSEP)
    if (txEb[2] == references) {
      if (txEbTime[txEb[1]] == "NA")
	txEbTime[txEb[1]] = time
      txInEb[txEb[1] SUBSEP id] = time
    }
  }
}
$2 == "RB" && $5 == "NA" {
  time = $1
  id = $3
  size = $4
  references = $6
  rbSize[id] += size
  rbTime[id] = time
}
$2 == "RB" && $5 == "EB" {
  time = $1
  id = $3
  references = $6
  if (ebRbTime[references] == "NA")
    ebRbTime[references] = time
  for (i in ibInEb) {
    split(i, ibEb, SUBSEP)
    if (ibEb[2] == references) {
      if (ibRbTime[ibEb[1]] == "NA")
	ibRbTime[ibEb[1]] = time
    }
  }
  for (i in txInEb) {
    split(i, txEb, SUBSEP)
    if (txEb[2] == references) {
      if (txRbTime[txEb[1]] == "NA")
	txRbTime[txEb[1]] = time
    }
  }
}
$2 == "RB" && $5 == "TX" {
  time = $1
  id = $3
  references = $6
  rbTime[id] = time
  if (txPraosTime[references] == "NA") {
    txPraosTime[references] = time
  }
}
END {
  print "Kind", "Item", "Size [B]", "References", "Created [s]", "To IB [s]", "To EB [s]", "To RB [s]", "In RB [s]"
  for (tx in txTime) {
    print "TX", tx, txSize[tx], txCopied[tx], txTime[tx], txIbTime[tx], txEbTime[tx], txRbTime[tx], txPraosTime[tx]
  }
  for (ib in ibTime) {
    print "IB", ib, ibSize[ib], ibCopied[ib], ibTime[ib], "NA", ibEbTime[ib], ibRbTime[ib], "NA"
  }
  for (eb in ebTime) {
    print "EB", eb, ebSize[eb], ebCopied[eb], ebTime[eb], "NA", "NA", ebRbTime[eb], "NA"
  }
  for (rb in rbTime) {
    print "RB", rb, rbSize[rb], "NA", rbTime[rb], "NA", "NA", "NA", "NA"
  }
}
' \
| gzip -9c \
> "$2"
