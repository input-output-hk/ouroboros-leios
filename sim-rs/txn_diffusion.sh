#!/bin/bash

jq --unbuffered -rc 'select(.message.type=="TransactionGenerated") | (.message.id|tostring)+" "+(.time|tostring)' < "$1" |
(
  while read id t; do
    echo $id $t
    CDF=`(
      echo $t
      jq -c 'select(.message|.type=="TransactionReceived" and .id=='$id') | {time,id:.message.id}' < "$1"
    ) | jq -srf convert.jq`
    if [ -z "$RET" ]; then
      RET="$CDF"
      N=1
    else
      RET="$CDF\n1<>$N\n$RET"
      let N++
    fi
  done
  echo -e "$RET"
)