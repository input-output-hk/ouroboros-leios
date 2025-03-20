#!/usr/bin/env bash

source env.sh

mongoexport --host="$HOST" \
            --db="$DB" \
            --collection=receipts \
            --type=csv \
            --fields='simulator,network,label,leios-stage-length-slots,ib-generation-probability,ib-body-avg-size-bytes,eb-generation-probability,kind,item,producer,recipient,sent,received,elapsed' \
| gzip -9vc > results/receipts.csv.gz

mongoexport --host="$HOST" \
            --db="$DB" \
            --collection=cpus \
            --type=csv \
            --fields 'simulator,network,leios-stage-length-slots,ib-generation-probability,ib-body-avg-size-bytes,eb-generation-probability,label,slot,node,task,duration' \
| gzip -9vc > results/cpus.csv.gz

mongoexport --host="$HOST" \
            --db="$DB" \
            --collection=ibgen \
            --type=csv \
            --fields='simulator,network,label,leios-stage-length-slots,ib-generation-probability,ib-body-avg-size-bytes,eb-generation-probability,time,ib,node,eb-count,eb-first,eb-last,size' \
| gzip -9vc > results/ibgen.csv.gz

mongoexport --host="$HOST" \
            --db="$DB" \
            --collection=ebgen \
            --type=csv \
            --fields='simulator,network,label,leios-stage-length-slots,ib-generation-probability,ib-body-avg-size-bytes,eb-generation-probability,time,eb,node,ib-count,rb-count,rb-first,rb-last,size' \
| gzip -9vc > results/ebgen.csv.gz

mongoexport --host="$HOST" \
            --db="$DB" \
            --collection=rbgen \
            --type=csv \
            --fields='simulator,network,label,leios-stage-length-slots,ib-generation-probability,ib-body-avg-size-bytes,eb-generation-probability,time,rb,eb-count,size' \
| gzip -9vc > results/rbgen.csv.gz
