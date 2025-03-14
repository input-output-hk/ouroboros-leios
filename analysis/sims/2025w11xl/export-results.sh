#!/usr/bin/env bash

source env.sh

mongoexport --host="$HOST" \
            --db="$DB" \
            --collection=receipts \
            --type=csv \
            --fields='elapsed,ib-body-avg-size-bytes,ib-generation-probability,item,kind,label,leios-stage-length-slots,network,producer,received,recipient,sent,simulator' \
| gzip -9vc > results/receipts.csv.gz

mongoexport --host="$HOST" \
            --db="$DB" \
            --collection=cpus \
            --type=csv \
            --fields 'duration,ib-body-avg-size-bytes,ib-generation-probability,label,leios-stage-length-slots,network,node,simulator,slot,task' \
| gzip -9vc > results/cpus.csv.gz

mongoexport --host="$HOST" \
            --db="$DB" \
            --collection=ibgen \
            --type=csv \
            --fields='eb-count,eb-first,eb-last,ib,ib-body-avg-size-bytes,ib-generation-probability,label,leios-stage-length-slots,network,node,simulator,time,size' \
| gzip -9vc > results/ibgen.csv.gz

mongoexport --host="$HOST" \
            --db="$DB" \
            --collection=ebgen \
            --type=csv \
            --fields='eb,ib-body-avg-size-bytes,ib-count,ib-generation-probability,label,leios-stage-length-slots,network,node,rb-count,rb-first,rb-last,simulator,size,time' \
| gzip -9vc > results/ebgen.csv.gz

mongoexport --host="$HOST" \
            --db="$DB" \
            --collection=rbgen \
            --type=csv \
            --fields='eb-count,ib-body-avg-size-bytes,ib-generation-probability,label,leios-stage-length-slots,network,rb,simulator,time,size' \
| gzip -9vc > results/rbgen.csv.gz
