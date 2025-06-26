#!/usr/bin/env bash

sed -e 's/Label/Variant,Sharding/' \
    -e 's/full-/full,/' \
    -e 's/noib-/full-without-ibs,/' \
    -e 's/txrf-/full-with-tx-references,/' \
    -e 's/shard/sharded/' \
    -e 's/simpl/unsharded/' \
    -e 's/overc/overcollateralized/' \
    -i vars/*/case.csv
