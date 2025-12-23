#!/usr/bin/env bash

psql -f block-history.sql mainnet

pigz -9fv block-stats.tsv

