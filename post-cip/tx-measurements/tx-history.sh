#!/usr/bin/env bash

psql -f tx-history.sql mainnet

pigz -9fv *.tsv
