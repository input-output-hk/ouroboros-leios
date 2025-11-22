#!/usr/bin/env bash

psql -f active-slots.sql mainnet

pigz -9fv active-slots.tsv
