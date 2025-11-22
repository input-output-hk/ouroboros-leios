#!/usr/bin/env bash

for region in eu-central-1 us-east-2 ap-northeast-1
do
  rsync -vazc --progress --stats "$(cat $region/ip):2025-11-*.log" "$region/"
done
