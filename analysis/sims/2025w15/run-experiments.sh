#!/usr/bin/env bash

if [[ -z "$1" ]]
then
  J=1
else
  J=$1
fi

find runs -type f -name run.sh | sort -R | parallel --jobs=$J
