#!/usr/bin/env bash

DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

./queries/haskell/run-queries.sh

./queries/rust/run-queries.sh
