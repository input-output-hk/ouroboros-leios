#!/usr/bin/env bash

# Poll Moog for Antithesis test results.
# Usage: wait-for-test.sh <testRunId>
# Exits 0 on success, 1 on rejection/failure/unknown.
set -euo pipefail

if [ "$#" -ne 1 ]; then
  echo "error: expected exactly 1 argument: <testRunId>" >&2
  echo "usage: wait-for-test.sh <testRunId>" >&2
  exit 1
fi
ID="$1"

# Wallet auth isn't needed for read-only queries
unset MOOG_WALLET_FILE

function query_run() { moog facts test-runs --test-run-id "$ID"; }

# Phase 1: wait for acceptance (fast poll)
echo "Waiting to be accepted..."
while true; do
  if ! RESULT=$(query_run 2>&1); then
    echo "query failed (transient?): $RESULT"
    sleep 10
    echo "retrying..."
    continue
  fi
  echo "current status: $RESULT"
  STATUS=$(echo "$RESULT" | jq -r '.[0].value.phase') || {
    echo "failed to parse status, retrying..."
    sleep 10
    continue
  }
  case $STATUS in
    accepted)
      echo "accepted"
      break
      ;;
    rejected)
      echo "rejected"
      exit 1
      ;;
    finished)
      echo "already finished"
      break
      ;;
    pending)
      ;;
    *)
      echo "unknown status: $STATUS"
      ;;
  esac
  sleep 10
  echo "..."
done

# Phase 2: wait for completion (slow poll)
echo "Waiting to finish..."
while true; do
  if ! RESULT=$(query_run 2>&1); then
    echo "query failed (transient?): $RESULT"
    sleep 300
    echo "retrying..."
    continue
  fi
  echo "current status: $RESULT"
  STATUS=$(echo "$RESULT" | jq -r '.[0].value.phase') || {
    echo "failed to parse status, retrying..."
    sleep 300
    continue
  }
  case $STATUS in
    finished)
      echo "finished"
      break
      ;;
    accepted)
      ;;
    *)
      echo "unknown status: $STATUS"
      ;;
  esac
  sleep 300
  echo "..."
done

# Final outcome check (retry on transient errors)
for i in 1 2 3; do
  if RESULT=$(query_run 2>&1); then
    break
  fi
  echo "final query failed (attempt $i/3): $RESULT"
  sleep 10
done
echo "final result: $RESULT"
case $(echo "$RESULT" | jq -r '.[0].value.outcome') in
  success)
    exit 0
    ;;
  failure)
    echo "failed"
    exit 1
    ;;
  *)
    echo "unknown outcome"
    exit 1
    ;;
esac
