#!/usr/bin/env bash

# Poll Moog for Antithesis test results.
# Usage: wait-for-test.sh <testRunId>
# Exits 0 on success, 1 on rejection/failure/unknown.
set -euo pipefail

ID="$1"

# Wallet auth isn't needed for read-only queries
unset MOOG_WALLET_FILE

function query_run() { moog facts test-runs --test-run-id "$ID"; }

# Phase 1: wait for acceptance (fast poll)
echo "Waiting to be accepted..."
while true; do
  RESULT=$(query_run)
  echo "current status: $RESULT"
  STATUS=$(echo "$RESULT" | jq -r '.[0].value.phase')
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
  RESULT=$(query_run)
  echo "current status: $RESULT"
  STATUS=$(echo "$RESULT" | jq -r '.[0].value.phase')
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
  sleep 60
  echo "..."
done

# Final outcome check
RESULT=$(query_run)
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
