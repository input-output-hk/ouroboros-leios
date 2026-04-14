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
CONSECUTIVE_ERRORS=0
MAX_CONSECUTIVE_ERRORS=10
while true; do
  if ! RESULT=$(query_run 2>&1); then
    CONSECUTIVE_ERRORS=$((CONSECUTIVE_ERRORS + 1))
    echo "query failed (attempt $CONSECUTIVE_ERRORS/$MAX_CONSECUTIVE_ERRORS): $RESULT"
    if [ "$CONSECUTIVE_ERRORS" -ge "$MAX_CONSECUTIVE_ERRORS" ]; then
      echo "error: too many consecutive query failures in acceptance phase" >&2
      exit 1
    fi
    sleep 10
    echo "retrying..."
    continue
  fi
  echo "current status: $RESULT"
  STATUS=$(echo "$RESULT" | jq -r '.[0].value.phase') || {
    CONSECUTIVE_ERRORS=$((CONSECUTIVE_ERRORS + 1))
    echo "failed to parse status (attempt $CONSECUTIVE_ERRORS/$MAX_CONSECUTIVE_ERRORS), retrying..."
    if [ "$CONSECUTIVE_ERRORS" -ge "$MAX_CONSECUTIVE_ERRORS" ]; then
      echo "error: too many consecutive parse failures in acceptance phase" >&2
      exit 1
    fi
    sleep 10
    continue
  }
  CONSECUTIVE_ERRORS=0
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
CONSECUTIVE_ERRORS=0
MAX_CONSECUTIVE_ERRORS=5
while true; do
  if ! RESULT=$(query_run 2>&1); then
    CONSECUTIVE_ERRORS=$((CONSECUTIVE_ERRORS + 1))
    echo "query failed (attempt $CONSECUTIVE_ERRORS/$MAX_CONSECUTIVE_ERRORS): $RESULT"
    if [ "$CONSECUTIVE_ERRORS" -ge "$MAX_CONSECUTIVE_ERRORS" ]; then
      echo "error: too many consecutive query failures in completion phase" >&2
      exit 1
    fi
    sleep 300
    echo "retrying..."
    continue
  fi
  echo "current status: $RESULT"
  STATUS=$(echo "$RESULT" | jq -r '.[0].value.phase') || {
    CONSECUTIVE_ERRORS=$((CONSECUTIVE_ERRORS + 1))
    echo "failed to parse status (attempt $CONSECUTIVE_ERRORS/$MAX_CONSECUTIVE_ERRORS), retrying..."
    if [ "$CONSECUTIVE_ERRORS" -ge "$MAX_CONSECUTIVE_ERRORS" ]; then
      echo "error: too many consecutive parse failures in completion phase" >&2
      exit 1
    fi
    sleep 300
    continue
  }
  CONSECUTIVE_ERRORS=0
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
FINAL_RESULT_OK=false
OUTCOME=""
for i in 1 2 3; do
  if ! RESULT=$(query_run 2>&1); then
    echo "final query failed (attempt $i/3): $RESULT"
    sleep 10
    continue
  fi
  echo "final result: $RESULT"
  OUTCOME=$(echo "$RESULT" | jq -r '.[0].value.outcome') || {
    echo "failed to parse final outcome (attempt $i/3), retrying..."
    sleep 10
    continue
  }
  FINAL_RESULT_OK=true
  break
done

if [ "$FINAL_RESULT_OK" != true ]; then
  echo "error: failed to fetch a valid final outcome after 3 attempts" >&2
  exit 1
fi

case $OUTCOME in
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
