#!/usr/bin/env bash
#
# Walk a running dozen-devnet through the cases the adaptive endorsements
# controller has to handle, for a run with VOTERS (see the README):
#
#   1. baseline         every voter online
#   2. offline          bp3 votes with its own key only, so its share of the
#                       generated voters (a third of a tenth of the stake) is
#                       offline. aliveStake should drop by that much once the
#                       last AliveWindow samples no longer hold their votes,
#                       and the cut it caused until then should recover.
#   3. restored         bp3 votes with its whole bundle again
#   4. slow third       bp3 is pinned to one core. Without bp3 there is no
#                       quorum, so the cap should shrink until bp3's votes make
#                       the deadline again.
#   5. restored         bp3 gets all cores back
#
# Each phase lasts two periods of a TPS_SQUARE=50:500:600 wave. Restarts go
# through the process-compose API, so the devnet must run with SERVER=1 (the
# default) and TC=0: a traffic-controlled node runs under sudo, which a
# restart cannot re-enter. Events are appended to
# $WORKING_DIR/adaptive-experiment.events with UTC timestamps.
set -euo pipefail

: "${WORKING_DIR:=$(pwd)/tmp-devnet}"
: "${PHASE:=2400}"
EVENTS="$WORKING_DIR/adaptive-experiment.events"
KEYS="$WORKING_DIR/bp3/keys"

event() {
  echo "$(date -u +%FT%TZ) $*" | tee -a "$EVENTS"
}

# The cardano-node process running in bp3's directory.
bp3_pid() {
  for p in $(pgrep -x cardano-node); do
    if [ "$(readlink "/proc/$p/cwd")" = "$WORKING_DIR/bp3" ]; then
      echo "$p"
      return
    fi
  done
  echo "no cardano-node running in $WORKING_DIR/bp3" >&2
  exit 1
}

set_bundle() {
  chmod u+w "$KEYS/bls.skey"
  cp "$1" "$KEYS/bls.skey"
  chmod 400 "$KEYS/bls.skey"
  process-compose process restart bp3
}

if [ "$(jq 'if type == "array" then length else 0 end' "$KEYS/bls.skey" 2>/dev/null || echo 0)" -lt 2 ]; then
  echo "bp3 has no voter bundle; start the devnet with VOTERS, e.g. VOTERS=500" >&2
  exit 1
fi
[ -f "$KEYS/bls.skey.full" ] || cp "$KEYS/bls.skey" "$KEYS/bls.skey.full"
jq '[.[0]]' "$KEYS/bls.skey.full" >"$KEYS/bls.skey.own"

echo "Waiting for the first votes ..."
until grep -qF 'LeiosVoted\"' "$WORKING_DIR/bp1/node.log" 2>/dev/null; do sleep 10; done

event "baseline"
sleep "$PHASE"

event "offline: bp3 votes with its own key only"
set_bundle "$KEYS/bls.skey.own"
sleep "$PHASE"

event "restored: bp3 votes with its whole bundle"
set_bundle "$KEYS/bls.skey.full"
sleep $((PHASE / 2))

event "slow third: bp3 pinned to one core"
taskset -a -p -c 0 "$(bp3_pid)" >/dev/null
sleep "$PHASE"

event "restored: bp3 on all cores"
taskset -a -p -c "0-$(($(nproc) - 1))" "$(bp3_pid)" >/dev/null
sleep $((PHASE / 2))

event "done"
