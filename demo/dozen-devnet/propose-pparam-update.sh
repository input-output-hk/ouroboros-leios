#!/usr/bin/env bash
# Propose and ratify a protocol parameter update on the devnet.
#
#   ./propose-pparam-update.sh --key-value maxEndorserBlockTxsSize=200000
#   ./propose-pparam-update.sh --cli-arg '--max-endorser-block-size 400000'
#
# Protocol parameters are no longer changed by a Shelley update-proposal signed
# with genesis keys; since Conway they are a governance action that has to be
# ratified. This script does the whole cycle: submit the ParameterChange, vote
# with every DRep, then wait for the epoch boundary that enacts it.
#
# It depends on two things being true of the genesis, both set up for exactly
# this (see config/genesis/conway-genesis.json):
#
#   * committeeMinSize is 0. The constitutional committee is empty with a
#     threshold of 0, and the ledger only reads that as "accepts" when
#     activeCommitteeSize >= committeeMinSize -- otherwise it treats an empty
#     committee as voting No and nothing can ever ratify. This is the same
#     shortcut cardano-testnet takes (ucppCommitteeMinSize = 0), and it is a
#     test-only arrangement: a real network would elect a committee.
#
#   * The three initialDReps are keys we hold, in config/drep-keys/, and each
#     delegator's stake is vote-delegated to one of them. All three voting Yes
#     is 100% of the delegated stake, which clears every DRep threshold
#     (the highest, ppGovGroup, is 0.75).
#
# The three pools vote too. Every Leios parameter is declared
# 'PPGroups 'NetworkGroup 'SecurityGroup in Dijkstra/PParams.hs, and anything in
# the security group needs SPO approval at poolVotingThresholds.ppSecurityGroup
# (0.51) on top of the DRep thresholds -- DReps alone leave it sitting in the
# queue until it expires. Their cold keys are the block producers' own, under
# tmp-devnet/bp*/keys/, so all three voting Yes is 100% of the pool stake.
set -euo pipefail

SOURCE_DIR=${SOURCE_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}
WORKING_DIR=${WORKING_DIR:-"${SOURCE_DIR}/tmp-devnet"}
SHARED_CONFIG_DIR=${SHARED_CONFIG_DIR:-"${SOURCE_DIR}/../proto-devnet/config"}
: "${CARDANO_NODE_NETWORK_ID:=164}"
# Not `:=`: the devshell exports a relative CARDANO_NODE_SOCKET_PATH pointing at
# a relay, and this script cd's, so an inherited relative path resolves to
# nothing. Only an absolute override is honoured.
case "${CARDANO_NODE_SOCKET_PATH:-}" in
  /*) ;;
  *) CARDANO_NODE_SOCKET_PATH="${WORKING_DIR}/bp1/node.socket" ;;
esac
export CARDANO_NODE_NETWORK_ID CARDANO_NODE_SOCKET_PATH

ERA=${ERA:-dijkstra}
WORK=${WORK:-"${WORKING_DIR}/pparam-update"}
UTXO_DIR="${SHARED_CONFIG_DIR}/utxo-keys/utxo1"
DREP_DIR="${SHARED_CONFIG_DIR}/drep-keys"

# Anchors are mandatory on a governance action, and `transaction build` insists
# on actually downloading one to check its hash -- unconditionally, with no
# opt-out flag, and file: URLs are rejected as an unsupported scheme. So the
# script serves the anchor itself over loopback for the duration of the run
# (see serve_anchor below). Set ANCHOR_URL to use a real document instead.
ANCHOR_URL=${ANCHOR_URL:-}
ANCHOR_PORT=${ANCHOR_PORT:-8099}

CLI_ARGS=()
usage() {
  sed -n '2,32p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
  echo
  echo "Options:"
  echo "  --key-value NAME=VALUE   a pparam by its CLI flag name, e.g. maxTxSize=32768"
  echo "  --cli-arg '--flag VALUE' pass a create-protocol-parameters-update flag verbatim"
  echo "  --show                   print the current pparams and exit"
  exit "${1:-0}"
}

# The flags this CLI actually accepts, so a wrong guess fails here with the
# alternatives rather than producing a rejected action.
cli_flags() {
  cardano-cli "${ERA}" governance action create-protocol-parameters-update --help 2>&1 |
    grep -oE '[-][-][a-z0-9-]+' | sort -u
}

# `--key-value maxTxSize=32768` becomes `--max-tx-size 32768`. Hyphenating the
# camelCase name works for most parameters but by no means all: the query
# reports `minFeeA`/`minFeeB` where the flags are --min-fee-linear and
# --min-fee-constant, and `committeeMinSize` is --min-committee-size. So the
# result is checked against the real flag list before use.
kv_to_flag() {
  local name=${1%%=*} value=${1#*=}
  local flag
  flag=$(printf '%s' "$name" | sed -E 's/([a-z0-9])([A-Z])/\1-\2/g' | tr '[:upper:]' '[:lower:]')
  if ! cli_flags | grep -qx -- "--${flag}"; then
    {
      echo "no such flag --${flag} (guessed from '${name}')."
      echo "closest flags this CLI offers:"
      cli_flags | grep -iE "$(printf '%s' "$name" | sed -E 's/([A-Z])/|\1/g' |
        tr '[:upper:]' '[:lower:]' | sed 's/^|//' | cut -c1-40)" | sed 's/^/  /' | head -8
      echo "or pass it verbatim with --cli-arg '--flag VALUE'"
    } >&2
    exit 1
  fi
  printf -- '--%s %s' "$flag" "$value"
}

while [ $# -gt 0 ]; do
  case "$1" in
    --key-value) read -r -a pair <<<"$(kv_to_flag "$2")"; CLI_ARGS+=("${pair[@]}"); shift 2 ;;
    --cli-arg) read -r -a pair <<<"$2"; CLI_ARGS+=("${pair[@]}"); shift 2 ;;
    --show) cardano-cli "${ERA}" query protocol-parameters; exit 0 ;;
    -h | --help) usage ;;
    *) echo "unknown option: $1" >&2; usage 1 ;;
  esac
done

[ ${#CLI_ARGS[@]} -gt 0 ] || { echo "nothing to change; pass --key-value or --cli-arg" >&2; usage 1; }

for f in "${UTXO_DIR}/utxo.skey" "${DREP_DIR}/drep1/drep.skey"; do
  [ -f "$f" ] || { echo "missing key: $f" >&2; exit 1; }
done
[ -S "$CARDANO_NODE_SOCKET_PATH" ] || { echo "no node socket at $CARDANO_NODE_SOCKET_PATH" >&2; exit 1; }

mkdir -p "$WORK"
cd "$WORK"

# Serve the anchor over loopback so `transaction build` can fetch and verify it.
ANCHOR_PID=""
cleanup() { [ -n "$ANCHOR_PID" ] && kill "$ANCHOR_PID" 2>/dev/null || true; }
trap cleanup EXIT

if [ -z "$ANCHOR_URL" ]; then
  mkdir -p anchor
  cat >anchor/pparam-update.json <<EOF
{
  "title": "devnet protocol parameter update",
  "changes": "${CLI_ARGS[*]}",
  "note": "Local devnet action; this anchor is served from the machine that submitted it and is not archived anywhere."
}
EOF
  python3 -m http.server "$ANCHOR_PORT" --bind 127.0.0.1 --directory anchor >/dev/null 2>&1 &
  ANCHOR_PID=$!
  ANCHOR_URL="http://127.0.0.1:${ANCHOR_PORT}/pparam-update.json"
  for _ in $(seq 40); do
    curl -fsS "$ANCHOR_URL" >/dev/null 2>&1 && break
    sleep 0.25
  done
  curl -fsS "$ANCHOR_URL" >/dev/null || { echo "anchor server did not come up on ${ANCHOR_PORT}" >&2; exit 1; }
fi
ANCHOR_HASH=${ANCHOR_HASH:-$(cardano-cli hash anchor-data --url "$ANCHOR_URL")}
echo "anchor: ${ANCHOR_URL} (${ANCHOR_HASH})"

DEPOSIT=$(cardano-cli "${ERA}" query gov-state | jq -r '.currentPParams.govActionDeposit')
EPOCH_BEFORE=$(cardano-cli "${ERA}" query tip | jq -r '.epoch')
echo "epoch ${EPOCH_BEFORE}, deposit ${DEPOSIT} lovelace"

# The deposit is returned to this address once the action is enacted or expires.
UTXO_ADDR=$(cardano-cli "${ERA}" address build --payment-verification-key-file "${UTXO_DIR}/utxo.vkey")
# Any stake address works as the return account; reuse delegator1's.
RETURN_ADDR=$(cardano-cli "${ERA}" stake-address build \
  --stake-verification-key-file "${SHARED_CONFIG_DIR}/stake-delegators/delegator1/staking.vkey")

echo "==> creating the action: ${CLI_ARGS[*]}"
# Every ParameterChange must name its predecessor, so that a chain of them can
# only be enacted in order. The very first one has none, and the flags must then
# be absent entirely -- passing them empty is a hard CLI error, not a no-op.
# Once one has enacted, omitting them is rejected with InvalidPrevGovActionId.
# prevGovActionIds is an object keyed by action type, not a list of tagged
# entries, and it lives on the next enact state rather than at the top level.
PREV=$(cardano-cli "${ERA}" query gov-state |
  jq -c '.nextRatifyState.nextEnactState.prevGovActionIds.PParamUpdate // empty')
PREV_ARGS=()
if [ -n "$PREV" ]; then
  PREV_ARGS=(
    --prev-governance-action-tx-id "$(echo "$PREV" | jq -r '.txId')"
    --prev-governance-action-index "$(echo "$PREV" | jq -r '.govActionIx')"
  )
  echo "    predecessor: $(echo "$PREV" | jq -r '.txId')#$(echo "$PREV" | jq -r '.govActionIx')"
else
  echo "    no predecessor ParameterChange yet"
fi

cardano-cli "${ERA}" governance action create-protocol-parameters-update \
  --testnet \
  --governance-action-deposit "$DEPOSIT" \
  --deposit-return-stake-address "$RETURN_ADDR" \
  --anchor-url "$ANCHOR_URL" \
  --anchor-data-hash "$ANCHOR_HASH" \
  "${PREV_ARGS[@]}" \
  "${CLI_ARGS[@]}" \
  --out-file pparam-update.action

echo "==> submitting"
cardano-cli "${ERA}" transaction build \
  --change-address "$UTXO_ADDR" \
  --tx-in "$(cardano-cli "${ERA}" query utxo --address "$UTXO_ADDR" --output-json |
      jq -r 'to_entries | max_by(.value.value.lovelace) | .key')" \
  --proposal-file pparam-update.action \
  --out-file propose.raw
cardano-cli "${ERA}" transaction sign \
  --tx-body-file propose.raw \
  --signing-key-file "${UTXO_DIR}/utxo.skey" \
  --out-file propose.signed
cardano-cli "${ERA}" transaction submit --tx-file propose.signed
ACTION_TX=$(cardano-cli "${ERA}" transaction txid --output-text --tx-file propose.signed)
echo "    action tx: ${ACTION_TX}"

# The proposal is only queryable once its transaction is in a block, and on a
# devnet under the tx-firehose that is not prompt: the proposal queues behind
# whatever is already in the mempool, which at 10 MB is minutes of backlog. Wait
# in wall-clock terms rather than a fixed iteration count.
echo "==> waiting for the proposal to appear in gov-state (up to 30 min)"
DEADLINE=$(( SECONDS + 1800 ))
ACTION_IX=""
while [ "$SECONDS" -lt "$DEADLINE" ]; do
  ACTION_IX=$(cardano-cli "${ERA}" query gov-state |
    jq -r --arg id "$ACTION_TX" \
      '[.proposals[]? | select(.actionId.txId==$id)][0].actionId.govActionIx // empty')
  [ -n "$ACTION_IX" ] && break
  sleep 10
done
# Voting with a null index produces an unreadable optparse error much later.
[ -n "$ACTION_IX" ] || {
  echo "proposal ${ACTION_TX} never reached a block; it is still in the mempool" >&2
  echo "or was dropped. The deposit is only returned once it is on chain." >&2
  exit 1
}
echo "    action index: ${ACTION_IX}"

echo "==> voting Yes with all three DReps and all three pools"
VOTE_ARGS=()
SIGN_ARGS=()
for i in 1 2 3; do
  cardano-cli "${ERA}" governance vote create \
    --yes \
    --governance-action-tx-id "$ACTION_TX" \
    --governance-action-index "$ACTION_IX" \
    --drep-verification-key-file "${DREP_DIR}/drep${i}/drep.vkey" \
    --out-file "drep${i}.vote"
  VOTE_ARGS+=(--vote-file "drep${i}.vote")
  SIGN_ARGS+=(--signing-key-file "${DREP_DIR}/drep${i}/drep.skey")

  cardano-cli "${ERA}" governance vote create \
    --yes \
    --governance-action-tx-id "$ACTION_TX" \
    --governance-action-index "$ACTION_IX" \
    --cold-verification-key-file "${WORKING_DIR}/bp${i}/keys/cold.vkey" \
    --out-file "pool${i}.vote"
  VOTE_ARGS+=(--vote-file "pool${i}.vote")
  SIGN_ARGS+=(--signing-key-file "${WORKING_DIR}/bp${i}/keys/cold.skey")
done

cardano-cli "${ERA}" transaction build \
  --change-address "$UTXO_ADDR" \
  --tx-in "$(cardano-cli "${ERA}" query utxo --address "$UTXO_ADDR" --output-json |
      jq -r 'to_entries | max_by(.value.value.lovelace) | .key')" \
  "${VOTE_ARGS[@]}" \
  --out-file vote.raw
cardano-cli "${ERA}" transaction sign \
  --tx-body-file vote.raw \
  --signing-key-file "${UTXO_DIR}/utxo.skey" \
  "${SIGN_ARGS[@]}" \
  --out-file vote.signed
cardano-cli "${ERA}" transaction submit --tx-file vote.signed
echo "    votes submitted"

# Ratification is decided at the epoch boundary and enactment follows it, so the
# change becomes visible in the pparams one boundary after the votes land.
echo "==> waiting for enactment (ratify at one epoch boundary, enact at the next)"
while :; do
  EPOCH_NOW=$(cardano-cli "${ERA}" query tip | jq -r '.epoch')
  STATE=$(cardano-cli "${ERA}" query gov-state)
  # Print the tallies: a stall here is almost always a missing voter group.
  echo "$STATE" | jq -r --arg id "$ACTION_TX" \
    '[.proposals[]? | select(.actionId.txId==$id)][0]
     | select(. != null)
     | "    epoch '"${EPOCH_NOW}"': drep=\(.dRepVotes | length) spo=\(.stakePoolVotes | length) cc=\(.committeeVotes | length)"'
  if ! echo "$STATE" | jq -e --arg id "$ACTION_TX" \
      '[.proposals[]? | select(.actionId.txId==$id)] | length > 0' >/dev/null; then
    echo "    proposal gone from the queue at epoch ${EPOCH_NOW}: enacted or expired"
    break
  fi
  RATIFIED=$(echo "$STATE" | jq -r --arg id "$ACTION_TX" \
    '[.nextRatifyState.enactedGovActions[]? | select(.actionId.txId==$id)] | length')
  [ "$RATIFIED" != "0" ] && echo "    ratified, enacting at the next boundary"
  sleep 30
done

echo "==> current values"
cardano-cli "${ERA}" query protocol-parameters
