#!/usr/bin/env bash
#
# Wrapper script to set defaults, check requirements and run the dozen-devnet
# demo using process-compose.
#
# Topology: three block producers, each with three private relays, and the nine
# relays fully meshed among themselves. Twelve nodes total, hence the name. A
# block producer only ever talks to its own three relays, so every tx and every
# block between two pools crosses at least two relay hops — the degree profile
# of a real SPO deployment, unlike the all-to-all proto-devnet.
#
#   bp1 ── relay11 ─┐
#      ├─ relay12 ──┤
#      └─ relay13 ──┤
#   bp2 ── relay21 ─┤
#      ├─ relay22 ──┼── full mesh across all nine relays
#      └─ relay23 ──┤
#   bp3 ── relay31 ─┤
#      ├─ relay32 ──┤
#      └─ relay33 ──┘
set -eo pipefail

# Set defaults for all environment variables
# These can be overridden by exporting them before running this script
set -a
: "${WORKING_DIR:=$(pwd)/tmp-devnet}"
: "${SOURCE_DIR:=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}"
# Genesis, pool keys, delegator keys, Alloy modules and dashboards are shared
# with the proto-devnet demo — same network magic, same pools, so duplicating
# them would only invite drift. Only config.yaml, topology.template.json and
# alloy.template are our own (see config/).
: "${SHARED_CONFIG_DIR:="${SOURCE_DIR}/../proto-devnet/config"}"
# Reuse an existing WORKING_DIR instead of wiping it, keeping every node's
# databases so the cluster continues the chain it was on. Genesis is left exactly
# as it was -- moving systemStart would invalidate all persisted data -- while
# configs, topology, compose files and observability are regenerated, so config
# edits still take effect. Best effort: see the preflight warnings below.
: "${RESUME:=0}"
# Add VOTERS extra committee members: that many freshly generated key sets land
# in $WORKING_DIR/voters and their pools go into the shelley genesis holding
# 10% of the delegated stake in equal parts (the producers keep 90%), so all
# of them hold weighted committee seats from epoch 0. Their
# BLS signing keys are partitioned round-robin into three bundles, and each
# block producer votes with its own key plus its share — with VOTERS=100 that is
# 100 extra votes per EB across bp1/bp2/bp3. Exercises the multi-key
# --shelley-bls-key; needs a node built with key bundle support. Voter keys are
# part of the genesis, so like it they are preserved on RESUME=1 and the value
# of VOTERS must not change across a resume.
: "${VOTERS:=0}"
# All nodes listen on the same ports; they are told apart by IP address. That
# keeps the node count out of the port bookkeeping entirely.
: "${PORT:=3001}"
: "${METRICS_PORT:=12798}"
# Base firehose submission rate (TxFirehose1); override with e.g. TPS=1000
: "${TPS:=500}"
# Outputs per generated tx, i.e. a lever on transaction *size*. The EB body holds
# one (hash, size) pair per tx — 36 B — regardless of how big the tx is, so
# maxTxsPerEb and therefore tx/s are size-independent, and byte throughput scales
# linearly with size until maxEBClosureSize (12 MB) binds instead. That crossover
# is at 12 MB / 13,888 = 864 B per tx, close to the mainnet median. Above it byte
# throughput is flat and only tx/s falls, so overshooting is cheap and
# undershooting costs linearly.
#
# 1 output is 232 B as the mempool accounts it (228 B on the wire); each extra
# output adds roughly 35-40 B.
#
# The practical ceiling is funding: each output needs its own min-ada, and the fee
# is fixed, so the input selection has to cover fee + OUTPUTS * min-ada. 5 outputs
# gives ~648 B transactions.
: "${OUTPUTS:=1}"
# Which tx-firehose to run. Defaults to whatever is on PATH, which is normally the
# nix-store build; point it at a local cabal build to iterate on the generator
# without rebuilding the devnet:
#   TX_FIREHOSE=.../dist-newstyle/.../tx-firehose ./run.sh
# PATH is resolved by the process at exec time, so an already-running
# process-compose keeps using whatever it started with — hence the explicit knob.
: "${TX_FIREHOSE:=tx-firehose}"
# Colours the three generators tag their transactions with, so a mempool
# observer can tell whose load it is holding. Explicit and well separated rather
# than --color auto: auto derives a hue from the key, which is uniform but can
# land two generators close enough to be hard to tell apart by eye.
: "${COLOR1:=ff0000}"
: "${COLOR2:=00ff00}"
: "${COLOR3:=0000ff}"
# Mempool observers are not devnet processes: process-compose cannot tile, so
# twelve panes would only be viewable one at a time. See ./mempool-panes.sh.
# Traffic control (on by default, disable with TC=0)
: "${TC:=1}"
if [ "$TC" = "1" ]; then
  # RATE is the rate limit on each node's single uplink, i.e. the whole node's
  # send capacity shared across all of its peers — not a per-peer allowance.
  # DELAY is applied once per direction (on the receiving side), so it stays a
  # one-way delay and the round trip between any two nodes is 2 x DELAY.
  #
  # 10ms one way = 20ms RTT, a typical intra-continent link. Deliberately not
  # the intercontinental 100ms/200ms: with a uniform delay that figure would
  # also apply to each block producer's link to its own relays, which in
  # reality are co-located. Raise it once the happy-path throughput picture is
  # established.
  : "${RATE:=50Mbps}"
  : "${DELAY:=10ms}"
  # A different subnet than proto-devnet's 172.28.0.0/24 so both devnets can be
  # up at the same time (turn XRAY off on one of them, the observability stack
  # binds fixed ports).
  : "${IP_HOST:=172.29.0.1}"
  : "${IP_PREFIX:=172.29.0.}"
else
  # Use distinct loopback aliases so each node's --host-addr (which
  # ouroboros-network also uses as the source IP for outbound sockets) does
  # not collide with another node's listening 4-tuple. With all nodes sharing
  # 127.0.0.1, outbound connect() can return EADDRNOTAVAIL because the kernel
  # cannot assign (127.0.0.1:listener_port, 127.0.0.1:peer_port) for the new
  # socket while the listener still owns that port. Splitting across the 127/8
  # range avoids the collision entirely. 127.3/16 leaves proto-devnet's
  # 127.2/16 alone.
  : "${IP_PREFIX:=127.3.0.}"
fi
# X-ray observability (on by default, disable with XRAY=0)
: "${XRAY:=1}"
: "${XRAY_SOURCE_DIR:="${SOURCE_DIR}/../extras/x-ray"}"
# Process-compose HTTP API, so the devnet can be driven from another shell
# without touching the TUI:
#   process-compose process list
#   process-compose process start TxFirehose2
#   process-compose process restart relay11
# Bound to loopback deliberately — it can start and stop processes. Set
# SERVER=0 for the old --no-server behaviour.
: "${SERVER:=1}"
: "${SERVER_ADDRESS:=127.0.0.1}"
: "${SERVER_PORT:=8080}"
# Extra RTS options per node, appended after the binary's baked-in
# "-T -I0 -A16m -qg1 -qb1 -N2". Empty keeps the built-in behaviour. Twelve
# nodes at -N2 is 24 capabilities: oversubscribed on 16 cores, two thirds
# idle on 64. Try NODE_RTS="-N4" on a big host.
: "${NODE_RTS:=}"
set +a

# Network namespace prefix, distinct from proto-devnet's so the two do not
# delete each other's namespaces on init.
NS_PREFIX="dozen-devnet"

BPS=(bp1 bp2 bp3)
RELAYS=(relay11 relay12 relay13 relay21 relay22 relay23 relay31 relay32 relay33)
NODES=("${BPS[@]}" "${RELAYS[@]}")

# Group-aligned addressing that reads straight off the topology: producer G
# sits at IP_PREFIX(10 * G) and its relays at IP_PREFIX(10 * G + R):
#
#   bp1 .10   relay11 .11   relay12 .12   relay13 .13
#   bp2 .20   relay21 .21   relay22 .22   relay23 .23
#   bp3 .30   relay31 .31   relay32 .32   relay33 .33
#
# The visualiser's HOST_PORT_TO_NODE table
# (ui/src/components/Sim/hooks/lokiParsers.ts) mirrors this scheme and has to
# change with it. Addresses land in every node's config and topology.json, so
# a change takes a re-render of the working dir (RESUME=1 ./run.sh or fresh).
node_ip() {
  local name="$1" gr
  case "$name" in
  bp[0-9])
    echo "${IP_PREFIX}$((10 * ${name#bp}))"
    return 0
    ;;
  relay[0-9][0-9])
    gr="${name#relay}"
    echo "${IP_PREFIX}$((10 * ${gr:0:1} + ${gr:1:1}))"
    return 0
    ;;
  esac
  echo "unknown node: $name" >&2
  return 1
}

# A relay is named relay<bp><n>, so relay11 belongs to bp1. Block producers peer
# with their own relays only; relays peer with their block producer and with
# every other relay.
node_peers() {
  local name="$1" r
  case "$name" in
  bp*)
    for r in "${RELAYS[@]}"; do
      if [ "${r:5:1}" = "${name#bp}" ]; then
        echo "$r"
      fi
    done
    ;;
  relay*)
    echo "bp${name:5:1}"
    for r in "${RELAYS[@]}"; do
      if [ "$r" != "$name" ]; then
        echo "$r"
      fi
    done
    ;;
  *)
    echo "unknown node: $name" >&2
    return 1
    ;;
  esac
}

# Emit the process-compose fragment defining all node processes. Generated
# rather than checked in because the node list is the topology's single source
# of truth; $1 selects the traffic-controlled variant.
gen_nodes_compose() {
  local tc="$1" out="$2" name ip
  {
    echo '# Generated by run.sh — do not edit, regenerate instead.'
    echo 'version: "0.5"'
    echo
    echo 'processes:'
    for name in "${NODES[@]}"; do
      ip=$(node_ip "$name")
      echo "  ${name}:"
      if [ "$tc" = "1" ]; then
        echo "    is_elevated: true"
      fi
      echo "    command: |"
      echo "      NODE_DIR=\"${WORKING_DIR}/${name}\" \\"
      echo "      IP=\"${ip}\" \\"
      echo "      PORT=\"${PORT}\" \\"
      # Passed inline rather than inherited: elevated processes go through
      # sudo, which drops the environment.
      echo "      NODE_RTS=\"${NODE_RTS}\" \\"
      echo "      CARDANO_NODE=\"${CARDANO_NODE_BIN}\" \\"
      if [ "$tc" = "1" ]; then
        echo "      ${IP_BIN} netns exec ${NS_PREFIX}:${name} bash \"${SOURCE_DIR}/run-node.sh\""
      else
        echo "      bash \"${SOURCE_DIR}/run-node.sh\""
      fi
      echo "    log_location: \"${WORKING_DIR}/${name}/node.log\""
      # The host reaches every node through the bridge, so the probe works in
      # both the namespaced and the loopback case.
      #
      # The probe exists only so the firehoses can gate on
      # 'condition: process_healthy'; it must never be what stops a node. A
      # node does not listen until it has replayed, and at 60 failures the
      # window was 5 + 60*2 = 125s -- which killed all twelve at 123s the
      # first time a resumed cluster replayed a ten-hour chain, a ~15 minute
      # job. The threshold is now three hours: long enough that a node
      # replaying is never preempted, at the cost of a genuinely dead node
      # leaving its firehose waiting instead of failing it.
      echo "    readiness_probe:"
      echo "      exec:"
      echo "        command: \"bash -c ': </dev/tcp/${ip}/${PORT}'\""
      echo "      initial_delay_seconds: 5"
      echo "      period_seconds: 2"
      echo "      failure_threshold: 5400"
      if [ "$tc" = "1" ]; then
        echo "    depends_on:"
        echo "      InitNamespaces:"
        echo "        condition: process_completed_successfully"
      fi
    done

  } >"$out"
}

# Check for required commands
REQUIRED_COMMANDS=(
  "process-compose"
  "sqlite3"
  "jq"
  "yq"
  "envsubst"
  "cardano-node"
  "cardano-cli"
  "tx-firehose"
)
if [ "$TC" = "1" ]; then
  REQUIRED_COMMANDS+=("ip" "tc")
fi

MISSING_COMMANDS=()
for cmd in "${REQUIRED_COMMANDS[@]}"; do
  if ! command -v "$cmd" &>/dev/null; then
    MISSING_COMMANDS+=("$cmd")
  fi
done

if [ ${#MISSING_COMMANDS[@]} -gt 0 ]; then
  echo "Error: The following required commands are not available:"
  for cmd in "${MISSING_COMMANDS[@]}"; do
    echo "  - $cmd"
  done
  echo ""
  echo "Please install the missing commands or use nix:"
  echo "  nix run github:input-output-hk/ouroboros-leios#demo-dozen-devnet"
  exit 1
fi

if [ ! -d "$SHARED_CONFIG_DIR/genesis" ]; then
  echo "Error: no genesis files at $SHARED_CONFIG_DIR/genesis"
  echo "Set SHARED_CONFIG_DIR to a proto-devnet config directory."
  exit 1
fi

# Resolve ip/tc to absolute paths. The elevated processes run through sudo,
# which drops the environment, so a PATH-only iproute2 — the usual case when it
# comes from a devshell rather than the system profile — would leave both
# InitNamespaces and every `ip netns exec` failing with "command not found".
IP_BIN=""
TOOL_PATH=""
if [ "$TC" = "1" ]; then
  IP_BIN=$(command -v ip)
  TOOL_PATH=$(dirname "$IP_BIN")
  tc_dir=$(dirname "$(command -v tc)")
  if [ "$tc_dir" != "$TOOL_PATH" ]; then
    TOOL_PATH="${TOOL_PATH}:${tc_dir}"
  fi
fi
export TOOL_PATH

# Same sudo-drops-the-environment problem as ip/tc above, but for cardano-node
# itself: run-node.sh invokes it by bare name, which only resolves under a
# PATH-only devshell build (e.g. the dependency-localisation override in
# nix/haskell.nix) when the process is not elevated. Resolve it here, while
# still running in the caller's own (non-elevated) shell, and pass the
# absolute path down inline like NODE_DIR/IP/PORT/NODE_RTS.
CARDANO_NODE_BIN=$(command -v cardano-node)

# Check if WORKING_DIR already exists
if [ -d "$WORKING_DIR" ]; then
  if [ "$RESUME" = "1" ]; then
    echo "RESUME=1: keeping $WORKING_DIR"
  else
    # Never destructive from a prompt: a mistyped answer would throw away a
    # run that may have taken hours to reach the state being investigated.
    echo "Working directory already exists: $WORKING_DIR"
    read -r -rp "Resume from persisted data? (Y/n): " response
    if [[ "$response" =~ ^[Yy]$ || -z "$response" ]]; then
      RESUME=1
    else
      echo "Aborting. To start fresh, remove the working directory first:"
      echo "  chmod a+w -R \"$WORKING_DIR\" && rm -rf \"$WORKING_DIR\""
      exit 0
    fi
  fi
elif [ "$RESUME" = "1" ]; then
  echo "RESUME=1 but $WORKING_DIR does not exist; initializing from scratch."
  RESUME=0
fi

if [ "$RESUME" = "1" ]; then
  # Genesis is the anchor: every persisted chain is only valid against the
  # systemStart it was produced under, so this is the one thing a resume must
  # not touch.
  if [ ! -f "$WORKING_DIR/genesis/shelley-genesis.json" ]; then
    echo "Error: RESUME=1 but $WORKING_DIR/genesis is missing -- cannot resume." >&2
    exit 1
  fi
  resume_start=$(jq -r '.systemStart' "$WORKING_DIR/genesis/shelley-genesis.json")
  echo "Resuming dozen-devnet in $WORKING_DIR (systemStart $resume_start, preserved)"
  # The Leios database has no schema migration, so a node built after a schema
  # change cannot open one written before it. Cheap detection: the CREATE
  # statements are stored as text in the file.
  for db in "$WORKING_DIR"/*/db/leios.db; do
    [ -e "$db" ] || continue
    if ! grep -qa "ebsMissingTxs" "$db"; then
      echo "Warning: $db predates the ebsMissingTxs schema; this node will" >&2
      echo "         fail to start. Delete the node's db/ to let it resync." >&2
    fi
  done
  # Chain state is far enough along that the firehose's own view of the UTxO may
  # no longer match; if it wedges, that is the first thing to suspect.
  echo "Note: resume is best effort -- tx-firehose state is not checkpointed."
else
  echo "Initializing dozen-devnet in $WORKING_DIR"
fi

# Create working directory
mkdir -p "$WORKING_DIR"

CONFIG_DIR="${SOURCE_DIR}/config"

# Copy genesis files and set start time. Skipped on resume: a new systemStart
# would orphan every persisted chain.
if [ "$RESUME" != "1" ]; then
  cp -r "$SHARED_CONFIG_DIR/genesis" "$WORKING_DIR/genesis"
  chmod u+w -R "${WORKING_DIR}/genesis"

  startTimeEpoch=$(date +%s)
  startTimeIso=$(date -u -d "@$startTimeEpoch" +"%Y-%m-%dT%H:%M:%SZ")

  jq --argjson time "$startTimeEpoch" '.startTime = $time' \
    "$SHARED_CONFIG_DIR/genesis/byron-genesis.json" >"$WORKING_DIR/genesis/byron-genesis.json"

  jq --arg time "$startTimeIso" '.systemStart = $time' \
    "$SHARED_CONFIG_DIR/genesis/shelley-genesis.json" >"$WORKING_DIR/genesis/shelley-genesis.json"

  # Generate the VOTERS extra committee members and put their pools into the
  # shelley genesis. Each voter is a complete key set; the pool never forges
  # (nobody runs its VRF/KES), it exists to hold a committee seat whose BLS
  # key one of the block producers votes with (see the bundle assembly below).
  if [ "$VOTERS" -gt 0 ]; then
    VOTERS_DIR="$WORKING_DIR/voters"
    rm -rf "$VOTERS_DIR"
    mkdir -p "$VOTERS_DIR"
    # 90/10 stake split: the producers keep what they have, and the voters
    # together get one ninth of it — 10% of the resulting total — in equal
    # parts, so committee seat weights are real and the vote tally climbs in
    # ~(10/VOTERS)% steps instead of thirds (smoother CDFs on the voting
    # dashboard). Certification stays with bp1/bp2/bp3 (90% > the 0.75
    # quorum), but their pools never forge, so ~10% of leader slots go empty.
    # Delegated stake = the initialFunds whose address (00 | payment | stake)
    # carries a stake key hash that staking.stake delegates.
    delegatedStake=$(jq '
      .staking.stake as $delegs
      | [.initialFunds | to_entries[] | select($delegs[.key[58:114]]) | .value]
      | add' "$WORKING_DIR/genesis/shelley-genesis.json")
    VOTER_STAKE=$((delegatedStake / 9 / VOTERS))
    MAGIC=$(jq .networkMagic "$WORKING_DIR/genesis/shelley-genesis.json")
    echo "Generating $VOTERS voter key sets in $VOTERS_DIR"
    for i in $(seq 1 "$VOTERS"); do
      d="$VOTERS_DIR/voter$i"
      mkdir -p "$d"
      cardano-cli address key-gen \
        --verification-key-file "$d/payment.vkey" --signing-key-file "$d/payment.skey"
      cardano-cli dijkstra stake-address key-gen \
        --verification-key-file "$d/stake.vkey" --signing-key-file "$d/stake.skey"
      cardano-cli node key-gen \
        --cold-verification-key-file "$d/cold.vkey" --cold-signing-key-file "$d/cold.skey" \
        --operational-certificate-issue-counter-file "$d/opcert.counter"
      cardano-cli node key-gen-VRF \
        --verification-key-file "$d/vrf.vkey" --signing-key-file "$d/vrf.skey"
      cardano-cli dijkstra node key-gen-BLS \
        --verification-key-file "$d/bls.vkey" --signing-key-file "$d/bls.skey"
      # The BLS proof of possession exists only inside a registration
      # certificate, so build one offline and fish it out: the PoP is the only
      # 48-byte string in there (0x5830 = CBOR bytes(48)).
      cardano-cli dijkstra stake-pool registration-certificate \
        --cold-verification-key-file "$d/cold.vkey" \
        --vrf-verification-key-file "$d/vrf.vkey" \
        --bls-signing-key-file "$d/bls.skey" \
        --pool-pledge 0 --pool-cost 0 --pool-margin 0 \
        --pool-reward-account-verification-key-file "$d/stake.vkey" \
        --pool-owner-stake-verification-key-file "$d/stake.vkey" \
        --pool-relay-ipv4 127.0.0.1 --pool-relay-port 3001 \
        --testnet-magic "$MAGIC" \
        --out-file "$d/pool-reg.cert"
      # The PoP is the 48-byte string right after the pubkey in the cert
      # (5860 <pubkey> 5830 <pop>). Anchor on the known pubkey: a bare
      # `5830[0-9a-f]{96}` also matches byte sequences inside other fields
      # (about once every ~200 certs, at arbitrary hex offsets).
      blsPub=$(jq -r .cborHex "$d/bls.vkey")
      blsPub=${blsPub#5860}
      pop=$(jq -r .cborHex "$d/pool-reg.cert" | grep -oE "5860${blsPub}5830[0-9a-f]{96}" || true)
      if [ -z "$pop" ]; then
        echo "Error: did not find the BLS pubkey followed by its PoP in $d/pool-reg.cert" >&2
        exit 1
      fi
      pop=${pop: -96}
      jq -n \
        --arg poolId "$(cardano-cli dijkstra stake-pool id --cold-verification-key-file "$d/cold.vkey" --output-hex)" \
        --arg vrf "$(cardano-cli node key-hash-VRF --verification-key-file "$d/vrf.vkey")" \
        --arg stakeHash "$(cardano-cli dijkstra stake-address key-hash --stake-verification-key-file "$d/stake.vkey")" \
        --arg payHash "$(cardano-cli address key-hash --payment-verification-key-file "$d/payment.vkey")" \
        --arg blsPubKey "$blsPub" \
        --arg blsPossessionProof "$pop" \
        '$ARGS.named' >"$d/voter.json"
    done
    jq -s '.' "$VOTERS_DIR"/voter*/voter.json >"$VOTERS_DIR/voters.json"

    # One pool, one delegation and one funded base address (00 | payment key
    # hash | stake key hash, testnet) per voter — the stake behind the seat.
    jq --slurpfile voters "$VOTERS_DIR/voters.json" --argjson stake "$VOTER_STAKE" '
      reduce $voters[0][] as $v (.;
        .staking.pools[$v.poolId] =
          { cost: 0, margin: 0, metadata: null, owners: [], pledge: 0
          , publicKey: $v.poolId, relays: []
          , rewardAccount: {credential: {keyHash: $v.stakeHash}, network: "Testnet"}
          , vrf: $v.vrf
          , blsKey: {blsPubKey: $v.blsPubKey, blsPossessionProof: $v.blsPossessionProof}
          }
        | .staking.stake[$v.stakeHash] = $v.poolId
        | .initialFunds["00" + $v.payHash + $v.stakeHash] = $stake)
      # The stock initialFunds already add up to exactly maxLovelaceSupply, so
      # grow the supply by what the voters bring or the reserves go negative.
      | .maxLovelaceSupply += $stake * ($voters[0] | length)
    ' "$WORKING_DIR/genesis/shelley-genesis.json" >"$WORKING_DIR/genesis/shelley-genesis.json.tmp"
    mv "$WORKING_DIR/genesis/shelley-genesis.json.tmp" "$WORKING_DIR/genesis/shelley-genesis.json"
  fi
fi

# Set up each node
for NODE_NAME in "${NODES[@]}"; do
  NODE_DIR="$WORKING_DIR/$NODE_NAME"
  NODE_IP=$(node_ip "$NODE_NAME")

  echo "Setting up $NODE_NAME ($NODE_IP) in $NODE_DIR"
  mkdir -p "$NODE_DIR"

  # Copy config files. Prometheus binds the node's own address rather than
  # 0.0.0.0 so a single metrics port works for all twelve.
  cat "$CONFIG_DIR/config.yaml" |
    yq ".TraceOptionNodeName = \"$NODE_NAME\"" |
    yq ".TraceOptions.\"\".backends[1] = \"PrometheusSimple $NODE_IP $METRICS_PORT\"" \
      >"$NODE_DIR/config.yaml"

  # These localRoots are the whole enforcement of the topology: config.yaml sets
  # PeerSharing: false with no public/ledger peers, so a node only ever connects
  # to the peers listed here. All twelve nodes share one L2 segment, so
  # re-enabling PeerSharing would let the structure collapse into a mesh.
  accessPoints=$(node_peers "$NODE_NAME" | while read -r peer; do
    echo "{ \"port\": ${PORT}, \"address\": \"$(node_ip "$peer")\" }"
  done | jq -s '.')
  # hotValency has to cover every listed peer: the outbound governor promotes
  # only hotValency many peers from a group to hot, and tx-submission runs on
  # hot peers only. Leaving it at 2 would silently cap a relay at two upstream
  # tx sources no matter how many peers it knows.
  valency=$(echo "$accessPoints" | jq 'length')
  jq \
    --argjson accessPoints "$accessPoints" \
    --argjson valency "$valency" \
    '.localRoots[0].accessPoints = $accessPoints
     | .localRoots[0].hotValency = $valency
     | .localRoots[0].warmValency = $valency' \
    "$CONFIG_DIR/topology.template.json" >"$NODE_DIR/topology.json"

  # Symlink genesis files (shared, read-only)
  for era in byron shelley alonzo conway dijkstra; do
    ln -sf "../genesis/${era}-genesis.json" "$NODE_DIR/"
  done

  # Only block producers forge, so only they get pool keys. run-node.sh keys off
  # the presence of keys/ to decide whether to pass the forging arguments.
  case "$NODE_NAME" in
  bp*)
    # Not re-copied on resume: 'cp -r' onto an existing keys/ would nest it,
    # and the keys are identical anyway.
    if [ ! -d "$NODE_DIR/keys" ]; then
      cp -r "$SHARED_CONFIG_DIR/pools-keys/pool${NODE_NAME#bp}" "$NODE_DIR/keys"
      chmod 400 "$NODE_DIR/keys"/*.skey
    fi
    # The BLS key is settled after the copy (and again on resume). The
    # WORKING DIR, not the environment, says whether this devnet has voters:
    # their pools are baked into the genesis, so the bundles have to match it
    # even when a resume does not repeat VOTERS on the command line. With
    # voters, bp N votes with its own key plus every third voter's (bp1 gets
    # voters 1,4,7,…) — the bundle is a JSON array of key envelopes, which
    # --shelley-bls-key accepts in place of a single one.
    actualVoters=$({ find "$WORKING_DIR/voters" -maxdepth 1 -name 'voter[0-9]*' -type d 2>/dev/null || true; } | wc -l)
    if [ "$VOTERS" -gt 0 ] && [ "$VOTERS" != "$actualVoters" ]; then
      echo "Warning: VOTERS=$VOTERS but $WORKING_DIR/voters holds $actualVoters" >&2
      echo "         voter key sets; the genesis is fixed, using the $actualVoters." >&2
    fi
    rm -f "$NODE_DIR/keys/bls.skey"
    if [ "$actualVoters" -gt 0 ]; then
      n="${NODE_NAME#bp}"
      voter_keys=()
      for i in $(seq "$n" 3 "$actualVoters"); do
        voter_keys+=("$WORKING_DIR/voters/voter$i/bls.skey")
      done
      jq -s '.' "$SHARED_CONFIG_DIR/pools-keys/pool${n}/bls.skey" "${voter_keys[@]}" \
        >"$NODE_DIR/keys/bls.skey"
    else
      cp "$SHARED_CONFIG_DIR/pools-keys/pool${NODE_NAME#bp}/bls.skey" "$NODE_DIR/keys/bls.skey"
    fi
    chmod 400 "$NODE_DIR/keys/bls.skey"
    ;;
  esac
done

# tx-firehose reads its delegator payment/staking .skey files directly from
# $SHARED_CONFIG_DIR/stake-delegators/delegatorN/ (see process-compose.yaml).
# No copy or config-file generation needed.

# Node processes, and the name=ip table the namespace setup runs off.
NODES_COMPOSE="${WORKING_DIR}/process-compose-nodes.yaml"
gen_nodes_compose "$TC" "$NODES_COMPOSE"

NODE_SPEC=""
for NODE_NAME in "${NODES[@]}"; do
  NODE_SPEC="${NODE_SPEC}${NODE_SPEC:+ }${NODE_NAME}=$(node_ip "$NODE_NAME")"
done
export NODE_SPEC NS_PREFIX

# Prometheus scrape targets for every node, substituted into alloy.template.
# Tabs to match the surrounding Alloy river formatting.
SCRAPE_TARGETS=$(for NODE_NAME in "${NODES[@]}"; do
  printf '\t\t{\n'
  printf '\t\t\t"__address__" = "%s:%s",\n' "$(node_ip "$NODE_NAME")" "$METRICS_PORT"
  printf '\t\t\t"job"         = "integrations/cardano-node",\n'
  printf '\t\t\t"instance"    = "%s",\n' "$NODE_NAME"
  printf '\t\t\t"environment" = "leios",\n'
  printf '\t\t\t"group"       = "dozen-devnet",\n'
  printf '\t\t},\n'
done)
export SCRAPE_TARGETS

# Configure alloy for x-ray observability (named config.alloy to avoid conflict with alloy/ storage dir)
export ALLOY_CONFIG="${WORKING_DIR}/config.alloy"
envsubst <"${CONFIG_DIR}/alloy.template" >"${ALLOY_CONFIG}"

# Shared per-service Alloy enrichment modules that config.alloy imports via
# import.file. They carry no envsubst vars, so a plain copy suffices.
mkdir -p "${WORKING_DIR}/alloy-modules"
cp "${SHARED_CONFIG_DIR}/alloy-modules/"*.alloy "${WORKING_DIR}/alloy-modules/"

# Record which binaries this run actually resolved, because nothing else can
# tell you afterwards. `cardano-node --version` reports cardano-node's own git
# rev, and cabal.project points ../ouroboros-consensus at a local package — so a
# nix-store binary and a cabal build of the same commit report byte-identical
# version strings while differing in every dependency. The path and hash are the
# only durable evidence. Archive this next to the logs.
{
  echo "# dozen-devnet run provenance — $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo
  for tool in cardano-node cardano-cli tx-firehose; do
    path=$(command -v "$tool")
    echo "${tool}:"
    echo "  path:    ${path}"
    echo "  version: $("$tool" --version 2>/dev/null | head -1)"
    echo "  sha256:  $(sha256sum "$path" 2>/dev/null | cut -d' ' -f1)"
  done
  echo
  echo "settings:"
  for v in TPS OUTPUTS RATE DELAY TC XRAY SERVER NODE_RTS RESUME; do
    echo "  ${v}=${!v}"
  done
  echo "  nodes=${#NODES[@]}"
} >"${WORKING_DIR}/provenance.txt"

echo "Starting dozen-devnet ..."
echo "  Topology: 3 block producers x 3 relays, relays fully meshed (${#NODES[@]} nodes)"
# Traffic control integration
TC_COMPOSE=()
if [ "$TC" = "1" ]; then
  TC_COMPOSE=(-f "${SOURCE_DIR}/process-compose-tc.yaml")
  echo "  Traffic control: enabled TC=${TC} (RATE=${RATE} per node uplink, DELAY=${DELAY} one way)"
else
  echo "  Traffic control: disabled TC=${TC} (nodes on loopback)"
fi
# X-ray observability integration
XRAY_COMPOSE=()
if [ "$XRAY" = "1" ]; then
  set -a
  # shellcheck disable=SC2034
  DEMO_DASHBOARDS_DIR="${SHARED_CONFIG_DIR}/dashboards"
  # shellcheck source=/dev/null
  source "${XRAY_SOURCE_DIR}/env.sh"
  set +a
  XRAY_COMPOSE=(-f "${XRAY_SOURCE_DIR}/process-compose.yaml")
  echo "  X-ray observability: enabled XRAY=${XRAY} (Grafana at http://localhost:3000)"
else
  echo "  X-ray observability: disabled XRAY=${XRAY}"
fi
SERVER_FLAGS=(--no-server)
if [ "$SERVER" = "1" ]; then
  SERVER_FLAGS=(--address "${SERVER_ADDRESS}" --port "${SERVER_PORT}")
  echo "  Control API: http://${SERVER_ADDRESS}:${SERVER_PORT} (process-compose process ...)"
else
  echo "  Control API: disabled SERVER=${SERVER}"
fi
process-compose "${SERVER_FLAGS[@]}" \
  -f "${SOURCE_DIR}/process-compose.yaml" \
  -f "${NODES_COMPOSE}" \
  "${TC_COMPOSE[@]}" \
  "${XRAY_COMPOSE[@]}"
