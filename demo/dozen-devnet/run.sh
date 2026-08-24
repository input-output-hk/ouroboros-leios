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
: "${COLOR2:=00a0ff}"
: "${COLOR3:=ffd000}"
# Per-node mempool observers. MONITOR=0 turns them off, which is also the A/B for
# how much the observer itself perturbs what it measures: a drain is a round trip
# per transaction, so it is cheap per round but not free.
: "${MONITOR:=1}"
: "${MEMPOOL_MONITOR:=mempool-monitor}"
# Seconds between snapshots. Fragmentation evolves over tens of seconds, so a
# faster rate buys nothing and costs real round trips.
: "${MONITOR_INTERVAL:=10}"
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
	: "${IP_OFFSET:=10}"
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
	: "${IP_OFFSET:=0}"
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

# Which block producer's group a node belongs to, i.e. the digit after its
# prefix: bp2 and relay21..relay23 are all group 2. That is the group whose
# generator colour counts as "local" for that node.
node_group() {
	local digits="${1#bp}"
	digits="${digits#relay}"
	echo "${digits:0:1}"
}

# The Nth node in NODES gets IP_PREFIX(IP_OFFSET + N).
node_ip() {
	local name="$1" i=0 n
	for n in "${NODES[@]}"; do
		i=$((i + 1))
		if [ "$n" = "$name" ]; then
			echo "${IP_PREFIX}$((IP_OFFSET + i))"
			return 0
		fi
	done
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
			if [ "$tc" = "1" ]; then
				echo "      ${IP_BIN} netns exec ${NS_PREFIX}:${name} bash \"${SOURCE_DIR}/run-node.sh\""
			else
				echo "      bash \"${SOURCE_DIR}/run-node.sh\""
			fi
			echo "    log_location: \"${WORKING_DIR}/${name}/node.log\""
			# The host reaches every node through the bridge, so the probe works in
			# both the namespaced and the loopback case.
			echo "    readiness_probe:"
			echo "      exec:"
			echo "        command: \"bash -c ': </dev/tcp/${ip}/${PORT}'\""
			echo "      initial_delay_seconds: 5"
			echo "      period_seconds: 2"
			echo "      failure_threshold: 60"
			if [ "$tc" = "1" ]; then
				echo "    depends_on:"
				echo "      InitNamespaces:"
				echo "        condition: process_completed_successfully"
			fi
		done

		# One observer per node, because fragmentation is a statement about how
		# mempools differ and an aggregate would hide it. is_interactive gives
		# each one a process-compose pane, so twelve panes need no extra terminals.
		if [ "$MONITOR" = "1" ]; then
			local group own
			for name in "${NODES[@]}"; do
				group=$(node_group "$name")
				own="COLOR${group}"
				echo "  ObserveMempool-${name}:"
				echo "    working_dir: ${WORKING_DIR}"
				echo "    command: >"
				echo "      ${MEMPOOL_MONITOR}"
				echo "      --socket-path ${name}/node.socket"
				echo "      --testnet-magic 164"
				echo "      --label ${name}"
				echo "      --own-color ${!own}"
				echo "      --interval ${MONITOR_INTERVAL}"
				echo "      --tsv ${WORKING_DIR}/mempool-${name}.tsv"
				echo "    is_interactive: true"
				echo "    depends_on:"
				echo "      ${name}:"
				echo "        condition: process_healthy"
			done
		fi
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
# Only required when the observers are actually being started.
if [ "$MONITOR" = "1" ] && [ "$MEMPOOL_MONITOR" = "mempool-monitor" ]; then
	REQUIRED_COMMANDS+=("mempool-monitor")
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

# Check if WORKING_DIR already exists
if [ -d "$WORKING_DIR" ]; then
	echo "Working directory already exists: $WORKING_DIR"
	read -r -rp "Remove and re-initialize? (Y/n): " response
	if [[ "$response" =~ ^[Yy]$ || -z "$response" ]]; then
		chmod a+w -R "$WORKING_DIR"
		rm -rf "$WORKING_DIR"
	else
		echo "Aborting."
		exit 0
	fi
fi
echo "Initializing dozen-devnet in $WORKING_DIR"

# Create working directory
mkdir -p "$WORKING_DIR"

CONFIG_DIR="${SOURCE_DIR}/config"

# Copy genesis files and set start time
cp -r "$SHARED_CONFIG_DIR/genesis" "$WORKING_DIR/genesis"
chmod u+w -R "${WORKING_DIR}/genesis"

startTimeEpoch=$(date +%s)
startTimeIso=$(date -u -d "@$startTimeEpoch" +"%Y-%m-%dT%H:%M:%SZ")

jq --argjson time "$startTimeEpoch" '.startTime = $time' \
	"$SHARED_CONFIG_DIR/genesis/byron-genesis.json" >"$WORKING_DIR/genesis/byron-genesis.json"

jq --arg time "$startTimeIso" '.systemStart = $time' \
	"$SHARED_CONFIG_DIR/genesis/shelley-genesis.json" >"$WORKING_DIR/genesis/shelley-genesis.json"

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
		ln -s "../genesis/${era}-genesis.json" "$NODE_DIR/"
	done

	# Only block producers forge, so only they get pool keys. run-node.sh keys off
	# the presence of keys/ to decide whether to pass the forging arguments.
	case "$NODE_NAME" in
	bp*)
		cp -r "$SHARED_CONFIG_DIR/pools-keys/pool${NODE_NAME#bp}" "$NODE_DIR/keys"
		chmod 400 "$NODE_DIR/keys"/*.skey
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
	for v in TPS OUTPUTS RATE DELAY TC XRAY SERVER NODE_RTS; do
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
