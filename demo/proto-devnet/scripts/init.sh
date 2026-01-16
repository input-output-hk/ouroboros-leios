#!/usr/bin/env bash
set -euo pipefail

# Expects WORKING_DIR and LEIOS_SCHEMA to be set

# Check if WORKING_DIR already exists
if [ -d "$WORKING_DIR" ]; then
	echo "Working directory already exists: $WORKING_DIR"
	echo "Skipping init"
	exit 0
fi
echo "Initializing proto-devnet in $WORKING_DIR"

# Create working directory
mkdir -p "$WORKING_DIR"

CONFIG_DIR="${SOURCE_DIR}/config"

# Copy genesis files and set start time
cp -r "$CONFIG_DIR/genesis" "$WORKING_DIR/genesis"
chmod u+w -R "${WORKING_DIR}/genesis"

startTimeEpoch=$(date +%s)
startTimeIso=$(date -u -d "@$startTimeEpoch" +"%Y-%m-%dT%H:%M:%SZ")

jq --argjson time "$startTimeEpoch" '.startTime = $time' \
	"$CONFIG_DIR/genesis/byron-genesis.json" >"$WORKING_DIR/genesis/byron-genesis.json"

jq --arg time "$startTimeIso" '.systemStart = $time' \
	"$CONFIG_DIR/genesis/shelley-genesis.json" >"$WORKING_DIR/genesis/shelley-genesis.json"

# Set up each node
nodes=(1 2 3)
for i in "${nodes[@]}"; do
	NODE_NAME="node$i"
	NODE_DIR="$WORKING_DIR/$NODE_NAME"
	POOL_DIR="$CONFIG_DIR/pools-keys/pool$i"

	echo "Setting up $NODE_NAME in $NODE_DIR"
	mkdir -p "$NODE_DIR"

	# Copy config files
	cat "$CONFIG_DIR/config.json" |
		jq ".TraceOptionNodeName = \"$NODE_NAME\"" |
		jq ".TraceOptions.\"\".backends[1] = \"PrometheusSimple 0.0.0.0 $((12900 + "$i"))\"" \
			>"$NODE_DIR/config.json"

	# Generate upstream endpoints to other nodes
	accessPoints=$(for j in "${nodes[@]}"; do
		# Except self
		if [ "$i" -ne "$j" ]; then
			port="PORT_NODE$j"
			address="IP_NODE$j"
			echo "{ \"port\": ${!port}, \"address\": \"${!address}\" }"
		fi
	done | jq -s '.')
	jq \
		--argjson accessPoints "$accessPoints" \
		'.localRoots[0].accessPoints = $accessPoints' \
		"$CONFIG_DIR/topology.template.json" >"$NODE_DIR/topology.json"

	# Symlink genesis files (shared, read-only)
	ln -s "../genesis/byron-genesis.json" "$NODE_DIR/"
	ln -s "../genesis/shelley-genesis.json" "$NODE_DIR/"
	ln -s "../genesis/alonzo-genesis.json" "$NODE_DIR/"
	ln -s "../genesis/conway-genesis.json" "$NODE_DIR/"
	ln -s "../genesis/dijkstra-genesis.json" "$NODE_DIR/"

	# Copy pool keys and set permissions
	cp -r "$POOL_DIR" "$NODE_DIR/keys"
	chmod 400 "$NODE_DIR/keys"/*.skey

	# Create Leios database
	if [ -f "$LEIOS_SCHEMA" ]; then
		sqlite3 "$NODE_DIR/leios.db" <"$LEIOS_SCHEMA"
		echo "Created leios.db for $NODE_NAME"
	else
		echo "Warning: Leios schema not found at $LEIOS_SCHEMA"
	fi
done

# Copy utxo-keys for tx-generator and set permissions
echo "Setting up utxo-keys for tx-generator"
cp -r "$CONFIG_DIR/utxo-keys" "$WORKING_DIR/utxo-keys"
find "$WORKING_DIR/utxo-keys" -name "*.skey" -exec chmod 400 {} \;

# Configure tx-generator
envsubst <"${SOURCE_DIR}/gen.template.json" >"${WORKING_DIR}/gen.json"

echo "Proto-devnet initialized and prepared successfully"
