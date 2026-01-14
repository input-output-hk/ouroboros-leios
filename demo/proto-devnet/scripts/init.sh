#!/usr/bin/env bash
set -euo pipefail

# Expects WORKING_DIR, CONFIG_DIR, and LEIOS_SCHEMA to be set

# Check if WORKING_DIR already exists
if [ -d "$WORKING_DIR" ]; then
	echo "Working directory already exists: $WORKING_DIR"
	echo "Skipping init"
	exit 0
fi
echo "Initializing proto-devnet in $WORKING_DIR"

# Create working directory
mkdir -p "$WORKING_DIR"

# Set up each node
nodes=(1 2 3)
for i in "${nodes[@]}"; do
	NODE_NAME="node$i"
	NODE_DIR="$WORKING_DIR/$NODE_NAME"
	POOL_DIR="$CONFIG_DIR/pools-keys/pool$i"

	echo "Setting up $NODE_NAME in $NODE_DIR"
	mkdir -p "$NODE_DIR"

	# Copy config files
	jq ".TraceOptionNodeName = \"$NODE_NAME\"" "$CONFIG_DIR/config.json" >"$NODE_DIR/config.json"

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
	# FIXME: copy them once to WORKING_DIR, update time in byron/shelley and symlink from there
	ln -s "$CONFIG_DIR/genesis" "$NODE_DIR/genesis"

	# Symlink pool keys (read-only)
	ln -s "$POOL_DIR" "$NODE_DIR/keys"

	# Create Leios database
	if [ -f "$LEIOS_SCHEMA" ]; then
		sqlite3 "$NODE_DIR/leios.db" <"$LEIOS_SCHEMA"
		echo "Created leios.db for $NODE_NAME"
	else
		echo "Warning: Leios schema not found at $LEIOS_SCHEMA"
	fi
done

echo "Proto-devnet initialized and prepared successfully"
