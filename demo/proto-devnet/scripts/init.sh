#!/usr/bin/env bash
set -exuo pipefail

# Expects WORKING_DIR, CONFIG_DIR, and LEIOS_SCHEMA to be set

echo "Initializing proto-devnet in $WORKING_DIR"

# Check if WORKING_DIR already exists
if [ -d "$WORKING_DIR" ]; then
	echo "Working directory already exists: $WORKING_DIR"
	echo "Please remove it first if you want to reinitialize"
	exit 1
fi

# Create working directory structure
mkdir -p "$WORKING_DIR/node-data"
mkdir -p "$WORKING_DIR/socket/node1"
mkdir -p "$WORKING_DIR/socket/node2"
mkdir -p "$WORKING_DIR/socket/node3"

# Copy genesis files
echo "Copying genesis files from $CONFIG_DIR"
mkdir -p "$WORKING_DIR/genesis"
cp "$CONFIG_DIR"/*-genesis.json "$WORKING_DIR/genesis/"
chmod -R +rw "$WORKING_DIR/genesis"

# Set up each node
for i in 1 2 3; do
	NODE_DIR="$WORKING_DIR/node-data/node$i"
	POOL_DIR="$CONFIG_DIR/pools-keys/pool$i"

	echo "Setting up node$i"
	mkdir -p "$NODE_DIR/shelley"

	# Copy node config
	cp "$CONFIG_DIR/config.json" "$NODE_DIR/config.json"

	# Copy topology (using template for now, could be customized per-node)
	cp "$CONFIG_DIR/topology.template.json" "$NODE_DIR/topology.json"

	# Copy pool keys
	cp "$POOL_DIR/vrf.skey" "$NODE_DIR/shelley/vrf.skey"
	cp "$POOL_DIR/kes.skey" "$NODE_DIR/shelley/kes.skey"
	cp "$POOL_DIR/opcert.cert" "$NODE_DIR/shelley/opcert.cert"

	# Create Leios database
	if [ -f "$LEIOS_SCHEMA" ]; then
		cat "$LEIOS_SCHEMA" | sqlite3 "$NODE_DIR/leios.db"
		echo "Created leios.db for node$i"
	else
		echo "Warning: Leios schema not found at $LEIOS_SCHEMA"
	fi

	# Ensure everything is writable (important when CONFIG_DIR is in nix store)
	chmod -R +rw "$NODE_DIR"
done

echo "Proto-devnet initialized and prepared successfully"
