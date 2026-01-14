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
for i in 1 2 3; do
	NODE_DIR="$WORKING_DIR/node$i"
	POOL_DIR="$CONFIG_DIR/pools-keys/pool$i"

	echo "Setting up node$i in $NODE_DIR"
	mkdir -p "$NODE_DIR"

	# Copy config files
	# TODO: rename node name and fill in topology
	cp "$CONFIG_DIR/config.json" "$NODE_DIR/config.json"
	cp "$CONFIG_DIR/topology.template.json" "$NODE_DIR/topology.json"

	# Symlink genesis files (shared, read-only)
	ln -s "$CONFIG_DIR/genesis" "$NODE_DIR/genesis"

	# Symlink pool keys (read-only)
	ln -s "$POOL_DIR" "$NODE_DIR/keys"

	# Create Leios database
	if [ -f "$LEIOS_SCHEMA" ]; then
		sqlite3 "$NODE_DIR/leios.db" <"$LEIOS_SCHEMA"
		echo "Created leios.db for node$i"
	else
		echo "Warning: Leios schema not found at $LEIOS_SCHEMA"
	fi
done

echo "Proto-devnet initialized and prepared successfully"
