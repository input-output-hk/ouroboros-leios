#!/bin/bash

# Exit on error
set -e

# Get the absolute paths
SITE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
FORMAL_SPEC_DIR="$SITE_DIR/static/formal-spec"
FORMAL_SPEC_ROOT="$(cd "$SITE_DIR/../../ouroboros-leios-formal-spec" && pwd)"

echo "Building Agda documentation..."

# Build Agda documentation
(cd "$FORMAL_SPEC_ROOT" && nix build .#leiosDocs)

# Create formal-spec directory if it doesn't exist and set permissions
mkdir -p "$FORMAL_SPEC_DIR"
chmod 755 "$FORMAL_SPEC_DIR"

# Remove existing files if any
rm -rf "$FORMAL_SPEC_DIR"/*

# Copy files with proper permissions (macOS compatible)
cp -R "$FORMAL_SPEC_ROOT/result/html/"* "$FORMAL_SPEC_DIR/"
chmod -R 755 "$FORMAL_SPEC_DIR"

echo "Processing HTML files..."

# Check if config file exists
CONFIG_PATH="$SITE_DIR/agda-docs.config.json"
if [ ! -f "$CONFIG_PATH" ]; then
    echo "Error: agda-docs.config.json not found"
    exit 1
fi

# Process HTML files using the agda-web-docs-lib
cd "$SITE_DIR" && NODE_OPTIONS="--max-old-space-size=16384" npx agda-web-docs-lib process "$FORMAL_SPEC_DIR" "$CONFIG_PATH"