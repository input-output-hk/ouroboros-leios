#!/bin/bash

# Exit on error
set -e

# Get the directory of this script
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SITE_DIR="$(dirname "$SCRIPT_DIR")"
FORMAL_SPEC_DIR="$(cd "$SITE_DIR/../../../ouroboros-leios-formal-spec" && pwd)"

echo "Testing formal spec integration..."

# Step 1: Build formal spec docs (simulating formal-spec.yaml)
echo "Building formal spec documentation..."
cd "$FORMAL_SPEC_DIR"

# Clean up any previous build artifacts
rm -rf result

# Add Nix configuration for trusted users
export NIX_CONFIG="trusted-users = root $USER
substituters = https://cache.nixos.org/
trusted-public-keys = cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY="

# Build the docs with --impure to handle dirty git tree
echo "Running nix build..."
nix build .#leiosDocs --impure

# Step 2: Copy docs to site (simulating formal-spec-integration.yaml)
echo "Copying docs to site..."
mkdir -p "$SITE_DIR/static/agda_html"

# The HTML files are directly in result/html
HTML_DIR="result/html"
if [ ! -d "$HTML_DIR" ]; then
    echo "Error: Could not find HTML directory at $HTML_DIR"
    echo "Contents of result directory:"
    ls -R result
    exit 1
fi

# Copy the files
echo "Copying from $HTML_DIR to $SITE_DIR/static/agda_html/"
cp -r "$HTML_DIR"/* "$SITE_DIR/static/agda_html/"

# Step 3: Process the HTML files
echo "Processing HTML files..."
cd "$SITE_DIR"
node scripts/process-agda-html.js

# Step 4: Build the site
echo "Building site..."
yarn build

echo "Done! You can test the site with:"
echo "cd $SITE_DIR && yarn serve" 