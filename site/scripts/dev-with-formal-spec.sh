#!/bin/bash

# Exit on error
set -e

# Get the directory of this script
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SITE_DIR="$(dirname "$SCRIPT_DIR")"
FORMAL_SPEC_DIR="$(cd "$SITE_DIR/../../ouroboros-leios-formal-spec" && pwd)"

echo "Building Agda documentation..."
cd "$FORMAL_SPEC_DIR"

# Add Nix configuration for trusted users
export NIX_CONFIG="trusted-users = root $USER
substituters = https://cache.nixos.org/
trusted-public-keys = cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY="

# Build the docs with --impure to handle dirty git tree
nix build .#leiosDocs --impure

echo "Copying Agda HTML files..."
mkdir -p "$SITE_DIR/static/agda_html"

# Backup our custom CSS if it exists
if [ -f "$SITE_DIR/static/agda_html/agda.css" ]; then
    cp "$SITE_DIR/static/agda_html/agda.css" "$SITE_DIR/static/agda_html/agda.css.bak"
fi

# Copy all files except Agda.css
cp -r result/share/doc/agda/html/* "$SITE_DIR/static/agda_html/"

# Restore our custom CSS
if [ -f "$SITE_DIR/static/agda_html/agda.css.bak" ]; then
    mv "$SITE_DIR/static/agda_html/agda.css.bak" "$SITE_DIR/static/agda_html/agda.css"
fi

echo "Processing Agda HTML files..."
cd "$SITE_DIR"
node scripts/process-agda-html.js

echo "Starting development server..."
yarn start 
