#!/bin/bash

# Exit on error
set -e

# Get the directory of this script
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SITE_DIR="$(dirname "$SCRIPT_DIR")"
FORMAL_SPEC_DIR="$(cd "$SITE_DIR/../../../ouroboros-leios-formal-spec" && pwd)"

echo "Building Agda documentation..."
cd "$FORMAL_SPEC_DIR"
nix build .#leiosDocs

echo "Copying Agda HTML files..."
mkdir -p "$SITE_DIR/static/agda_html"
cp -r result/share/doc/agda/html/* "$SITE_DIR/static/agda_html/"

echo "Processing Agda HTML files..."
cd "$SITE_DIR"
node scripts/process-agda-html.js

echo "Done! The Agda specification is now available at /agda_html/" 