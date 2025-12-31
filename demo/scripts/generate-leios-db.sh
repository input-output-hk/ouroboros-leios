#!/usr/bin/env bash
set -euo pipefail

# Script to generate Leios database and schedule
# This can be run standalone before the demo

# Default values (DEFAULT_MANIFEST is set by the Nix package, or defaults to local path)
DEFAULT_OUTPUT_DIR="./leios-data"
: "${DEFAULT_MANIFEST:=./manifest.json}"

# Parse arguments
OUTPUT_DIR="${1:-$DEFAULT_OUTPUT_DIR}"
MANIFEST="${2:-$DEFAULT_MANIFEST}"

# Check if manifest exists
if [[ ! -f "$MANIFEST" ]]; then
  echo "Error: Manifest file not found: $MANIFEST"
  echo ""
  echo "Usage: generate-leios-db [output-dir] [manifest-file]"
  echo ""
  echo "Arguments:"
  echo "  output-dir    Directory where DB and schedule will be generated (default: $DEFAULT_OUTPUT_DIR)"
  echo "  manifest-file Path to manifest JSON file (default: uses packaged manifest)"
  echo ""
  echo "Example:"
  echo "  generate-leios-db ./my-data"
  echo "  generate-leios-db ./my-data ./custom-manifest.json"
  exit 1
fi

# Create output directory if it doesn't exist
mkdir -p "$OUTPUT_DIR"

echo "Generating Leios DB and schedule..."
echo "  Output directory: $OUTPUT_DIR"
echo "  Manifest: $MANIFEST"

# Generate the database and base schedule
leiosdemo202510 generate \
  "$OUTPUT_DIR/leios.db" \
  "$MANIFEST" \
  "$OUTPUT_DIR/base-schedule.json"

echo "Base schedule generated at: $OUTPUT_DIR/base-schedule.json"
echo ""
echo "Database generated at: $OUTPUT_DIR/leios.db"
echo ""
echo "Generation complete! You can now run the demo with:"
echo "  LEIOS_DB=$OUTPUT_DIR/leios.db LEIOS_BASE_SCHEDULE=$OUTPUT_DIR/base-schedule.json nix run .#leios-demo"
echo ""
echo "Note: The demo will apply EB_RELEASE_OFFSET at runtime to generate the final schedule."
echo "      Use EB_RELEASE_OFFSET environment variable to customize the release timing."
