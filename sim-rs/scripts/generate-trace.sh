#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<EOF
Usage: $(basename "$0") <topology> <output-name> [-s slots] [-p params]...

Generate a simulation trace for the UI.

Arguments:
  topology     Path to topology YAML file
  output-name  Name for output (produces ui/public/traces/<name>-nocpu.jsonl.gz)
  -s slots     Number of slots to simulate (default: 120)
  -p params    Parameter file(s) passed to sim-cli (repeatable)

Example:
  $(basename "$0") ../data/simulation/pseudo-mainnet/topology-v3.yaml micro-mainnet -s 120
EOF
  exit 1
}

[[ $# -lt 2 ]] && usage

TOPOLOGY="$1"
OUTPUT_NAME="$2"
shift 2

SLOTS=120
PARAMS=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    -s) SLOTS="$2"; shift 2 ;;
    -p) PARAMS+=(-p "$2"); shift 2 ;;
    *)  echo "Unknown option: $1"; usage ;;
  esac
done

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SIM_RS_DIR="$(dirname "$SCRIPT_DIR")"
TRACES_DIR="$SIM_RS_DIR/../ui/public/traces"
RAW="$TRACES_DIR/${OUTPUT_NAME}.jsonl"
FINAL="$TRACES_DIR/${OUTPUT_NAME}-nocpu.jsonl.gz"

mkdir -p "$TRACES_DIR"

echo "Building sim-cli..."
cargo build --release --manifest-path "$SIM_RS_DIR/Cargo.toml"

echo "Running simulation: $SLOTS slots on $(basename "$TOPOLOGY")..."
"$SIM_RS_DIR/target/release/sim-cli" \
  "$TOPOLOGY" "$RAW" \
  -s "$SLOTS" \
  "${PARAMS[@]+"${PARAMS[@]}"}"

echo "Stripping CPU events and compressing..."
grep -v 'Cpu' < "$RAW" | gzip > "$FINAL"
rm "$RAW"

echo "Done: $FINAL"
