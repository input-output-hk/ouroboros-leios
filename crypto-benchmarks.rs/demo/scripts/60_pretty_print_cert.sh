#!/usr/bin/env bash
# 60_pretty_print_cert.sh
# Wrapper that pretty-prints certificate & votes using an embedded Python helper.
# Usage: ./60_pretty_print_cert.sh -d RUN_DIR
set -euo pipefail

usage() { echo "Usage: $0 -d RUN_DIR | --dir RUN_DIR"; exit 2; }


# Defaults
DIR=""

# Parse short options
while getopts "d:" opt; do
  case "$opt" in
    d) DIR="$OPTARG" ;;
    *) usage ;;
  esac
done
shift $((OPTIND-1))

# Parse long options (e.g., --dir RUN_DIR)
while (( "$#" )); do
  case "$1" in
    --dir)
      DIR="${2:-}"
      shift 2 ;;
    --)
      shift; break ;;
    -*)
      usage ;;
    *)
      # ignore positional args
      shift ;;
  esac
done

if [[ -z "${DIR}" ]]; then
  usage
fi

# Resolve absolute paths
DIR_ABS="$(cd "${DIR}" 2>/dev/null && pwd || true)"
if [[ -z "${DIR_ABS}" || ! -d "${DIR_ABS}" ]]; then
  echo "Error: RUN_DIR not found: ${DIR}" >&2
  exit 1
fi

echo "== [60_pretty_print_cert] DIR=${DIR_ABS} =="

CERT="${DIR_ABS}/certificate.cbor"
VOTES="${DIR_ABS}/votes.cbor"

if [[ ! -f "${CERT}" ]]; then
  echo "{ \"error\": \"certificate not found: ${CERT}\" }"
  exit 1
fi

# Prefer virtualenv python in demo/.venv if present, then $PYTHON, then python3, then python
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
DEMO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
if [[ -x "${DEMO_ROOT}/.venv/bin/python" ]]; then
  PY_BIN="${DEMO_ROOT}/.venv/bin/python"
elif [[ -n "${PYTHON:-}" && -x "${PYTHON}" ]]; then
  PY_BIN="${PYTHON}"
elif command -v python3 >/dev/null 2>&1; then
  PY_BIN="$(command -v python3)"
elif command -v python >/dev/null 2>&1; then
  PY_BIN="$(command -v python)"
else
  echo '{ "error": "No Python interpreter found. Install python3 or create .venv." }'
  exit 2
fi

# Run the Python helper, print to console, and also save to RUN_DIR/certificate.pretty.json
OUTPUT="$("${PY_BIN}" "${SCRIPT_DIR}/pretty_cert.py" "${CERT}" "${VOTES}")"

# Print to console and save to file
echo "${OUTPUT}" | tee "${DIR_ABS}/certificate.pretty.json" >/dev/null
echo "${OUTPUT}"