#!/usr/bin/env bash
# 60_pretty_print_cert.sh
# Pretty-print certificate & votes using a Python helper.
# Usage:
#   ./60_pretty_print_cert.sh -d RUN_DIR [--all-voters] [--max-ids N]
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: 60_pretty_print_cert.sh -d RUN_DIR [--all-voters] [--max-ids N]

Options:
  -d, --dir RUN_DIR     Run directory containing certificate.cbor (and votes.cbor)
      --all-voters      Include full lists of persistent and non-persistent voters
      --max-ids N       When not using --all-voters, include at most N voter IDs (default 5)
EOF
  exit 2
}

# Defaults
DIR=""
ALL_VOTERS=0
MAX_IDS="5"

# Single portable arg parser (handles both short and long flags)
while [[ $# -gt 0 ]]; do
  case "$1" in
    -d|--dir)
      [[ $# -ge 2 ]] || usage
      DIR="$2"; shift 2 ;;
    --all-voters)
      ALL_VOTERS=1; shift ;;
    --max-ids)
      [[ $# -ge 2 ]] || usage
      MAX_IDS="$2"; shift 2 ;;
    --)
      shift; break ;;
    -*)
      usage ;;
    *)
      # ignore stray positional args
      shift ;;
  esac
done

[[ -z "${DIR}" ]] && usage

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
  printf '{ "error": "certificate not found: %s" }\n' "${CERT}"
  exit 1
fi

# Prefer venv python in demo/.venv if present, then $PYTHON, then python3, then python
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

# Build args for the Python helper
PY_ARGS=( "${CERT}" )
[[ -f "${VOTES}" ]] && PY_ARGS+=( "${VOTES}" )
PY_ARGS+=( --max-ids "${MAX_IDS}" )
[[ "${ALL_VOTERS}" -eq 1 ]] && PY_ARGS+=( --all-voters )

# Run the Python helper and emit JSON to both console and file
"${PY_BIN}" "${SCRIPT_DIR}/pretty_cert.py" "${PY_ARGS[@]}" | tee "${DIR_ABS}/certificate.pretty.json"