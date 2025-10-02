#!/usr/bin/env bash
set -euo pipefail
DIR_SCRIPT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$DIR_SCRIPT/.env_cli"

usage() {
  cat <<USAGE
Usage: $0 -d <run_dir>

Verify the cryptographic validity of a certificate.

Options:
  -d, --dir   Run directory that contains registry.cbor and certificate.cbor
USAGE
  exit 1
}

DIR=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    -d|--dir) DIR="$2"; shift 2;;
    -h|--help) usage;;
    *) echo "Unknown argument: $1"; usage;;
  esac
done

[[ -z "${DIR}" ]] && usage
DIR="$(cd "$DIR" 2>/dev/null && pwd || true)"
[[ -z "${DIR}" || ! -d "${DIR}" ]] && { echo "Run directory not found: ${DIR}"; exit 1; }

REG="${DIR}/registry.cbor"
CERT="${DIR}/certificate.cbor"

[[ -f "${REG}" ]] || { echo "Missing ${REG}"; exit 1; }
[[ -f "${CERT}" ]] || { echo "Missing ${CERT}"; exit 1; }

echo "== [50_verify_certificate] DIR=${DIR} =="
"$CLI" --verbose verify-certificate \
  --registry-file "${REG}" \
  --certificate-file "${CERT}"