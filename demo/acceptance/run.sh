#!/usr/bin/env bash
#
# The acceptance demo is proto-devnet in a line, with its middle node swapped for
# the relay under test; see README.md.
set -eo pipefail

set -a
: "${ACCEPTANCE_DIR:=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}"
: "${PROTO_DEVNET_DIR:=${ACCEPTANCE_DIR}/../proto-devnet}"
: "${WORKING_DIR:=$(pwd)/tmp-acceptance}"
# Defaults to the prototype node, the reference to reach parity with.
: "${RELAY_CARDANO_NODE:=$(command -v cardano-node || true)}"
TOPOLOGY=line
RELAY_NODES=2
CARDANO_NODE_2="$RELAY_CARDANO_NODE"
EXTRA_COMPOSE="${ACCEPTANCE_DIR}/process-compose.yaml ${EXTRA_COMPOSE:-}"
set +a

exec bash "${PROTO_DEVNET_DIR}/run.sh"
