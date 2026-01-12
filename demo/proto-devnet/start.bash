set -eo pipefail

SCRIPT_DIR=$(readlink -f "$(dirname "$0")")

if [ -d devnet ]; then
	read -r -p "Environment devnet/ already exists. Delete it? (y/n): [y]" yn
	case ${yn:-y} in
	[Yy]*) rm -rf devnet ;;
	[Nn]*)
		echo "Aborted"
		exit 1
		;;
	esac
fi

# We need to create an environment before starting it, because the prototype
# `cardano-node` is a bit older than `cardano-testnet` and needs patching:

cardano-testnet create-env --output devnet --num-pool-nodes 3 --slot-length 1 --testnet-magic 164 --params-mainnet

cat devnet/configuration.yaml | jq '.EnableP2P = true' >devnet/configuration-p2p.yaml && mv devnet/configuration{-p2p,}.yaml

# Create leios DB (EB storage)
# TODO: move this to cardano-node code
SCHEMA=${SCRIPT_DIR}/../2025-11/data/leios-schema.sql
for node in node1 node2 node3; do
	cat "$SCHEMA" | sqlite3 devnet/node-data/$node/leios.db
done
# FIXME: not a relative path?
export LEIOS_DB_PATH="leios.db"

cardano-testnet cardano --node-env devnet --update-time
