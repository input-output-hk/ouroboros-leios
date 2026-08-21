# Holds the network namespaces for the lifetime of the project.
#
# Its only job is to still be running at shutdown. process-compose runs a
# process's shutdown hook only while that process is alive, and InitNamespaces
# exits the moment it is done, so a hook on InitNamespaces never fires — the
# teardown has to hang off something long-lived. This is that something.
#
# Runs elevated, like the nodes, so the trap has the privileges to delete
# namespaces and the bridge.
set -uo pipefail

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
# shellcheck source=/dev/null
source "${SCRIPT_DIR}/teardown-namespaces.sh"

cleanup() {
	# Without this both traps fire and the teardown runs twice. It is idempotent,
	# so that is only noise, but noise in a teardown is how people learn to
	# ignore teardown output.
	trap - EXIT TERM INT
	echo "tearing down ${NS_PREFIX}:* namespaces and ${BRIDGE}"
	teardown_namespaces
	exit 0
}
trap cleanup EXIT TERM INT

echo "holding ${NS_PREFIX}:* namespaces; they are torn down when this stops"
sleep infinity &
wait
