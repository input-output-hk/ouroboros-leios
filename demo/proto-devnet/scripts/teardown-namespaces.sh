# Tear down everything init-namespaces.sh created.
#
# Two callers: init-namespaces.sh sources this to clean up before it builds, and
# hold-namespaces.sh sources it to clean up when the project shuts down. Running
# it directly tears down and exits, which is the manual escape hatch.
#
# Idempotent — safe when nothing is up, and safe to run twice.
#
# Deliberately sets no shell options, so sourcing cannot change the caller's.
# NS_PREFIX defaults to this demo's. TOOL_PATH is prepended to PATH because sudo
# drops it and iproute2 may only exist in a devshell.

NS_PREFIX="${NS_PREFIX:-proto-devnet}"
export PATH="${TOOL_PATH:-}:${PATH}"

teardown_namespaces() {
  local ns dev stale orphans

  # A veth pair dies as a unit, and every interface here has its peer inside a
  # namespace, so deleting the namespaces also removes the host-side ends along
  # with the addresses and routes on them.
  mapfile -t stale < <(ip netns list | cut -d' ' -f1 | grep "^${NS_PREFIX}:" || true)
  for ns in "${stale[@]}"; do
    ip netns del "$ns" || true
  done

  # Unless a run died between `ip link add` and `ip link set netns`, which
  # leaves a host-side end with no peer to take it away.
  mapfile -t orphans < <(ip -o link show type veth 2>/dev/null |
    sed 's/^[0-9]*: //; s/[@:].*//' | grep -E '^(host->n|n[0-9]+->)' || true)
  for dev in "${orphans[@]}"; do
    ip link del "$dev" || true
  done
}

if [ "${BASH_SOURCE[0]}" = "$0" ]; then
  teardown_namespaces
fi
