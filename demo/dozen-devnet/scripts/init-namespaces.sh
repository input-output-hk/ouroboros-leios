set -exuo pipefail

# Put every node in its own network namespace, joined by one Linux bridge, and
# shape each node's single uplink.
#
# Unlike proto-devnet's per-edge veth mesh this is O(nodes), not O(edges): with
# nine fully meshed relays a per-edge setup would need 45 veth pairs and 90 ifb
# devices, and each relay would end up with 9 x RATE of aggregate bandwidth.
# Here RATE is the whole node's capacity, shared across all of its peers, which
# is what a real relay's NIC actually looks like. Connectivity is not enforced
# here at all — all nodes share one L2 segment and the topology comes purely
# from the localRoots in each node's topology.json.
#
# Expects NS_PREFIX, NODE_SPEC ("name=ip name=ip ..."), IP_HOST, RATE, DELAY.

BRIDGE="br-dozen"

# Delete namespaces from a previous run (ours only — proto-devnet may be up).
mapfile -t stale < <(ip netns list | cut -d' ' -f1 | grep "^${NS_PREFIX}:" || true)
for ns in "${stale[@]}"; do
  ip netns del "$ns" || true
done
ip link del "$BRIDGE" 2>/dev/null || true

# br_netfilter, if loaded, pushes bridged frames through iptables FORWARD,
# where a host firewall may drop them. Warn rather than change a global sysctl.
if [ -r /proc/sys/net/bridge/bridge-nf-call-iptables ] &&
  [ "$(cat /proc/sys/net/bridge/bridge-nf-call-iptables)" = "1" ]; then
  echo "WARNING: bridge-nf-call-iptables=1 — bridged frames traverse iptables" >&2
  echo "         FORWARD, which a host firewall (or docker's DROP policy) may" >&2
  echo "         drop. If nodes cannot reach each other, check that first:" >&2
  echo "           sudo iptables -L FORWARD -n" >&2
  echo "           sudo sysctl -w net.bridge.bridge-nf-call-iptables=0" >&2
fi

ip link add "$BRIDGE" type bridge
ip addr add "${IP_HOST}/24" dev "$BRIDGE"
ip link set "$BRIDGE" up

# Rate-limit the egress of a device: htb ceiling with fq_codel underneath. Any
# arguments after the rate are a command prefix for tc — `ip netns exec <ns>`
# for a device inside a namespace, nothing for one in the host namespace.
limit_rate() {
  local dev="$1" rate="$2"
  shift 2
  "$@" tc qdisc add dev "$dev" root handle 1: htb default 1
  "$@" tc class add dev "$dev" parent 1: classid 1:1 htb rate "$rate"
  "$@" tc qdisc add dev "$dev" parent 1:1 handle 10: fq_codel
}

# Delay a device's ingress by mirroring it onto an ifb and running netem there.
# Applying the delay on ingress only means each direction crosses exactly one
# netem, so DELAY stays a one-way delay and an RTT is 2 x DELAY.
add_delay() {
  local ns="$1" dev="$2" delay="$3"
  ip netns exec "$ns" ip link add "ifb!${dev}" type ifb
  ip netns exec "$ns" ip link set "ifb!${dev}" up
  ip netns exec "$ns" tc qdisc add dev "$dev" handle ffff: ingress
  ip netns exec "$ns" tc filter add dev "$dev" parent ffff: protocol ip u32 \
    match u32 0 0 action mirred egress redirect dev "ifb!${dev}"
  ip netns exec "$ns" tc qdisc add dev "ifb!${dev}" root netem delay "$delay"
}

read -r -a node_specs <<<"$NODE_SPEC"
for spec in "${node_specs[@]}"; do
  name="${spec%%=*}"
  addr="${spec#*=}"
  ns="${NS_PREFIX}:${name}"
  host_dev="v-${name}"
  node_dev="p-${name}"

  ip netns add "$ns"
  ip link add "$host_dev" type veth peer name "$node_dev"
  ip link set "$node_dev" netns "$ns"

  # Host side: plug into the bridge.
  ip link set "$host_dev" master "$BRIDGE"
  ip link set "$host_dev" up

  # Node side: one address on the shared /24, plus a working loopback.
  ip netns exec "$ns" ip addr add "127.0.0.1/8" dev lo
  ip netns exec "$ns" ip link set lo up
  ip netns exec "$ns" ip addr add "${addr}/24" dev "$node_dev"
  ip netns exec "$ns" ip link set "$node_dev" up

  # Uplink: what the node sends. Downlink: what the bridge sends to it — capped
  # too, so nine peers cannot collectively deliver 9 x RATE into one relay.
  limit_rate "$node_dev" "$RATE" ip netns exec "$ns"
  limit_rate "$host_dev" "$RATE"
  add_delay "$ns" "$node_dev" "$DELAY"
done
