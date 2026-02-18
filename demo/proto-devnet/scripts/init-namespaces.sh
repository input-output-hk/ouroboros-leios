set -exuo pipefail

NS_PREFIX="proto-devnet"
NS_NODE1="${NS_PREFIX}:node1"
NS_NODE2="${NS_PREFIX}:node2"
NS_NODE3="${NS_PREFIX}:node3"

# Delete existing namespaces (cleanup)
ip netns del "$NS_NODE1" 2>/dev/null || true
ip netns del "$NS_NODE2" 2>/dev/null || true
ip netns del "$NS_NODE3" 2>/dev/null || true

# Create namespaces
ip netns add "$NS_NODE1"
ip netns add "$NS_NODE2"
ip netns add "$NS_NODE3"

# Create VETH links between each pair of nodes (full mesh)
# node1 <-> node2
ip link add "n1->n2" type veth peer name "n2->n1"
ip link set "n1->n2" netns "$NS_NODE1"
ip link set "n2->n1" netns "$NS_NODE2"
ip netns exec "$NS_NODE1" ip link set "n1->n2" up
ip netns exec "$NS_NODE2" ip link set "n2->n1" up

# node1 <-> node3
ip link add "n1->n3" type veth peer name "n3->n1"
ip link set "n1->n3" netns "$NS_NODE1"
ip link set "n3->n1" netns "$NS_NODE3"
ip netns exec "$NS_NODE1" ip link set "n1->n3" up
ip netns exec "$NS_NODE3" ip link set "n3->n1" up

# node2 <-> node3
ip link add "n2->n3" type veth peer name "n3->n2"
ip link set "n2->n3" netns "$NS_NODE2"
ip link set "n3->n2" netns "$NS_NODE3"
ip netns exec "$NS_NODE2" ip link set "n2->n3" up
ip netns exec "$NS_NODE3" ip link set "n3->n2" up

# Create VETH links from host to each node (for metrics, socket access)
for i in 1 2 3; do
	ns_var="NS_NODE${i}"
	ip link add "host->n${i}" type veth peer name "n${i}->host"
	ip link set "n${i}->host" netns "${!ns_var}"
	ip link set "host->n${i}" up
	ip netns exec "${!ns_var}" ip link set "n${i}->host" up
done

# Configure IFB devices and traffic control for ingress
# Each entry: "namespace device"
EDGES=(
	"$NS_NODE1 n1->n2"
	"$NS_NODE1 n1->n3"
	"$NS_NODE2 n2->n1"
	"$NS_NODE2 n2->n3"
	"$NS_NODE3 n3->n1"
	"$NS_NODE3 n3->n2"
)

limit_rate() {
	local ns="$1" dev="$2" rate="$3"
	ip netns exec "$ns" tc qdisc add dev "$dev" root handle 1: htb default 1
	ip netns exec "$ns" tc class add dev "$dev" parent 1: classid 1:1 htb rate "$rate"
	ip netns exec "$ns" tc qdisc add dev "$dev" parent 1:1 handle 10: fq_codel
}

add_delay() {
	local ns="$1" dev="$2" delay="$3"
	ip netns exec "$ns" tc qdisc add dev "$dev" handle ffff: ingress
	ip netns exec "$ns" tc filter add dev "$dev" parent ffff: protocol ip u32 match u32 0 0 action mirred egress redirect dev "ifb!${dev}"
	ip netns exec "$ns" tc qdisc add dev "ifb!${dev}" root netem delay "$delay"
}

for edge in "${EDGES[@]}"; do
	ns="${edge%% *}"
	dev="${edge#* }"
	# IFB device for ingress TC
	ip netns exec "$ns" ip link add "ifb!${dev}" type ifb
	ip netns exec "$ns" ip link set "ifb!${dev}" up
	# Apply symmetric rate limit and delay
	limit_rate "$ns" "$dev" "$RATE"
	add_delay "$ns" "$dev" "$DELAY"
done

# Configure IP addresses using point-to-point addressing
# node1
ip netns exec "$NS_NODE1" ip addr add local "$IP_NODE1" peer "$IP_NODE2/32" dev "n1->n2"
ip netns exec "$NS_NODE1" ip addr add local "$IP_NODE1" peer "$IP_NODE3/32" dev "n1->n3"
ip netns exec "$NS_NODE1" ip addr add local "127.0.0.1" dev "lo"

# node2
ip netns exec "$NS_NODE2" ip addr add local "$IP_NODE2" peer "$IP_NODE1/32" dev "n2->n1"
ip netns exec "$NS_NODE2" ip addr add local "$IP_NODE2" peer "$IP_NODE3/32" dev "n2->n3"
ip netns exec "$NS_NODE2" ip addr add local "127.0.0.1" dev "lo"

# node3
ip netns exec "$NS_NODE3" ip addr add local "$IP_NODE3" peer "$IP_NODE1/32" dev "n3->n1"
ip netns exec "$NS_NODE3" ip addr add local "$IP_NODE3" peer "$IP_NODE2/32" dev "n3->n2"
ip netns exec "$NS_NODE3" ip addr add local "127.0.0.1" dev "lo"

# Host routes to each node
ip addr add "$IP_HOST" dev "host->n1"
ip route add "$IP_NODE1" dev "host->n1"
ip netns exec "$NS_NODE1" ip addr add "$IP_NODE1" dev "n1->host"
ip netns exec "$NS_NODE1" ip route add "$IP_HOST" dev "n1->host"

ip addr add "$IP_HOST" dev "host->n2"
ip route add "$IP_NODE2" dev "host->n2"
ip netns exec "$NS_NODE2" ip addr add "$IP_NODE2" dev "n2->host"
ip netns exec "$NS_NODE2" ip route add "$IP_HOST" dev "n2->host"

ip addr add "$IP_HOST" dev "host->n3"
ip route add "$IP_NODE3" dev "host->n3"
ip netns exec "$NS_NODE3" ip addr add "$IP_NODE3" dev "n3->host"
ip netns exec "$NS_NODE3" ip route add "$IP_HOST" dev "n3->host"
