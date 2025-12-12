set -exuo pipefail
set -a && source "$WORKING_DIR/.env" && set +a

NS_PREFIX="leios-experiment"
NS_UPSTREAM="${NS_PREFIX}:upstream"
NS_NODE0="${NS_PREFIX}:node0"
NS_DOWNSTREAM="${NS_PREFIX}:downstream"

# Delete all namespaces
ip netns del "$NS_UPSTREAM" || true
ip netns del "$NS_NODE0" || true
ip netns del "$NS_DOWNSTREAM" || true

# Create all namespaces
ip netns add "$NS_UPSTREAM"
ip netns add "$NS_NODE0"
ip netns add "$NS_DOWNSTREAM"

# Create a VETH link upstream <-> node0
ip link add "up->n0" type veth peer name "n0->up"
ip link set "up->n0" netns "$NS_UPSTREAM"
ip link set "n0->up" netns "$NS_NODE0"
ip netns exec "$NS_UPSTREAM" ip link set "up->n0" up
ip netns exec "$NS_NODE0" ip link set "n0->up" up

# Create a VETH link node0 <-> downstream
ip link add "n0->down" type veth peer name "down->n0"
ip link set "n0->down" netns "$NS_NODE0"
ip link set "down->n0" netns "$NS_DOWNSTREAM"
ip netns exec "$NS_NODE0" ip link set "n0->down" up
ip netns exec "$NS_DOWNSTREAM" ip link set "down->n0" up

# Create a VETH link host <-> upstream
ip link add "host->up" type veth peer name "up->host"
ip link set "up->host" netns "$NS_UPSTREAM"
ip link set "host->up" up
ip netns exec "$NS_UPSTREAM" ip link set "up->host" up

# Create a VETH link host <-> node0
ip link add "host->n0" type veth peer name "n0->host"
ip link set "n0->host" netns "$NS_NODE0"
ip link set "host->n0" up
ip netns exec "$NS_NODE0" ip link set "n0->host" up

# Create a VETH link host <-> downstream
ip link add "host->down" type veth peer name "down->host"
ip link set "down->host" netns "$NS_DOWNSTREAM"
ip link set "host->down" up
ip netns exec "$NS_DOWNSTREAM" ip link set "down->host" up

# Configure IFB devices for TC
ip netns exec "$NS_UPSTREAM" ip link add "ifb!up->n0" type ifb
ip netns exec "$NS_NODE0" ip link add "ifb!n0->up" type ifb
ip netns exec "$NS_NODE0" ip link add "ifb!n0->down" type ifb
ip netns exec "$NS_DOWNSTREAM" ip link add "ifb!down->n0" type ifb

ip netns exec "$NS_UPSTREAM" ip link set "ifb!up->n0" up
ip netns exec "$NS_NODE0" ip link set "ifb!n0->up" up
ip netns exec "$NS_NODE0" ip link set "ifb!n0->down" up
ip netns exec "$NS_DOWNSTREAM" ip link set "ifb!down->n0" up

# Configure traffic control

function limit_rate() {
  ns="$1"
  veth_dev="$2"
  rate="$3"
  ip netns exec "$ns" tc qdisc add dev "$veth_dev" root handle 1: htb default 1
  ip netns exec "$ns" tc class add dev "$veth_dev" parent 1: classid 1:1 htb rate "$rate"
  ip netns exec "$ns" tc qdisc add dev "$veth_dev" parent 1:1 handle 10: fq_codel
}

function delay() {
  ns="$1"
  veth_dev="$2"
  delay="$3"
  ip netns exec "$ns" tc qdisc add dev "$veth_dev" handle ffff: ingress
  ip netns exec "$ns" tc filter add dev "$veth_dev" parent ffff: protocol ip u32 match u32 0 0 action mirred egress redirect dev "ifb!$veth_dev"
  ip netns exec "$ns" tc qdisc add dev "ifb!$veth_dev" root netem delay "$delay"
}

limit_rate "$NS_UPSTREAM" "up->n0" "$RATE_UP_TO_N0"
delay "$NS_UPSTREAM" "up->n0" "$DELAY_UP_TO_N0"

limit_rate "$NS_NODE0" "n0->up" "$RATE_N0_TO_UP"
delay "$NS_NODE0" "n0->up" "$DELAY_N0_TO_UP"
limit_rate "$NS_NODE0" "n0->down" "$RATE_N0_TO_DOWN"
delay "$NS_NODE0" "n0->down" "$DELAY_N0_TO_DOWN"

limit_rate "$NS_DOWNSTREAM" "down->n0" "$RATE_DOWN_TO_N0"
delay "$NS_DOWNSTREAM" "down->n0" "$DELAY_DOWN_TO_N0"

# Configure IP assignments and network routes
ip netns exec "$NS_UPSTREAM" ip addr add local "$IP_UPSTREAM_NODE" peer "$IP_NODE0" dev "up->n0"
ip netns exec "$NS_UPSTREAM" ip addr add local "127.0.0.1" dev "lo"
ip netns exec "$NS_NODE0" ip addr add local "$IP_NODE0" peer "$IP_UPSTREAM_NODE" dev "n0->up"
ip netns exec "$NS_NODE0" ip addr add local "$IP_NODE0" peer "$IP_DOWNSTREAM_NODE" dev "n0->down"
ip netns exec "$NS_NODE0" ip addr add local "127.0.0.1" dev "lo"
ip netns exec "$NS_DOWNSTREAM" ip addr add local "$IP_DOWNSTREAM_NODE" peer "$IP_NODE0" dev "down->n0"
ip netns exec "$NS_DOWNSTREAM" ip addr add local "127.0.0.1" dev "lo"

IP_HOST="10.0.0.4"
ip addr add "$IP_HOST" dev "host->up"
ip route add "$IP_UPSTREAM_NODE" dev "host->up"
ip netns exec "$NS_UPSTREAM" ip addr add "$IP_UPSTREAM_NODE" dev "up->host"
ip netns exec "$NS_UPSTREAM" ip route add "$IP_HOST" dev "up->host"

ip addr add "$IP_HOST" dev "host->n0"
ip route add "$IP_NODE0" dev "host->n0"
ip netns exec "$NS_NODE0" ip addr add "$IP_NODE0" dev "n0->host"
ip netns exec "$NS_NODE0" ip route add "$IP_HOST" dev "n0->host"

ip addr add "$IP_HOST" dev "host->down"
ip route add "$IP_DOWNSTREAM_NODE" dev "host->down"
ip netns exec "$NS_DOWNSTREAM" ip addr add "$IP_DOWNSTREAM_NODE" dev "down->host"
ip netns exec "$NS_DOWNSTREAM" ip route add "$IP_HOST" dev "down->host"
