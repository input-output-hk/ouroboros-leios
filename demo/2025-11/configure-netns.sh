NS_PREFIX="leios_experiment"
NS_UPSTREAM="${NS_PREFIX}-upstream"
NS_NODE0="${NS_PREFIX}-node0"
NS_DOWNSTREAM="${NS_PREFIX}-downstream"

# Delete all namespaces
ip netns del "$NS_UPSTREAM";
ip netns del "$NS_NODE0";
ip netns del "$NS_DOWNSTREAM";

# Create all namespaces
ip netns add "$NS_UPSTREAM";
ip netns add "$NS_NODE0";
ip netns add "$NS_DOWNSTREAM";

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

limit_rate "$NS_UPSTREAM" "up->n0" "100mbit"
delay "$NS_UPSTREAM" "up->n0" "20ms"

limit_rate "$NS_NODE0" "n0->up" "100mbit"
delay "$NS_NODE0" "n0->up" "20ms"
limit_rate "$NS_NODE0" "n0->down" "100mbit"
delay "$NS_NODE0" "n0->down" "20ms"

limit_rate "$NS_DOWNSTREAM" "down->n0" "100mbit"
delay "$NS_DOWNSTREAM" "down->n0" "20ms"

# Configure UPSTREAM network
# ip netns exec "$NS_UPSTREAM" ip addr add "$NET_NODE0" dev "upstream->node0"

