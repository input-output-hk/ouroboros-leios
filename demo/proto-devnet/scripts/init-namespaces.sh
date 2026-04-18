set -exuo pipefail

NS_PREFIX="proto-devnet"
NS_NODE1="${NS_PREFIX}:node1"
NS_NODE2="${NS_PREFIX}:node2"
NS_NODE3="${NS_PREFIX}:node3"

HOSTS="1 2 3"

# scrub
for i in $HOSTS; do
  ip netns del "${NS_PREFIX}:node${i}" 2>/dev/null || true
done
ip netns del ns-br 2>/dev/null || true

# create namespaces
for i in $HOSTS; do ip netns add "${NS_PREFIX}:node${i}"; done
ip netns add ns-br

# create switch
ip -n ns-br link add name br type bridge
ip -n ns-br link set dev br up

# connect each node to the bridge
for i in $HOSTS; do
  ns_var="NS_NODE${i}"
  ip_var="IP_NODE${i}"
  NS="${!ns_var}"
  IP="${!ip_var}"
  ip link add "veth${i}" netns "$NS" type veth peer name "veth${i}-br" netns ns-br
  ip -n "$NS" link set "veth${i}" up
  ip -n "$NS" link set lo up
  ip -n ns-br link set "veth${i}-br" up
  ip -n "$NS" addr add "${IP}/24" dev "veth${i}"
  ip -n ns-br link set "veth${i}-br" master br
done

# shape traffic: per-peer rate limit on node egress, uniform delay on bridge-side
for i in $HOSTS; do
  ns_var="NS_NODE${i}"
  NS="${!ns_var}"
  tc -n "$NS" qdisc add dev "veth${i}" root handle 1: htb
  tc -n ns-br qdisc add dev "veth${i}-br" root handle 1: prio
  for peer in $HOSTS; do
    if [ "$i" -ne "$peer" ]; then
      peer_ip_var="IP_NODE${peer}"
      PEER_IP="${!peer_ip_var}"
      tc -n "$NS" class add dev "veth${i}" parent 1: classid "1:${peer}" htb rate "${RATE}" burst 15kb
      tc -n "$NS" qdisc add dev "veth${i}" parent "1:${peer}" fq_codel \
         quantum 2000 target 5ms interval 10ms
      tc -n "$NS" filter add dev "veth${i}" protocol ip parent 1: prio 1 u32 \
         match ip dst "${PEER_IP}" flowid "1:${peer}"
      tc -n ns-br filter add dev "veth${i}-br" protocol ip parent 1: prio 1 u32 \
         match ip dst "${PEER_IP}" flowid "1:${peer}"
      tc -n ns-br qdisc add dev "veth${i}-br" parent "1:${peer}" netem delay "${DELAY}"
    fi
  done
done

# Create VETH links from host to each node (for metrics, socket access)
for i in $HOSTS; do
  ns_var="NS_NODE${i}"
  NS="${!ns_var}"
  ip link add "host->n${i}" type veth peer name "n${i}->host"
  ip link set "n${i}->host" netns "$NS"
  ip link set "host->n${i}" up
  ip netns exec "$NS" ip link set "n${i}->host" up
done

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
