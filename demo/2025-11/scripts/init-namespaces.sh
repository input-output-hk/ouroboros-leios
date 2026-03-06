set -exuo pipefail

IP=10.0.0.
#upstream is 10.0.0.1
#middle/N0   is 10.0.0.2
#downstream is 10.0.0.3

DELAYS1=([2]=$DELAY_UP_TO_N0)
RATES1=([2]=$RATE_UP_TO_N0)
DELAYS2=([1]=$DELAY_N0_TO_UP [3]=$DELAY_N0_TO_DOWN)
RATES2=([1]=$RATE_N0_TO_UP [3]=$RATE_N0_TO_DOWN)
DELAYS3=([2]=$DELAY_DOWN_TO_N0)
RATES3=([2]=$RATE_DOWN_TO_N0)

HOSTS=$(seq 1 3)

NS_PREFIX="leios-experiment"
NS=([1]="${NS_PREFIX}:upstream" "${NS_PREFIX}:node0" "${NS_PREFIX}:downstream")

add_edge() {
  set -x
  i=$1
  local IP=$IP$i
  local NS=${NS[$i]}
  # create veth pair to connect ns${i} to ns-br
  ip link add veth${i} netns $NS type veth peer name veth${i}-br netns ns-br

  # Bring the devices up.
  ip -n $NS link set veth${i} up
  ip -n ns-br link set veth${i}-br up

  # Assign IP address to the veth interface at the host side.
  ip -n $NS addr add ${IP}/24 dev veth${i}
  # Plug opposite to switch
  ip -n ns-br link set veth${i}-br master br;

  { set +x; } 2>/dev/null
}

# scrub
{ set +x; } 2>/dev/null
for i in $HOSTS; do { ip netns del ${NS[$i]}; } 2>/dev/null; done
sudo ip netns del ns-br

# create namespaces
for i in $HOSTS; do set -x; ip netns add ${NS[$i]}; { set +x; } 2>/dev/null; done
set -x
ip netns add ns-br

# create switch
ip -n ns-br link add name br type bridge
ip -n ns-br link set dev br up
{ set +x; } 2>/dev/null
for i in $HOSTS; do
  add_edge $i
done

# shape egress
for i in $HOSTS; do
    declare -n DELAYS="DELAYS$i"
    declare -n RATES="RATES$i"
    NS_=${NS[$i]}
    set -x
    tc -n $NS_ qdisc add dev veth$i root handle 1: htb
    tc -n ns-br qdisc add dev veth${i}-br root handle 1: prio
    { set +x; } 2>/dev/null
    for peer_x in ${!DELAYS[@]}; do
        set -x
        IP=10.0.0.$peer_x
        DELAY=${DELAYS[$peer_x]}
        RATE=${RATES[$peer_x]}
        tc -n $NS_ class add dev veth$i parent 1: classid 1:${peer_x} htb rate ${RATE} burst 15kb
        tc -n $NS_ filter add dev veth$i protocol ip parent 1: prio 1 u32 match ip dst $IP flowid 1:$peer_x
        tc -n ns-br filter add dev veth${i}-br protocol ip parent 1: prio 1 u32 match ip dst $IP flowid 1:$peer_x
        tc -n ns-br qdisc add dev veth${i}-br parent 1:$peer_x netem delay ${DELAY}
        { set +x; } 2>/dev/null
    done
    { set +x; } 2>/dev/null
done
