#!/bin/bash
# WAN Emulation setup using tc (traffic control)
# Only runs if ENABLE_WAN_EMULATION=true

set -euo pipefail

if [ "${ENABLE_WAN_EMULATION:-false}" != "true" ]; then
    echo "WAN emulation disabled, skipping tc setup"
    exit 0
fi

echo "Setting up WAN emulation..."

# Get the network interface (eth0 in Docker)
IFACE="${WAN_INTERFACE:-eth0}"
RATE="${RATE:-10Mbps}"
DELAY="${DELAY:-200ms}"

echo "  Interface: $IFACE"
echo "  Rate: $RATE"
echo "  Delay: $DELAY"

# Check if tc is available
if ! command -v tc &> /dev/null; then
    echo "ERROR: tc command not found. Install iproute2."
    exit 1
fi

# Apply rate limiting with htb + fq_codel
echo "Applying rate limiting (htb + fq_codel)..."
tc qdisc add dev "$IFACE" root handle 1: htb default 1 2>/dev/null || \
    tc qdisc replace dev "$IFACE" root handle 1: htb default 1
tc class add dev "$IFACE" parent 1: classid 1:1 htb rate "$RATE" 2>/dev/null || \
    tc class replace dev "$IFACE" parent 1: classid 1:1 htb rate "$RATE"
tc qdisc add dev "$IFACE" parent 1:1 handle 10: fq_codel 2>/dev/null || \
    tc qdisc replace dev "$IFACE" parent 1:1 handle 10: fq_codel

# Apply delay with netem on ingress via ifb
echo "Applying delay (netem via ifb)..."

# Load ifb module (may fail in container, that's ok)
modprobe ifb 2>/dev/null || true

# Create ifb device if it doesn't exist
ip link add ifb0 type ifb 2>/dev/null || true
ip link set ifb0 up 2>/dev/null || true

# Set up ingress qdisc and redirect to ifb
tc qdisc add dev "$IFACE" handle ffff: ingress 2>/dev/null || \
    tc qdisc replace dev "$IFACE" handle ffff: ingress
tc filter add dev "$IFACE" parent ffff: protocol ip u32 match u32 0 0 action mirred egress redirect dev ifb0 2>/dev/null || true

# Apply netem delay on ifb
tc qdisc add dev ifb0 root netem delay "$DELAY" 2>/dev/null || \
    tc qdisc replace dev ifb0 root netem delay "$DELAY"

echo "WAN emulation configured successfully!"
echo "  Rate limiting: $RATE (htb + fq_codel)"
echo "  Delay: $DELAY (netem)"
