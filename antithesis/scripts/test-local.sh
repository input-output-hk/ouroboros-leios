#!/bin/bash
# Local test script for Leios Antithesis stack
# Tests that the docker-compose stack works correctly

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ANTITHESIS_DIR="$(dirname "$SCRIPT_DIR")"

cd "$ANTITHESIS_DIR"

# Configuration
ENABLE_WAN_EMULATION="${ENABLE_WAN_EMULATION:-true}"
TEST_DURATION="${TEST_DURATION:-60}"
STARTUP_TIMEOUT="${STARTUP_TIMEOUT:-180}"

echo "=============================================="
echo "Leios Antithesis Local Test"
echo "=============================================="
echo "WAN Emulation: $ENABLE_WAN_EMULATION"
echo "Test Duration: ${TEST_DURATION}s"
echo "Startup Timeout: ${STARTUP_TIMEOUT}s"
echo "=============================================="

# Cleanup function
cleanup() {
    echo ""
    echo "Cleaning up..."
    docker compose down -v 2>/dev/null || true
}
trap cleanup EXIT

# Build images
echo ""
echo ">>> Building images..."
docker compose build

# Start stack
echo ""
echo ">>> Starting stack (WAN emulation: $ENABLE_WAN_EMULATION)..."
export ENABLE_WAN_EMULATION
export ONSET_OF_REF_SLOT=$(date +%s)
docker compose up -d

# Wait for services to be healthy
echo ""
echo ">>> Waiting for services to be healthy (timeout: ${STARTUP_TIMEOUT}s)..."
start_time=$(date +%s)
while true; do
    elapsed=$(($(date +%s) - start_time))
    if [ $elapsed -gt $STARTUP_TIMEOUT ]; then
        echo "ERROR: Timeout waiting for services to be healthy"
        echo ""
        echo "Service status:"
        docker compose ps
        echo ""
        echo "Logs:"
        docker compose logs --tail=50
        exit 1
    fi

    # Check if all main services are healthy
    healthy_count=$(docker compose ps --format json 2>/dev/null | grep -c '"Health":"healthy"' || echo 0)
    if [ "$healthy_count" -ge 3 ]; then
        echo "All services healthy after ${elapsed}s"
        break
    fi

    echo "  Waiting... (${elapsed}s elapsed, $healthy_count/3 healthy)"
    sleep 5
done

# Check analysis container started
echo ""
echo ">>> Checking analysis container..."
sleep 10  # Give analysis container time to initialize

if docker compose logs analysis 2>/dev/null | grep -q "setup_complete\|Setup complete"; then
    echo "Analysis container signaled setup_complete"
else
    echo "WARNING: Analysis container may not have signaled setup_complete yet"
    echo "Analysis logs:"
    docker compose logs analysis --tail=20
fi

# Run for test duration
echo ""
echo ">>> Running test for ${TEST_DURATION}s..."
sleep "$TEST_DURATION"

# Check results
echo ""
echo ">>> Checking test results..."

# Check for assertions in analysis logs
echo ""
echo "Analysis container output:"
docker compose logs analysis --tail=30

# Check if Praos latency assertions passed
if docker compose logs analysis 2>/dev/null | grep -q "Praos block diffusion"; then
    echo ""
    echo "Praos latency assertions found in logs"
else
    echo ""
    echo "WARNING: No Praos latency assertions found in logs"
fi

# Check if Leios blocks were received
if docker compose logs analysis 2>/dev/null | grep -q "Leios blocks"; then
    echo "Leios block assertions found in logs"
else
    echo "WARNING: No Leios block assertions found in logs"
fi

# Final status
echo ""
echo "=============================================="
echo "Service Status:"
docker compose ps
echo "=============================================="

# Check for any errors
if docker compose ps --format json 2>/dev/null | grep -q '"Health":"unhealthy"'; then
    echo ""
    echo "ERROR: Some services are unhealthy"
    exit 1
fi

echo ""
echo "SUCCESS: Local test completed!"
echo "=============================================="
