# Leios Antithesis Testing

Docker Compose orchestration for testing Leios consensus using [Antithesis](https://antithesis.com/) deterministic simulation testing.

## Configurations

Two mutually exclusive network configurations are available:

1. Proto-devnet (`--profile devnet`): 3 block-producing pools with tx-generator
2. ImmDB mock (`--profile immdb`): upstream/node0/downstream with immdb-server

These are separate test environments and should not be run together.

## Architecture

### Proto-Devnet (`--profile devnet`)

3 block-producing pool nodes in a full mesh topology (each pool connects to
every other pool) with transaction load:

```
┌─────────┐     ┌─────────┐     ┌─────────┐
│  pool1  │◄───►│  pool2  │◄───►│  pool3  │
│ :3001   │     │ :3002   │     │ :3003   │
└────┬────┘     └────┬────┘     └────┬────┘
     │               │               │
     └───────────────┼───────────────┘
                     │
              ┌──────┴──────┐
              │tx-generator │
              └──────┬──────┘
                     │
              ┌──────┴──────┐
              │  analysis   │
              └─────────────┘
```

| Service | IP Address | Port | Purpose |
|---------|------------|------|---------|
| pool1 | 172.28.0.10 | 3001 | Block producer with pool1 credentials |
| pool2 | 172.28.0.20 | 3002 | Block producer with pool2 credentials |
| pool3 | 172.28.0.30 | 3003 | Block producer with pool3 credentials |
| tx-generator | dynamic | - | Transaction load generator |
| analysis | dynamic | - | Metrics analysis and Antithesis assertions |

Features:
- Real block production with registered stake
- Fast 0.1s slots for rapid iteration
- Transaction load testing
- Mesh topology with full connectivity

### ImmDB Mock (--profile immdb)

Linear topology with immdb-server providing mock blocks:

```
┌──────────┐     ┌─────────┐     ┌────────────┐
│ upstream │────►│  node0  │────►│ downstream │
│ (immdb)  │     │         │     │            │
└──────────┘     └─────────┘     └────────────┘
```

| Service | IP Address | Port | Purpose |
|---------|------------|------|---------|
| upstream | 172.28.0.110 | 3001 | immdb-server block source |
| node0 | 172.28.0.120 | 3002 | Leios-enabled cardano-node |
| downstream | 172.28.0.130 | 3003 | Receiving cardano-node |
| analysis-immdb | dynamic | - | Metrics analysis |

## Quick Start

```bash
# Proto-devnet (3 block-producing pools)
docker compose --profile devnet up

# ImmDB mock setup
docker compose --profile immdb up

# Build images only
docker compose --profile devnet build
docker compose --profile immdb build

# Start in background
docker compose --profile devnet up -d

# View logs
docker compose --profile devnet logs -f

# Stop and clean up
docker compose --profile devnet down -v
```

## Usage

### Proto-Devnet Mode

```bash
docker compose --profile devnet up
```

### ImmDB Mock Mode

```bash
docker compose --profile immdb up
```

### With Observability Stack

```bash
# Proto-devnet with observability
docker compose --profile devnet --profile observability up

# ImmDB with observability
docker compose --profile immdb --profile observability up
```

Adds Prometheus, Loki, Alloy, and Grafana:

| Service | Port | Purpose |
|---------|------|---------|
| Prometheus | 9090 | Metrics collection |
| Loki | 3100 | Log aggregation |
| Grafana | 3000 | Dashboards |

Access Grafana at http://localhost:3000 (no login required).

### With WAN Emulation

```bash
ENABLE_WAN_EMULATION=true docker compose --profile devnet up
```

Enables network latency/bandwidth simulation using tc.

## Configuration

### Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| GIT_SHA | latest | Docker image tag |
| ENABLE_WAN_EMULATION | false | Enable network simulation |
| PRAOS_LATENCY_THRESHOLD_MS | 5000 | Latency threshold for assertions |
| CHECK_INTERVAL_SECONDS | 5 | Analysis check interval |
| INITIAL_WAIT_SECONDS | 30 | Wait before first analysis |

### WAN Emulation Variables (ImmDB profile)

| Variable | Default | Description |
|----------|---------|-------------|
| RATE_UP_TO_N0 | 10Mbps | Bandwidth upstream to node0 |
| DELAY_UP_TO_N0 | 200ms | Latency upstream to node0 |
| RATE_N0_TO_DOWN | 10Mbps | Bandwidth node0 to downstream |
| DELAY_N0_TO_DOWN | 200ms | Latency node0 to downstream |

### Genesis Configuration (Proto-Devnet)

Genesis parameters in `demo/proto-devnet/config/genesis/`:

| Parameter | Value | Description |
|-----------|-------|-------------|
| slotLength | 0.1s | Slot duration |
| activeSlotsCoeff | 0.05 | Active slot coefficient |
| securityParam | 5 | Security parameter (k) |
| epochLength | 500 | Slots per epoch |
| networkMagic | 164 | Network identifier |

## File Structure

```
antithesis/
├── docker-compose.yaml          # Main orchestration
├── Dockerfile.cardano-node-bp   # Block producer image (proto-devnet)
├── Dockerfile.cardano-node      # Leios node image (immdb)
├── Dockerfile.immdb-server      # ImmDB server image (immdb)
├── Dockerfile.analysis          # Analysis container image
├── analyse.py                   # Log parsing and metrics
├── entrypoint-analysis.py       # Analysis main loop
├── scripts/
│   ├── init-pool-node.sh        # Pool initialization (proto-devnet)
│   ├── run-pool-node.sh         # Pool runtime (proto-devnet)
│   ├── run-tx-generator.sh      # TX generator (proto-devnet)
│   ├── init-node0.sh            # Node0 initialization (immdb)
│   ├── init-downstream.sh       # Downstream initialization (immdb)
│   ├── init-upstream.sh         # Upstream initialization (immdb)
│   ├── run-cardano-node.sh      # Node runtime (immdb)
│   ├── run-upstream.sh          # Upstream runtime (immdb)
│   └── setup-wan-emulation.sh   # Network simulation
└── config/
    ├── prometheus.yml           # Prometheus scrape config
    ├── loki.yml                 # Loki configuration
    ├── alloy.river              # Alloy log collection
    └── grafana/                 # Grafana provisioning
```

## Volumes

| Volume | Profile | Purpose |
|--------|---------|---------|
| pool1-data | devnet | Pool1 node data |
| pool2-data | devnet | Pool2 node data |
| pool3-data | devnet | Pool3 node data |
| txgen-data | devnet | TX generator working directory |
| genesis-shared | devnet | Shared genesis files |
| upstream-data | immdb | Upstream immdb-server data |
| node0-data | immdb | Node0 data |
| downstream-data | immdb | Downstream node data |
| logs | both | Node log files for analysis |

## Verification

### Proto-Devnet

```bash
# Check all services are healthy
docker compose --profile devnet ps

# Verify blocks are being produced
docker compose --profile devnet logs pool1 | grep -i "AddedToCurrentChain"

# Check tx-generator
docker compose --profile devnet logs tx-generator

# View analysis output
docker compose --profile devnet logs analysis
```

### ImmDB Profile

```bash
# Check services
docker compose --profile immdb ps

# Verify upstream is serving blocks
docker compose --profile immdb logs upstream

# Check node0 is receiving
docker compose --profile immdb logs node0 | grep -i "AddedToCurrentChain"

# View analysis
docker compose --profile immdb logs analysis-immdb
```

## Antithesis Integration

The analysis container reports assertions to Antithesis SDK:

- always: Praos block diffusion p95 latency < threshold
- always: Praos blocks are received when created
- sometimes: Leios endorser blocks (EBs) are created

When running outside Antithesis, assertions are logged to stdout.

## Troubleshooting

### Pools not connecting (proto-devnet)

Check topology configuration:
```bash
docker compose --profile devnet exec pool1 cat /data/topology.json
```

### No blocks being produced (proto-devnet)

Verify genesis timestamp is recent:
```bash
docker compose --profile devnet exec pool1 cat /data/shelley-genesis.json | jq '.systemStart'
```

### Upstream not serving blocks (immdb)

Check schedule file exists:
```bash
docker compose --profile immdb exec upstream cat /data/schedule.json
```

### Build issues

Clean rebuild:
```bash
docker compose --profile devnet down -v
docker compose --profile devnet build --no-cache
docker compose --profile devnet up
```

## Development

### Rebuilding a single service

```bash
docker compose --profile devnet build pool1
docker compose --profile devnet up -d pool1
```

### Accessing a container

```bash
docker compose --profile devnet exec pool1 bash
```

## Related Documentation

- [Proto-Devnet Demo](../demo/proto-devnet/README.md)
- [2025-11 Demo](../demo/2025-11/README.md)
- [Ouroboros Leios Specification](https://leios.cardano-scaling.org)
- [Antithesis Documentation](https://antithesis.com/docs/)
