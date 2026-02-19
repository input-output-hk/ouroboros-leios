# Mempool Simulation

Discrete-event simulation of Cardano mempool propagation with adversarial front-running.

Simulates how transactions propagate through a network of nodes, where some nodes are adversaries that front-run honest transactions by replacing them with their own versions.

## Simulation Model

This section documents exactly what the simulator does and does not model, including all simplifications relative to the real Cardano protocol. The goal is transparency: readers should be able to assess which results transfer to a real deployment and which are artifacts of the model.

### Network Topology

| Aspect | Simulation | Real Cardano | Impact |
|--------|-----------|--------------|--------|
| Graph structure | Random regular directed graph (edge-swap randomised ring lattice) | Ouroboros P2P topology with hot/warm/cold peer buckets, churn governor | Sim graph is more uniform; real topology has heterogeneous degree and clustering |
| Link properties | All links share identical latency and bandwidth | Links vary by geography, ISP, and node capacity | Sim underestimates variance in propagation times |
| Peer churn | Optional: random edge swaps at fixed interval with uniform probability | Continuous churn governed by peer selection policy and network events | Sim churn is coarser and not policy-driven |
| Adversary insertion | Adversary rewires existing honest edges (upstream) and adds new edges (downstream) | Adversary must discover and connect through P2P layer | Sim gives adversary easier/faster insertion |

### Link Delay Model

Every message between two nodes incurs a delay computed as:

```
delivery_time = send_time + latency + (80 + message_size) / bandwidth + jitter
```

| Component | Value | Notes |
|-----------|-------|-------|
| `latency` | Configurable (default 50 ms viz, 100 ms CLI) | Fixed per-link; no per-hop variation |
| Overhead | 80 bytes | Constant protocol framing per message |
| Bandwidth | Configurable (default 12.5 MB/s viz, 1.25 MB/s CLI) | Shared capacity not modeled — each message gets full bandwidth independently |
| Jitter | Uniform random 0–150 ns | Negligibly small; placeholder for future enhancement |

**Simplification: no queuing or contention.** Each link transmits every message at full bandwidth independently. In reality, multiple concurrent transfers on the same link would compete for bandwidth, increasing effective delay. This means the simulation is **optimistic** about propagation times under high load.

### Transaction Propagation (Praos Gossip)

Transactions follow a 3-step offer/request/send protocol:

```
  Node A                    Node B
    │                         │
    │──── OfferTx (32 B) ───→│   Step 1: announce tx ID
    │                         │
    │←── RequestTx (32 B) ───│   Step 2: request full body
    │                         │
    │──── SendTx (tx_size) ──→│   Step 3: send full tx
    │                         │
```

**Total latency per hop:**
```
3 × latency + (2 × (80 + 32) + (80 + tx_size)) / bandwidth
= 3 × latency + (304 + tx_size) / bandwidth
```

| Simplification | Description | Impact |
|----------------|-------------|--------|
| No multiplexing | Each tx offer/request/send is independent; no mini-protocol mux overhead | Slightly optimistic — real mux adds framing and scheduling |
| No tx validation delay | Accepting a tx into the mempool is instantaneous | Optimistic — real nodes run ledger validation (script execution, UTxO checks) |
| First-offer wins | A node requests from whichever peer offers first | Matches real protocol (first valid offer triggers request) |
| Propagation direction | Node offers to both upstream and downstream peers after accepting | Matches Cardano gossip (bidirectional announcement) |

### Block Production and Diffusion

| Aspect | Simulation | Real Cardano | Impact |
|--------|-----------|--------------|--------|
| Block timing | Poisson process with configurable mean interval | Slot-based with VRF lottery (geometric distribution) | Similar in aggregate; sim doesn't model slot boundaries |
| Block content | Greedy fill from producer's mempool up to `block_size` | Ordered by fee, priority, script budget | Sim doesn't model fee markets or ordering strategy |
| Block diffusion | Single `DiffuseBlock` message carrying full block payload | Header-first diffusion: header → validate → body request | Sim is **optimistic** — real protocol adds round trips for header validation |
| Block propagation delay | `latency + (80 + block_payload_size) / bandwidth` | Multiple round trips for header + body + validation | Significantly faster in sim |
| Chain selection | Not modeled — blocks simply apply globally | Ouroboros chain selection with rollbacks | Sim can't model forks or competing chains |
| Tx removal on block | Immediately removed from ALL nodes' mempools on production; removed per-node on diffusion | Removed per-node as block arrives and is validated | Production-time global removal is optimistic for the producer; per-node diffusion-time removal is realistic |

### Endorser Block (Leios EB) Model

When EB mode is enabled, endorser blocks are produced alongside regular blocks. The EB model has several significant simplifications:

#### EB Production and Diffusion

```
  Producer                  Peer
    │                        │
    │── DiffuseEB (32B×N) ──→│   EB header = list of tx ID references
    │                        │
```

**EB size on the wire:** `32 × txRefCount` bytes (just the tx ID hashes).

| Simplification | Description | Impact |
|----------------|-------------|--------|
| EB timing | Produced probabilistically alongside each block (`ebAnnouncementRate`) | Real Leios has a separate EB production schedule independent of blocks |
| EB content | References all txs in producer's mempool up to `ebSize` | Real EB construction may be more selective |
| Certification | Instant coin flip (`ebCertificationRate`) at production time | Real certification involves a voting protocol among multiple nodes over time |
| Uncertified EB penalty | Next block after an uncertified EB is forced empty | Placeholder — real penalty mechanism TBD in Leios spec |
| EB-to-block pipeline | Not modeled — EBs and blocks interact only through the empty-block penalty | Real Leios has Input Blocks → Endorser Blocks → Voting → Ranking Blocks pipeline |

#### EB Transaction Fetching

When a node receives an EB referencing transactions it hasn't seen, it fetches them. This uses a **simplified 2-step protocol** instead of the 3-step gossip:

```
  Node A                    Node B
    │                         │
    │──── FetchEBTx (32 B) ──→│   Request tx by ID (skips offer step)
    │                         │
    │←── SendEBTx (tx_size) ──│   Peer sends full tx body
    │                         │
```

**Total latency per fetch:**
```
2 × latency + ((80 + 32) + (80 + tx_size)) / bandwidth
= 2 × latency + (192 + tx_size) / bandwidth
```

| Simplification | Description | Impact |
|----------------|-------------|--------|
| Omniscient peer selection | Node checks global `inMempool` bitmap to find a peer that has the tx, then fetches from the first match | **Optimistic** — real nodes don't know which peers have which txs; would need to broadcast requests or use prior announcements as hints |
| Single-source fetch | Only fetches from one peer (`break` after first match) | Optimistic — no retry on failure, no fan-out |
| No EB validation delay | EB is accepted and triggers fetches immediately | Real nodes would validate EB structure before acting on it |
| Fetched txs enter normal mempool | `SendEBTx` calls `acceptTx`, which triggers full gossip propagation | This is intentional — creates backpressure that defends against adversary front-running |

### Adversary Model

| Aspect | Simulation | Real Cardano | Impact |
|--------|-----------|--------------|--------|
| Front-running | Every honest tx is replaced with an adversarial variant | In reality, only some txs (arbitrage, order book entries) are exploitable |
| Adversarial tx creation | Instant (plus configurable delay) with same size as original | Real front-running requires analysis and may change tx size |
| Adversarial propagation | Uses same gossip protocol but with added delay | Same mechanism; delay models computation time |
| Conflict detection | Bitmap-based: first-seen wins per node | Real Cardano uses UTxO conflict detection |
| Adversary knowledge | Adversary sees txs arriving at its node | Same as real — no additional oracle |

### Transaction Load Model

Transaction injection uses a **byte-budget** approach:

```
total_bytes = txLoad_KBps × 1024 × duration
tx_count = total_bytes / txSize
```

| Simplification | Description | Impact |
|----------------|-------------|--------|
| Uniform tx size | All txs have identical size | Real Cardano has tx sizes ranging from ~250 B to ~16 KB |
| Uniform random timing | Each tx injected at `uniform(0, duration)` | Real tx arrival is bursty and time-varying |
| Uniform random node | Each tx submitted to a random honest node | Real submissions concentrate at stake pool operators and popular endpoints |
| Safety cap | 50,000 max transactions | Prevents runaway memory at high load settings |

Reference load values:
- **Current Cardano (Praos):** ~4.5 KB/s
- **Leios target:** ~140–300 KB/s

### Mempool Model

| Aspect | Simulation | Real Cardano | Impact |
|--------|-----------|--------------|--------|
| Capacity | Fixed bytes (default: 2 × block size) | Fixed bytes, but with more nuanced admission policies | Similar |
| Admission | Size check only (`canFitTx`) | Ledger validation, fee check, script budget | Sim is optimistic — no validation delay |
| Eviction | None — if mempool is full, tx is silently dropped | Real mempool may evict low-fee txs to make room | Sim may undercount propagation at high load |
| Byte tracking | Counter-based (no actual tx storage) | Full tx bodies stored | Sim is memory-efficient but can't model content-dependent policies |

### What Is NOT Modeled

The following aspects of real Cardano are entirely absent from the simulation:

1. **Ledger rules** — No UTxO model, no script execution, no fees
2. **Consensus** — No slot leadership schedule, no VRF, no chain selection, no rollbacks
3. **Block validation** — Blocks are accepted instantly with no verification delay
4. **Network layer** — No TCP, no connection management, no multiplexing overhead
5. **Memory/CPU constraints** — Nodes process events instantly with unlimited resources
6. **Geographic distribution** — All links have identical properties
7. **Multiple transaction types** — Only simple value transfers (no scripts, no metadata)
8. **Stake distribution** — Block production is uniform random, not stake-weighted

## Setup

```bash
nix develop  # or install Node.js 18+
npm install
```

## Usage

```bash
npm run cli -- [options]
```

### Options

```
Usage: mempool-sim [options]

Scaled bitmap memory pool simulator (Praos + Leios)

Options:
  -V, --version                    output the version number
  -n, --nodes <number>             Number of honest nodes (default: "50")
  -d, --degree <number>            Node connectivity degree (default: "6")
  -b, --block <bytes>              Block size in bytes (default: "90000")
  -l, --latency <seconds>          Network latency in seconds (default: "0.1")
  -w, --bandwidth <bps>            Bandwidth in bytes per second (default: "1250000")
  -a, --adversaries <number>       Number of adversary nodes (default: "2")
  --adversary-degree <number>      Adversary connectivity degree (default: "18")
  --adversary-delay <seconds>      Adversary front-run delay (default: "0.002")
  -t, --tx-load <kbps>             Transaction load in KB/s (default: "100")
  --tx-size <bytes>                Uniform tx size in bytes (default: "512")
  --tx-duration <seconds>          Duration over which to inject txs (default: "20")
  --slot-duration <seconds>        Block slot duration (default: "20")
  -s, --slots <number>             Number of slots to simulate (default: "10")
  --log-level <level>              Log level (choices: "fatal", "error", "warn", "info",
                                   "debug", "trace", default: "info")
  --log-target <target>            Log target (choices: "pino-pretty", "pino/file",
                                   default: "pino-pretty")
  --eb                             Enable endorser blocks (Leios) (default: false)
  --eb-size <bytes>                Endorser block size in bytes (default: "10000000")
  --eb-announcement-rate <rate>    EB announcement probability 0-1 (default: "1.0")
  --eb-certification-rate <rate>   EB certification probability 0-1 (default: "1.0")
  -h, --help                       display help for command
```

### Examples

Basic run with defaults:
```bash
npm run cli
```

Small network test:
```bash
npm run cli -- -n 20 -a 1 --adversary-degree 6 -t 10
```

High throughput (Leios-range load):
```bash
npm run cli -- -n 100 -a 5 -t 200 --tx-size 512
```

With endorser blocks:
```bash
npm run cli -- -n 50 -a 2 -t 100 --eb --eb-announcement-rate 0.5
```

## How it works

1. Generates a random regular graph of honest nodes
2. Adds adversary nodes with configurable connectivity
3. Injects transactions at random honest nodes according to the byte-budget load model
4. Transactions propagate via 3-step offer/request/send gossip protocol
5. Adversary nodes front-run honest txs by creating adversarial versions
6. Blocks are produced via Poisson process; transactions are removed from mempools
7. If EB enabled: endorser blocks reference mempool txs and trigger 2-step fetch for unknown txs
8. Reports final statistics: honest vs adversarial transaction fractions, poisoning analysis

## Output

The simulation logs:
- Network configuration
- Topology (node connections)
- Per-node mempool state (at debug level)
- Block production and fill statistics
- Poisoning analysis (p_poison vs theoretical predictions)
- Final statistics: honest vs adversarial transaction fractions
