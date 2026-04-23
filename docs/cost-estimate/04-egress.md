# Egress cost estimation per node

Network egress is metered for most cloud providers even though many have some
monthly budget that is free. In the following example calculation, we try to be
as precise as possible given today's
[p2p default configuration](https://book.world.dev.cardano.org/environments/mainnet/config.json)
of the node.

All values use confirmed throughput in TxkB/s (transaction kilobytes per
second reaching the ledger). Seconds per month: 2,628,000 (30.4167 days).

## Network Topology

The Cardano relay network is asymmetric. A typical relay node has:

- **~20 outbound (upstream) connections**: connections the relay initiates to
  other relays; blocks, EB bodies, votes, and certificates are pulled from these
- **~100 inbound (downstream) connections**: connections initiated by other
  relays and clients; headers are pushed to all subscribers here, and txs are
  submitted from this direction

Different traffic types have different directions and different fetch models:

| Traffic type         | Flows      | Serves to (egress)                                        |
|----------------------|------------|-----------------------------------------------------------|
| Headers (RB/EB)      | Downstream | All ~100 inbound ChainSync subscribers                    |
| Block bodies (RB/EB) | Downstream | Fraction of inbound: 100 × (1/20 upstreams) ≈ **5 peers** |
| Tx diffusion         | Upstream   | 20 upstream peers × (2/20 fetch ratio) = **2 peers**      |
| Votes                | Downstream | ~2 peers (spanning-tree × 2 redundancy)                   |

> [!Note]
>
> The block/EB body peer count (5) derives from: each of 100 inbound peers has
> ~20 upstream sources and requests from ~1 of them on average → 100 × 1/20 = 5.
> Tx diffusion flows upstream (clients → relays → block producers): we serve our
> 20 outbound (upstream) peers. Each of those peers fetches txs from 2 of its
> ~20 downstream connections at a time → our selection probability = 2/20 = 10%
> → expected peers served = 20 × 10% = **2**. Same structure as block bodies
> (downstream), just mirrored: 100 inbound × (1/20) = 5 vs 20 outbound × (2/20) = 2.
>
> The **2-peer fetch** reflects TxSubmission V2 (`txInflightMultiplicity = 2` in
> `TxDecisionPolicy`), which deliberately downloads each tx from 2 upstream peers
> simultaneously for redundancy. TxSubmission V1 (currently deployed) uses
> announce-to-all with deduplication, which propagates each tx body along a
> spanning tree (~1 effective send per node). CIP-164 simulations use V1-style
> gossip and give ~2× lower tx egress; V2 is the target protocol for both
> Praos and Leios.

## Ouroboros Praos

The following numbers are from Cardano Mainnet, April 2025.

| Component  | Size (bytes) | Size (KiB) |
|------------|--------------|------------|
| Header (H) | 1,024        | 1          |
| Body (B)   | 90,112       | 88         |

### Blocks per Month

| Parameter               | Value       | Formula                                 |
|-------------------------|-------------|-----------------------------------------|
| Active slot coefficient | 0.05        | Protocol parameter                      |
| Seconds per month       | 2,628,000   | $30.4167 \times 24 \times 60 \times 60$ |
| **Blocks per month**    | **131,400** | $0.05 \times 2{,}628{,}000$             |

### Praos Relay Node Egress Calculation

1. **Tx mempool diffusion** (2 peers):

   Transactions flow upstream (clients → relays → block producers). We serve
   our ~20 upstream peers; each fetches from 2 of its ~20 downstreams → 2 peers:
   $4{,}500 \times 2 \times 2{,}628{,}000 \approx 22.0 \text{ GiB}$

2. **Header egress** (100 inbound downstream peers):
   $131{,}400 \times 1{,}024 \times 100 \approx 12.5 \text{ GiB}$

3. **Block body egress** (5 peers — fraction of inbound):
   $131{,}400 \times 90{,}112 \times 5 \approx 55.1 \text{ GiB}$

   Block bodies contain the same transactions already gossiped via the mempool
   — the full tx data is **re-transmitted a second time** as part of block
   propagation. Leios avoids this by carrying only 32-byte hash references in
   EBs; the confirmed tx data is never re-sent as part of block propagation.

4. **Total relay egress**: $\approx 89.6 \text{ GiB/month}$

## Ouroboros Leios

In Linear Leios (CIP-164), transactions are gossiped via the mempool. EBs carry
only 32-byte tx hash references; actual transaction data is propagated
independently as transactions arrive. Only transactions in certified EBs count
as confirmed throughput.

EBs are produced at the same rate as Praos blocks (0.05/s), but only those
produced sufficiently before the next RB are certifiable. An EB needs no block
to be produced in the following 14-slot voting window:

$$P(\text{EB certified}) = (1 - 0.05)^{14} = 0.95^{14} \approx 0.4877 \approx 0.48$$

Non-certified EBs still generate EB body traffic: their 32-byte tx hash
references are gossiped whether or not the EB is eventually certified, because
nodes do not know in advance which EBs will be certified. A confirmed transaction
is therefore expected to appear in $1/P(\text{cert}) \approx 2.08$ EB bodies
before one of those EBs is certified, scaling EB body egress accordingly.

In the asymptotic steady state we assume tx diffusion reaches all nodes before
any EB is certified, so no separate "missing tx fetch" traffic is needed — the
normal tx diffusion already covers EB closure.

### Block Size Components

| Component                     | Size (bytes) | Size (KiB) |
| ----------------------------- | ------------ | ---------- |
| EB Body (32 B per tx ref)     | varies       | varies     |
| Vote (per voter, per EB)      | 164          | 0.2        |
| RB Header (doubles as EB hdr) | 1,024        | 1          |
| RB Body (certificate)         | 8,000        | 8          |

> [!Note]
>
> In the current CIP-164 implementation, the RB header doubles as the EB header.
> One 1,024-byte combined header is produced per block slot; there is no separate
> EB header message.

### Protocol Rates

| Parameter             | Value                  | Source                                                                                    |
| --------------------- | ---------------------- | ----------------------------------------------------------------------------------------- |
| EB/RB rate            | 0.05/s                 | Active slot coefficient                                                                   |
| EBs per month         | 131,400                | $0.05 \times 2{,}628{,}000$                                                               |
| Votes per EB          | 600                    | `vote-generation-probability`; wFA+LS committee                                           |
| Vote size             | 164 bytes              | `vote-size-bytes`; per voter per EB                                                       |
| P(EB certified)       | ≈ 0.48                 | $(1-0.05)^{14} = 0.95^{14} \approx 0.4877$: probability no block in 14-slot voting window |
| Certified EBs/month   | 63,072                 | $0.05 \times 0.48 \times 2{,}628{,}000$                                                   |

### Egress Formulas

1. **Transaction Data Egress** (dominant — scales with TxkB/s):

   Transactions flow upstream (clients → relays → block producers). We serve
   our ~20 upstream peers; each fetches from 2 of its ~20 downstream connections
   → 20 × (2/20) = 2 peers on average:

   $$E_{\text{tx}} = \text{TxkB/s} \times 1{,}000 \times 2 \times T_{\text{month}}$$

2. **Vote Egress** (fixed — independent of throughput):

   Votes propagate downstream (toward the next block producer) using a pull-based
   mini-protocol with deduplication. We model ~2× spanning-tree redundancy for a
   typical relay:

   $$E_{\text{votes}} = 600 \times 164 \times 0.05 \times 2 \times 2{,}628{,}000 \approx 24.1 \text{ GiB}$$

3. **EB Body Egress** (tx hash references — scales with TxkB/s):

   Each confirmed tx appears in $1/P(\text{cert}) \approx 2.08$ EB bodies on
   average (non-certified EBs also gossip their tx hashes). EB bodies are
   fetched by the same fraction of inbound peers as Praos block bodies (5 peers):

   $$E_{\text{eb-body}} = R_{\text{eb}} \times T_{\text{month}} \times \frac{\text{TxkB/s} \times 1{,}000}{1{,}500 \times 0.05} \times 32 \times 5 \times \frac{1}{P(\text{cert})}$$

   Simplifying: $E_{\text{eb-body}} \approx \text{TxkB/s} \times 0.5438 \text{ GiB/month}$

4. **RB Header Egress** (combined RB/EB header, fixed):

   $$E_{\text{rb-hdr}} = 131{,}400 \times 1{,}024 \times 100 \approx 12.5 \text{ GiB}$$

5. **RB Body Egress** (certificate, certified RBs only):

   Only certified RBs carry a certificate. Fetched by the same fraction of
   inbound peers as Praos block bodies (5 peers). Using $N_{\text{cert}} = 63{,}072$/month:

   $$E_{\text{rb-body}} = 63{,}072 \times 8{,}000 \times 5 \approx 2.35 \text{ GiB}$$

### Fixed Overhead Summary

| Component       | Monthly Egress | Notes                                           |
|-----------------|----------------|-------------------------------------------------|
| Vote traffic    | 24.1 GiB       | 600 voters × 164 B × 0.05 EB/s × 2 peers        |
| RB/EB headers   | 12.5 GiB       | To all ~100 inbound downstream peers            |
| RB cert bodies  | 2.35 GiB       | 5 peers (same model as block bodies, 63,072/mo) |
| **Fixed total** | **38.95 GiB**  | Independent of throughput                       |

### Monthly Egress at Different Confirmed Throughputs

| TxkB/s        | Tx Data     | Block/EB Bodies | Fixed Overhead  | **Total**       | vs Praos  |
| ------------- | ----------- | --------------- | --------------- | --------------- | --------- |
| 4.5 (Praos)   | 22.0 GiB    | 55.1 GiB (blk)  | 12.5 GiB (hdr)  | **89.6 GiB**    | —         |
| 5             | 24.5 GiB    | 2.72 GiB (EB)   | 38.95 GiB       | **66.2 GiB**    | **-26%**  |
| 50            | 245.0 GiB   | 27.19 GiB       | 38.95 GiB       | **311.1 GiB**   | +247%     |
| 100           | 489.6 GiB   | 54.38 GiB       | 38.95 GiB       | **582.9 GiB**   | +550%     |
| 200           | 979.1 GiB   | 108.75 GiB      | 38.95 GiB       | **1,126.8 GiB** | +1,157%   |
| 300           | 1,468.7 GiB | 163.13 GiB      | 38.95 GiB       | **1,670.8 GiB** | +1,764%   |

> [!Note]
>
> - **Praos row**: tx mempool diffusion (22.0 GiB, 2 peers) + block body
>   re-transmission of the same txs (55.1 GiB, 5 peers) + headers (12.5 GiB,
>   100 peers) = 89.6 GiB. Every confirmed transaction is sent **twice** in Praos.
> - **Leios at 5 TxkB/s is ~26% cheaper than Praos**: eliminating block body
>   re-transmission (55.1 GiB) more than covers the fixed Leios overhead
>   (38.95 GiB). This advantage shrinks as throughput grows and tx data dominates.
> - EB body egress is scaled by 1/P(cert) ≈ 2.08× (non-certified EBs gossip their
>   tx hashes) and uses 5 peers — the same fetch model as Praos block bodies
> - Vote overhead (24.1 GiB/month) is fixed; votes flow downstream toward the
>   next block producer; 2-peer model reflects spanning-tree × 2 redundancy
> - "vs Praos" compares against Praos relay egress of 89.6 GiB/month

### Traffic Components at 200 TxkB/s

| Component        | Egress      | % of Total |
| ---------------- | ----------- | ---------- |
| Tx Data          | 979.1 GiB   | 86.9%      |
| EB Bodies        | 108.75 GiB  | 9.6%       |
| Vote Traffic     | 24.1 GiB    | 2.1%       |
| RB/EB Headers    | 12.5 GiB    | 1.1%       |
| RB Cert Bodies   | 2.35 GiB    | 0.2%       |

At 200 TxkB/s, transaction data dominates (87%) but EB bodies (9.7%) are
now significant — they carry the 1/P(cert) overhead of non-certified EBs
and are served to 5 downstream peers just like Praos block bodies.

### Monthly Cost by Cloud Provider ($)

Egress is billed per GB (10⁹ bytes); 1 GiB ≈ 1.074 GB.

| Provider      | Price/GB | Free (GB)    | 4.5 (Praos) | 5 TxkB/s | 50 TxkB/s | 100 TxkB/s | 200 TxkB/s | 300 TxkB/s |
| ------------- | -------- | ------------ | ----------- | --------- | --------- | ---------- | ---------- | ---------- |
| AWS           | $0.090   | 100          | $0.00       | $0.00     | $21.07    | $47.34     | $99.92     | $152.50    |
| GCP           | $0.120   | 0            | $11.54      | $8.53     | $40.09    | $75.12     | $145.22    | $215.33    |
| Azure         | $0.087   | 100          | $0.00       | $0.00     | $20.37    | $45.76     | $96.59     | $147.42    |
| Railway       | $0.100   | 0            | $9.62       | $7.11     | $33.41    | $62.60     | $121.02    | $179.44    |
| Alibaba Cloud | $0.074   | 10           | $6.38       | $4.52     | $23.98    | $45.59     | $88.81     | $132.05    |
| DigitalOcean  | $0.010   | 1,000        | $0.00       | $0.00     | $0.00     | $0.00      | $2.10      | $7.94      |
| Oracle Cloud  | $0.0085  | 10,240       | $0.00       | $0.00     | $0.00     | $0.00      | $0.00      | $0.00      |
| Linode        | $0.005   | 1,024        | $0.00       | $0.00     | $0.00     | $0.00      | $0.93      | $3.85      |
| Hetzner       | $0.0011  | 1,024        | $0.00       | $0.00     | $0.00     | $0.00      | $0.20      | $0.85      |
| UpCloud       | $0.000   | 1,024–24,576 | $0.00       | $0.00     | $0.00     | $0.00      | $0.00      | $0.00      |

> [!Note]
>
> - Prices are for US regions and may vary by location
> - Free allowances vary by plan tier; values shown are typical baseline
>   included transfer for standard instances
> - Both Praos and Leios at 5 TxkB/s fall within AWS/Azure 100 GB free tiers
> - DigitalOcean/Linode/Hetzner remain very cheap even at 200 TxkB/s due to
>   generous included transfer

### Data Egress Cost Sources

| Provider     | Price/GB | Source                                                 | Last Updated |
| ------------ | -------- | ------------------------------------------------------ | ------------ |
| AWS          | $0.090   | https://aws.amazon.com/ec2/pricing/                    | 2023         |
| GCP          | $0.120   | https://cloud.google.com/vpc/pricing                   | Feb 2025     |
| Azure        | $0.087   | https://azure.microsoft.com/pricing/details/bandwidth/ | Dec 2024     |
| DigitalOcean | $0.010   | https://www.digitalocean.com/pricing/                  | Apr 2025     |
| Linode       | $0.005   | https://www.linode.com/pricing/                        | Apr 2023     |
| Hetzner      | $0.0011  | https://www.hetzner.com/cloud/pricing                  | Apr 2026     |

Note: Prices may vary by region and volume. Some providers offer free tiers or
volume discounts not reflected in these base rates.
