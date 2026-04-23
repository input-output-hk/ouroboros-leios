# Egress cost estimation per node

Network egress is metered for most cloud providers even though many have some
monthly budget that is free. In the following example calculation, we try to be
as precise as possible given today's
[p2p default configuration](https://book.world.dev.cardano.org/environments/mainnet/config.json)
of the node.

All values use confirmed throughput in TxkB/s (transaction kilobytes per
second reaching the ledger). Seconds per month: 2,628,000 (30.4167 days).

## Ouroboros Praos

We start with Ouroboros Praos to have a baseline. The following numbers are from
Cardano Mainnet, April 2025.

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

### Network Topology Assumptions

For our calculations, we consider two types of nodes:

- Relay nodes: Connect to other relays
- Edge nodes: Connect to relay nodes but not to other edge nodes

We make the following assumptions about the network:

- [Default p2p configuration](https://book.world.dev.cardano.org/environments/mainnet/config.json):
  20 (upstream) peers per relay node
- ~3 edge nodes per relay node
- Block propagation model:
  - Headers: Propagated to all peers (20 relay + 3 edge = 23 peers)
  - Bodies: Requested by ~10% of relay peers (2 out of 20) + all 3 edge peers

### Praos Relay Node Egress Calculation

1. **Tx mempool diffusion** (5 peers — 2 relay + 3 edge):

   Transactions are gossiped through the mempool before block production,
   using the same model as Leios transaction gossip:
   $4{,}500 \times 5 \times 2{,}628{,}000 \approx 55.1 \text{ GiB}$

2. **Header egress** (23 peers):
   $131{,}400 \times 1{,}024 \times 23 \approx 2.88 \text{ GiB}$

3. **Block body egress** (5 peers — 2 relay + 3 edge):
   $131{,}400 \times 90{,}112 \times 5 \approx 55.1 \text{ GiB}$

   Block bodies contain the same transactions already gossiped via the mempool
   — the full tx data is **re-transmitted a second time** as part of block
   propagation. Leios avoids this by carrying only 32-byte hash references in
   EBs; the confirmed tx data is never re-sent.

4. **Total relay egress**: $\approx 113.1 \text{ GiB/month}$

## Ouroboros Leios

In Linear Leios (CIP-164), transactions are gossiped via the mempool. EBs carry
only 32-byte tx hash references; actual transaction data is propagated
independently as transactions arrive. Only transactions in certified EBs count
as confirmed throughput.

EBs are produced at the same rate as Praos blocks (0.05/s), but only those
produced sufficiently before the next RB are certifiable. An EB needs no block
to be produced in the following 14-slot voting window:

$$P(\text{EB certified}) = (1 - 0.05)^{14} = 0.95^{14} \approx 0.4877 \approx 0.48$$

Non-certified EBs still generate EB body and vote traffic: their 32-byte tx hash
references are gossiped whether or not the EB is eventually certified, because
nodes do not know in advance which EBs will be certified. A confirmed transaction
is therefore expected to appear in $1/P(\text{cert}) \approx 2.08$ EB bodies
before one of those EBs is certified, scaling EB body egress accordingly.

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

### Network Topology Assumptions

Same assumptions as Praos:

- 20 relay peers + 3 edge nodes per relay
- Transaction data propagation (mempool gossip):
  - Bodies requested by 2 relay peers + 3 edge peers = **5 peers**
  - (Same model as Praos block body propagation)
- RB headers (combined with EB header): propagated to all 23 peers
- RB cert bodies: requested by 2 relay peers (certified RBs only)
- Votes: gossiped to ~2 peers — see reasoning below

### Egress Formulas

1. **Transaction Data Egress** (dominant — scales with TxkB/s):

   Transactions are gossiped once per node when they arrive. Each tx body is
   served to ~5 requesting peers (2 relay + 3 edge):

   $$E_{\text{tx}} = \text{TxkB/s} \times 1{,}000 \times 5 \times T_{\text{month}}$$

2. **Vote Egress** (fixed — independent of throughput):

   Votes are gossiped peer-to-peer using a pull-based mini-protocol with
   deduplication. To estimate per-node egress, consider two bounds:

   - **Lower bound (spanning tree)**: each vote traverses exactly N−1 edges
     across the 10k-node network, so per node it is forwarded to 1 peer on
     average — identical to the original 1-peer model (12 GiB/month).
   - **Upper bound (full gossip fanout)**: every node forwards to all its
     connected peers before deduplication; with degree ~20 this is 10× the
     spanning-tree cost.

   In practice, the pull-based mini-protocol's "I have / give me" exchange
   eliminates most redundant transfers. For a typical relay, the effective
   redundancy is ~2× the spanning tree (each vote reaches two independent
   downstream paths before the deduplication kicks in). High-stake hub nodes
   with many inbound connections carry proportionally more. We use **2 peers**:

   $$E_{\text{votes}} = N_{\text{votes/EB}} \times V_{\text{size}} \times R_{\text{eb}} \times 2 \times T_{\text{month}}$$

   $$E_{\text{votes}} = 600 \times 164 \times 0.05 \times 2 \times 2{,}628{,}000 = 25.86 \times 10^9 \text{ bytes} \approx 24.1 \text{ GiB}$$

3. **EB Body Egress** (tx hash references — scales with TxkB/s):

   Each confirmed tx is expected to appear in $1/P(\text{cert}) \approx 2.08$ EB bodies
   (non-certified EBs still gossip their tx hashes). EB body size per EB =
   $\frac{\text{TxkB/s} \times 1{,}000}{1{,}500 \times 0.05} \times 32$ bytes.

   $$E_{\text{eb-body}} = R_{\text{eb}} \times T_{\text{month}} \times \frac{\text{TxkB/s} \times 1{,}000}{1{,}500 \times 0.05} \times 32 \times 2 \times \frac{1}{P(\text{cert})}$$

   Simplifying: $E_{\text{eb-body}} \approx \text{TxkB/s} \times 0.2175 \text{ GiB/month}$

4. **RB Header Egress** (combined RB/EB header, fixed):

   $$E_{\text{rb-hdr}} = 131{,}400 \times 1{,}024 \times 23 = 3{,}094{,}732{,}800 \text{ bytes} \approx 2.88 \text{ GiB}$$

5. **RB Body Egress** (certificate, certified RBs only):

   Only certified RBs carry a certificate. Using $N_{\text{cert}} = 63{,}072$/month:

   $$E_{\text{rb-body}} = 63{,}072 \times 8{,}000 \times 2 = 1{,}009{,}152{,}000 \text{ bytes} \approx 0.94 \text{ GiB}$$

### Fixed Overhead Summary

| Component       | Monthly Egress | Notes                                            |
|-----------------|----------------|--------------------------------------------------|
| Vote traffic    | 24.1 GiB       | 600 voters × 164 B × 0.05 EB/s × 2 peers         |
| RB/EB headers   | 2.88 GiB       | To all 23 peers (RB header doubles as EB header) |
| RB cert bodies  | 0.94 GiB       | To 2 relay peers (certified RBs only, 63,072/mo) |
| **Fixed total** | **27.9 GiB**   | Independent of throughput                        |

### Monthly Egress at Different Confirmed Throughputs

| TxkB/s      | Tx Data     | Block Bodies | EB Bodies | Fixed Overhead | **Total**       | vs Praos |
|-------------|-------------|--------------|-----------|----------------|-----------------|----------|
| 4.5 (Praos) | 55.1 GiB    | 55.1 GiB     | —         | 2.88 GiB (hdr) | **113.1 GiB**   | —        |
| 5           | 61.2 GiB    | —            | 1.09 GiB  | 27.9 GiB       | **90.2 GiB**    | **-20%** |
| 50          | 612.2 GiB   | —            | 10.88 GiB | 27.9 GiB       | **651.0 GiB**   | +476%    |
| 100         | 1,224.4 GiB | —            | 21.75 GiB | 27.9 GiB       | **1,274.1 GiB** | +1,027%  |
| 200         | 2,448.7 GiB | —            | 43.50 GiB | 27.9 GiB       | **2,520.1 GiB** | +2,128%  |
| 300         | 3,673.1 GiB | —            | 65.25 GiB | 27.9 GiB       | **3,766.3 GiB** | +3,230%  |

> [!Note]
>
> - The 4.5 (Praos) row now includes tx mempool diffusion (55.1 GiB) + block
>   body re-transmission (55.1 GiB) + headers (2.88 GiB) = 113.1 GiB total.
>   In Praos, every confirmed transaction is sent **twice**: once via mempool
>   gossip and once embedded in the block body.
> - **Leios at 5 TxkB/s is ~20% cheaper than Praos** in egress: it eliminates
>   the block body re-transmission, replacing it with 32-byte EB hash references.
>   The savings (55 GiB) outweigh the fixed Leios overhead (votes + certs,
>   27.9 GiB) at near-Praos throughput.
> - EB body egress is scaled by 1/P(cert) ≈ 2.08× because non-certified EBs
>   still gossip their tx hash references
> - Vote overhead (24.1 GiB/month) is fixed — 600 voters × 164 B × 0.05 EB/s
>   gossiped to ~2 peers (2× spanning-tree redundancy for a typical relay); hub
>   nodes with many inbound peers carry proportionally more
> - "vs Praos" compares against corrected Praos egress of 113.1 GiB/month

### Traffic Components at 200 TxkB/s

| Component      | Egress      | % of Total |
|----------------|-------------|------------|
| Tx Data        | 2,448.7 GiB | 97.2%      |
| EB Bodies      | 43.5 GiB    | 1.7%       |
| Vote Traffic   | 24.1 GiB    | 1.0%       |
| RB Headers     | 2.88 GiB    | 0.1%       |
| RB Cert Bodies | 0.94 GiB    | < 0.1%     |

At target throughput (200 TxkB/s), transaction data dominates egress (97.2%).
Vote traffic (24.1 GiB/month, fixed) is the floor cost regardless of throughput.

### Monthly Cost by Cloud Provider ($)

Egress is billed per GB (10⁹ bytes); 1 GiB ≈ 1.074 GB.

| Provider      | Price/GB | Free (GB)    | 4.5 (Praos) | 5 TxkB/s | 50 TxkB/s | 100 TxkB/s | 200 TxkB/s | 300 TxkB/s |
|---------------|----------|--------------|-------------|----------|-----------|------------|------------|------------|
| AWS           | $0.090   | 100          | $1.93       | $0.00    | $53.93    | $114.15    | $234.59    | $355.05    |
| GCP           | $0.120   | 0            | $14.58      | $11.62   | $83.90    | $164.21    | $324.79    | $485.40    |
| Azure         | $0.087   | 100          | $1.87       | $0.00    | $52.13    | $110.35    | $226.77    | $343.22    |
| Railway       | $0.100   | 0            | $12.15      | $9.69    | $69.92    | $136.84    | $270.66    | $404.50    |
| Alibaba Cloud | $0.074   | 10           | $8.25       | $6.43    | $51.00    | $100.52    | $199.55    | $298.59    |
| DigitalOcean  | $0.010   | 1,000        | $0.00       | $0.00    | $0.00     | $3.68      | $17.07     | $30.45     |
| Oracle Cloud  | $0.0085  | 10,240       | $0.00       | $0.00    | $0.00     | $0.00      | $0.00      | $0.00      |
| Linode        | $0.005   | 1,024        | $0.00       | $0.00    | $0.00     | $1.72      | $8.41      | $15.11     |
| Hetzner       | $0.0011  | 1,024        | $0.00       | $0.00    | $0.00     | $0.38      | $1.85      | $3.32      |
| UpCloud       | $0.000   | 1,024–24,576 | $0.00       | $0.00    | $0.00     | $0.00      | $0.00      | $0.00      |

> [!Note]
>
> - Prices are for US regions and may vary by location
> - Free allowances vary by plan tier; values shown are typical baseline
>   included transfer for standard instances
> - At high throughput (100+ TxkB/s), egress becomes a major cost item on
>   premium cloud providers (AWS, GCP, Azure); budget providers (Hetzner,
>   Linode) are significantly cheaper due to generous included transfer

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
