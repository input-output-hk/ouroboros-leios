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

- **~25 outbound (upstream) connections**: connections the relay initiates to
  other relays; blocks, EB bodies, votes, and certificates are pulled from these
- **~100 inbound (downstream) connections**: connections initiated by other
  relays and clients; headers are pushed to all subscribers here, and txs arrive
  from this direction (flowing upstream toward block producers)

Different traffic types have different directions and different fetch models:

| Traffic type         | Flows      | Serves to (egress)                                                         |
|----------------------|------------|----------------------------------------------------------------------------|
| Headers (RB/EB)      | Downstream | All ~100 inbound ChainSync subscribers                                     |
| Block bodies (RB/EB) | Downstream | 100 × (M/25) peers, where M = fetch multiplicity (typical 1, beefy 4–8)   |
| Tx diffusion         | Upstream   | 25 upstream peers × (1/25 fetch ratio) = **1 peer**                        |
| Votes                | Downstream | ~2 peers (spanning-tree × 2 redundancy)                                    |

> [!Note]
>
> The block/EB body peer count derives from: each of 100 inbound peers has ~25
> upstream sources and requests from M of them simultaneously (fetch multiplicity
> M). Our expected egress peers = 100 × M/25. For a lean relay M=1 → **4 peers**;
> for a beefy relay fetching from M=4–8 peers to reduce tail latency → **16–32
> peers**. High-stake pool relays commonly use M=4–8 to minimise block arrival
> latency at the cost of higher egress.
>
> Tx diffusion flows upstream (clients → relays → block producers): txs arrive
> from our 100 downstream peers and we forward them to our 25 upstream peers.
> Each upstream peer downloads each tx from 1 of its ~25 downstream connections
> → our selection probability = 1/25 → expected peers served = 25 × 1/25 = **1**.
>
> The **1-peer fetch** reflects the refactored TxSubmission V2
> ([ouroboros-network#5336](https://github.com/IntersectMBO/ouroboros-network/issues/5336)),
> which downloads each tx from one peer under normal conditions (additional
> requests are only made if a download takes longer than ~250 ms). This matches
> the CIP-164 simulation model (announce-to-all, fetch-from-one). TxSubmission
> V1 (currently deployed) fetches from all advertising peers until one succeeds,
> resulting in 20+ downloads per tx at a busy relay — significantly higher
> egress. The shipped V2 (ouroboros-network 10.7.1) uses `txInflightMultiplicity
> = 2` and is an intermediate step.
>
> **Not modelled**: txid announcements (32 bytes per tx, sent to all 25 upstream
> peers ≈ 800 bytes/tx) and received from all 100 downstream peers. At 300
> TxkB/s this adds ~4 GiB/month in txid egress — small relative to tx bodies
> but non-negligible at high throughput.

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

1. **Tx mempool diffusion** (1 peer):

   Transactions arrive from our ~100 downstream peers and are forwarded to our
   ~25 upstream peers; each upstream peer fetches from 1 of its ~25 downstreams
   → 1 peer:
   $4{,}500 \times 1 \times 2{,}628{,}000 \approx 11.0 \text{ GiB}$

2. **Header egress** (100 inbound downstream peers):
   $131{,}400 \times 1{,}024 \times 100 \approx 12.5 \text{ GiB}$

3. **Block body egress** (100 × M/25 peers; M=1 lean → 4 peers, M=4 beefy → 16):
   $131{,}400 \times 90{,}112 \times 4 \approx 44.1 \text{ GiB}$ (lean) /
   $131{,}400 \times 90{,}112 \times 16 \approx 176.5 \text{ GiB}$ (beefy, M=4)

   Block bodies contain the same transactions already gossiped via the mempool
   — the full tx data is **re-transmitted a second time** as part of block
   propagation. Leios avoids this by carrying only 32-byte hash references in
   EBs; the confirmed tx data is never re-sent as part of block propagation.

4. **Total relay egress**: $\approx 67.6 \text{ GiB/month}$

## Ouroboros Leios

In Linear Leios (CIP-164), transactions are gossiped via the mempool. EBs carry
only 32-byte tx hash references; actual transaction data is propagated
independently as transactions arrive. Only transactions in certified EBs count
as confirmed throughput.

EBs are produced at the same rate as Praos blocks (0.05/s), but only those
produced sufficiently before the next RB are certifiable. An RB announcing an
EB at slot $s$ can only include the certificate in a subsequent RB at slot
$s' \geq s + 3 L_{\text{hdr}} + L_{\text{vote}} + L_{\text{diff}} = s + 14$.
If any RB is produced within those 14 slots, the EB is discarded. Since each
slot produces a block independently with probability $f = 0.05$ (Bernoulli):

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

   Transactions arrive from ~100 downstream peers and are forwarded to ~25
   upstream peers; each upstream peer fetches from 1 of its ~25 downstream
   connections → 25 × (1/25) = 1 peer on average:

   $$E_{\text{tx}} = \text{TxkB/s} \times 1{,}000 \times 1 \times T_{\text{month}}$$

2. **Vote Egress** (fixed — independent of throughput):

   Votes propagate downstream (toward the next block producer) using a pull-based
   mini-protocol with deduplication. We model ~2× spanning-tree redundancy for a
   typical relay:

   $$E_{\text{votes}} = 600 \times 164 \times 0.05 \times 2 \times 2{,}628{,}000 \approx 24.1 \text{ GiB}$$

3. **EB Body Egress** (tx hash references — scales with TxkB/s):

   Each confirmed tx appears in $1/P(\text{cert}) \approx 2.08$ EB bodies on
   average (non-certified EBs also gossip their tx hashes). EB bodies are
   fetched by $100 \times M/25$ peers, the same model as Praos block bodies:

   $$E_{\text{eb-body}} = R_{\text{eb}} \times T_{\text{month}} \times \frac{\text{TxkB/s} \times 1{,}000}{1{,}500 \times 0.05} \times 32 \times \frac{100 M}{25} \times \frac{1}{P(\text{cert})}$$

   At M=1 (lean): $E_{\text{eb-body}} \approx \text{TxkB/s} \times 0.4350 \text{ GiB/month}$

   At M=4 (beefy): $E_{\text{eb-body}} \approx \text{TxkB/s} \times 1.740 \text{ GiB/month}$

4. **RB Header Egress** (combined RB/EB header, fixed):

   $$E_{\text{rb-hdr}} = 131{,}400 \times 1{,}024 \times 100 \approx 12.5 \text{ GiB}$$

5. **RB Body Egress** (certificate, certified RBs only):

   Only certified RBs carry a certificate. Fetched by $100 \times M/25$ peers.
   Using $N_{\text{cert}} = 63{,}072$/month:

   At M=1: $E_{\text{rb-body}} = 63{,}072 \times 8{,}000 \times 4 \approx 1.88 \text{ GiB}$

   At M=4: $E_{\text{rb-body}} = 63{,}072 \times 8{,}000 \times 16 \approx 7.54 \text{ GiB}$

### Fixed Overhead Summary

| Component       | Lean (M=1)   | Beefy (M=4)  | Notes                                      |
|-----------------|--------------|--------------|---------------------------------------------|
| Vote traffic    | 24.1 GiB     | 24.1 GiB     | 600 voters × 164 B × 0.05 EB/s × 2 peers   |
| RB/EB headers   | 12.5 GiB     | 12.5 GiB     | To all ~100 inbound downstream peers        |
| RB cert bodies  | 1.88 GiB     | 7.54 GiB     | 4 / 16 peers (63,072 certs/mo)              |
| **Fixed total** | **38.5 GiB** | **44.1 GiB** | Independent of throughput                   |

### Monthly Egress at Different Confirmed Throughputs

Lean relay (M=1, 4 body-fetch peers):

| TxkB/s        | Tx Data    | Block/EB Bodies | Fixed Overhead | **Total**     | vs Praos  |
| ------------- | ---------- | --------------- | -------------- | ------------- | --------- |
| 4.5 (Praos)   | 11.0 GiB   | 44.1 GiB (blk)  | 12.5 GiB (hdr) | **67.6 GiB**  | —         |
| 5             | 12.2 GiB   | 2.18 GiB (EB)   | 38.5 GiB       | **52.9 GiB**  | **-22%**  |
| 50            | 122.4 GiB  | 21.75 GiB       | 38.5 GiB       | **182.7 GiB** | +170%     |
| 100           | 244.8 GiB  | 43.50 GiB       | 38.5 GiB       | **326.8 GiB** | +383%     |
| 200           | 489.5 GiB  | 87.00 GiB       | 38.5 GiB       | **615.0 GiB** | +810%     |
| 300           | 734.3 GiB  | 130.50 GiB      | 38.5 GiB       | **903.3 GiB** | +1,236%   |

Beefy relay (M=4, 16 body-fetch peers):

| TxkB/s        | Tx Data    | Block/EB Bodies | Fixed Overhead | **Total**       | vs Praos  |
| ------------- | ---------- | --------------- | -------------- | --------------- | --------- |
| 4.5 (Praos)   | 11.0 GiB   | 176.5 GiB (blk) | 12.5 GiB (hdr) | **200.0 GiB**   | —         |
| 5             | 12.2 GiB   | 8.72 GiB (EB)   | 44.1 GiB       | **65.0 GiB**    | **-68%**  |
| 50            | 122.4 GiB  | 87.00 GiB       | 44.1 GiB       | **253.5 GiB**   | +27%      |
| 100           | 244.8 GiB  | 174.00 GiB      | 44.1 GiB       | **462.9 GiB**   | +131%     |
| 200           | 489.5 GiB  | 348.00 GiB      | 44.1 GiB       | **881.6 GiB**   | +341%     |
| 300           | 734.3 GiB  | 522.00 GiB      | 44.1 GiB       | **1,300 GiB**   | +550%     |

> [!Note]
>
> - **Praos row**: tx mempool diffusion (11.0 GiB, 1 peer) + block body
>   re-transmission of the same txs (44.1 / 176.5 GiB, 4/16 peers) + headers
>   (12.5 GiB, 100 peers). Every confirmed transaction is sent **twice** in Praos.
> - **Leios saves more on a beefy relay**: at M=4 the 176.5 GiB Praos block body
>   overhead is replaced by 8.72 GiB EB body overhead at 5 TxkB/s — a 68% saving.
>   At high throughput tx data dominates and the saving shrinks.
> - EB body egress is scaled by 1/P(cert) ≈ 2.08× (non-certified EBs gossip their
>   tx hashes) and by M/25 × 100 peers
> - Vote overhead and headers are unaffected by M — headers are pushed to all
>   subscribers; votes use a separate spanning-tree gossip
> - "vs Praos" compares against the Praos relay egress in the same M row

### Traffic Components at 200 TxkB/s

| Component        | Lean (M=1) | % of Total | Beefy (M=4) | % of Total |
| ---------------- | ---------- | ---------- | ----------- | ---------- |
| Tx Data          | 489.5 GiB  | 79.6%      | 489.5 GiB   | 55.5%      |
| EB Bodies        | 87.00 GiB  | 14.1%      | 348.0 GiB   | 39.5%      |
| Vote Traffic     | 24.1 GiB   | 3.9%       | 24.1 GiB    | 2.7%       |
| RB/EB Headers    | 12.5 GiB   | 2.0%       | 12.5 GiB    | 1.4%       |
| RB Cert Bodies   | 1.88 GiB   | 0.3%       | 7.54 GiB    | 0.9%       |
| **Total**        | **615 GiB**|            | **882 GiB** |            |

On a lean relay (M=1), tx data dominates (80%) and EB bodies are a secondary
cost (14%). On a beefy relay (M=4), tx data still dominates (56%) but EB bodies
grow to a significant secondary cost (39%), making the 1/P(cert) certification
overhead and body-fetch multiplicity a much more material factor.

### Monthly Cost by Cloud Provider ($)

Egress is billed per GB (10⁹ bytes); 1 GiB ≈ 1.074 GB.

| Provider      | Price/GB | Free (GB)    | 4.5 (Praos) | 5 TxkB/s | 50 TxkB/s | 100 TxkB/s | 200 TxkB/s | 300 TxkB/s |
| ------------- | -------- | ------------ | ----------- | --------- | --------- | ---------- | ---------- | ---------- |
| AWS           | $0.090   | 100          | $0.00       | $0.00     | $8.66     | $22.58     | $50.45     | $78.31     |
| GCP           | $0.120   | 0            | $8.71       | $6.82     | $23.54    | $42.11     | $79.26     | $116.41    |
| Azure         | $0.087   | 100          | $0.00       | $0.00     | $8.37     | $21.83     | $48.76     | $75.70     |
| Railway       | $0.100   | 0            | $7.26       | $5.68     | $19.62    | $35.09     | $66.05     | $97.01     |
| Alibaba Cloud | $0.074   | 10           | $4.63       | $3.46     | $13.78    | $25.23     | $48.14     | $71.05     |
| DigitalOcean  | $0.010   | 1,000        | $0.00       | $0.00     | $0.00     | $0.00      | $0.00      | $0.00      |
| Oracle Cloud  | $0.0085  | 10,240       | $0.00       | $0.00     | $0.00     | $0.00      | $0.00      | $0.00      |
| Linode        | $0.005   | 1,024        | $0.00       | $0.00     | $0.00     | $0.00      | $0.00      | $0.00      |
| Hetzner       | $0.0011  | 1,024        | $0.00       | $0.00     | $0.00     | $0.00      | $0.00      | $0.00      |
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
