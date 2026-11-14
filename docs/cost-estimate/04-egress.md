# Egress cost estimation per node

Network egress is metered for most cloud providers even though many have some
monthly budget that is free. In the following example calculation, we try to be
as precise as possible given today's
[p2p default configuration](https://book.world.dev.cardano.org/environments/mainnet/config.json)
of the node.

All values use confirmed throughput in TxkB/s (transaction kilobytes per
second reaching the ledger). Seconds per month: 2,629,728 (365.24 ÷ 12 = 30.437
days), as in the cost estimator.

## Network Topology

The Cardano relay network is asymmetric. A typical relay node has:

- **~25 outbound (upstream) connections**: connections the relay initiates to
  other relays; blocks, EB bodies and certificates are fetched from these, and
  votes are pushed by them
- **~60 inbound (downstream) connections**: connections initiated by other
  relays and clients; headers and votes are pushed to all of them, and txs arrive
  from this direction (flowing upstream toward block producers). 60 is a
  mid-level pool's relay; the best-connected relays of large pools carry about
  100 (MusashiNet's IOG relays: 92 hot downstream and 115 inbound peers on
  average, 7 days to 2026-11-12)

Different traffic types have different directions and different fetch models:

| Traffic type         | Flows      | Serves to (egress)                                                         |
|----------------------|------------|----------------------------------------------------------------------------|
| Headers (RB/EB)      | Downstream | All ~60 inbound ChainSync subscribers                                      |
| RB bodies (Praos blocks) | Downstream | 60 × (1/25) = 2.4 peers: BlockFetch asks one peer per block       |
| EB bodies            | Downstream | 60 × (M/25) peers, where M = fetch multiplicity (default 2)               |
| Tx diffusion         | Upstream   | 25 upstream peers × (1/25 fetch ratio) = **1 peer**                        |
| Votes                | Downstream | All ~60 inbound peers: each vote is pushed once to every downstream peer   |

> [!Note]
>
> The EB body peer count derives from: each of 60 inbound peers has ~25
> upstream sources and requests from M of them simultaneously (fetch multiplicity
> M). Our expected egress peers = 60 × M/25. The estimator's default is M=2
> (**4.8 peers**): the egress devnet measured about 1.5 to 2 copies of each EB
> body, and MusashiNet's relays downloaded each EB body 3.25 times. The
> tables below bracket it with a lean relay, M=1 → **2.4 peers**, and a beefy
> relay, M=4 → **9.6 peers**; fetching from up to 8 peers to reduce tail latency
> gives up to 19.2.
>
> Praos blocks (RB bodies, certificates included) are fetched from one peer at a
> time: BlockFetch's `MaxConcurrencyDeadline` defaults to 1. They use M = 1, so
> **2.4 peers**, on every relay.
>
> Tx diffusion flows upstream (clients → relays → block producers): txs arrive
> from our 60 downstream peers and we forward them to our 25 upstream peers.
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
> egress. The shipped V2 (cardano-node 10.7.1) uses `txInflightMultiplicity
> = 2` and is an intermediate step.
>
> **Not modelled**: txid announcements (32 bytes per tx, sent to all 25 upstream
> peers ≈ 800 bytes/tx) and received from all 60 downstream peers. At 300
> TxkB/s (265 tx/s of 1,132 B) this adds about 520 GiB/month in txid egress per
> relay, about 70% of the tx body egress, before message framing and packet
> headers. It is the next term to measure and add.

## Ouroboros Praos

The following numbers are Cardano mainnet's block sizes (November 2026).

| Component  | Size (bytes) | Size (KiB) |
|------------|--------------|------------|
| Header (H) | 1,024        | 1          |
| Body (B)   | 90,112       | 88         |

### Blocks per Month

| Parameter               | Value       | Formula                                 |
|-------------------------|-------------|-----------------------------------------|
| Active slot coefficient | 0.05        | Protocol parameter                      |
| Seconds per month       | 2,629,728   | $30.437 \times 24 \times 60 \times 60$  |
| **Blocks per month**    | **131,486** | $0.05 \times 2{,}629{,}728$             |

### Praos Relay Node Egress Calculation

1. **Tx mempool diffusion** (1 peer):

   Transactions arrive from our ~60 downstream peers and are forwarded to our
   ~25 upstream peers; each upstream peer fetches from 1 of its ~25 downstreams
   → 1 peer:
   $4{,}500 \times 1 \times 2{,}629{,}728 \approx 11.0 \text{ GiB}$

2. **Header egress** (60 inbound downstream peers):
   $131{,}486 \times 1{,}024 \times 60 \approx 7.5 \text{ GiB}$

3. **Block body egress** (60 × 1/25 = 2.4 peers: one peer per Praos block):
   $131{,}486 \times 90{,}112 \times 2.4 \approx 26.5 \text{ GiB}$

   Block bodies contain the same transactions already gossiped via the mempool,
   so the full tx data is **re-transmitted a second time** as part of block
   propagation. Leios avoids this for the transactions in EBs, which carry only
   37-byte references (hash and size). Ranking blocks without a certificate still
   carry full transactions, and those are re-sent as in Praos (RB Body Egress
   below).

4. **Total relay egress**: $\approx 45.0 \text{ GiB/month}$

## Ouroboros Leios

In Linear Leios (CIP-164), transactions are gossiped via the mempool. EBs carry
only 37-byte tx references (a 32 B hash plus the Tx size); actual transaction data is propagated
independently as transactions arrive. Only transactions in certified EBs count
as confirmed throughput.

EBs are produced at the same rate as Praos blocks (0.05/s), but only those
produced sufficiently before the next RB are certifiable. The certificate for an
EB announced at slot $s$ can only go in the next RB, and only if that RB comes at
slot $s' \geq s + 3 L_{\text{hdr}} + L_{\text{vote}} + L_{\text{diff}} = s + 14$.
If an RB is produced in the 13 slots between, the EB is discarded. Since each
slot produces a block independently with probability $f = 0.05$ (Bernoulli):

$$P(\text{EB certified}) = (1 - 0.05)^{13} = 0.95^{13} \approx 0.5133 \approx 0.51$$

as in CIP-164 and the feasibility report. Non-certified EBs still generate EB
body traffic: their 37-byte tx references are gossiped whether or not the EB is
eventually certified, because nodes do not know in advance which EBs will be
certified. A transaction that an EB carries is therefore expected to appear in
$1/P(\text{cert}) \approx 1.95$ EB bodies before one of those EBs is certified,
scaling EB body egress accordingly. EBs reference only the transactions RBs don't
carry: while Leios is active the RBs without a certificate are full, so
$(1 - P(\text{cert})) \times 4.5 \approx 2.19$ TxkB/s travel in RBs and the rest
in EBs.

The model assumes tx diffusion reaches every node before an EB is certified, so
it counts no traffic for fetching the transactions an EB carries that a node
hasn't seen. That traffic exists: on MusashiNet 5 to 20% of on-chain bytes
reached relays only inside EBs (7 days to 2026-11-12). It is not modelled.

### Block Size Components

| Component                     | Size (bytes) | Size (KiB) |
| ----------------------------- | ------------ | ---------- |
| EB Body (37 B per tx ref)     | varies       | varies     |
| Vote (per voter, per EB)      | 91           | 0.1        |
| RB Header (doubles as EB hdr) | 1,024        | 1          |
| RB Body (certificate)         | 129          | 0.1        |
| RB Body (transactions)        | 90,112       | 88         |

> [!Note]
>
> In the current CIP-164 implementation, the RB header doubles as the EB header:
> one 1,024-byte combined header is produced per block. LeiosNotify still
> announces each EB to every downstream peer, about 985 B per EB per peer on the
> egress devnet (the announcement repeats the header). That announcement is not
> modelled.

### Protocol Rates

| Parameter             | Value                  | Source                                                                                    |
| --------------------- | ---------------------- | ----------------------------------------------------------------------------------------- |
| EB/RB rate            | 0.05/s                 | Active slot coefficient                                                                   |
| EBs per month         | 131,486                | $0.05 \times 2{,}629{,}728$                                                               |
| Votes per EB          | 600                    | Committee seats: one vote per seat per EB; 600 for launch, below CIP-164's 900, to limit vote traffic (about 95% of active stake) |
| Vote size             | 91 bytes               | 88 B vote (ouroboros-consensus golden test) + 3 B `MsgLeiosVotes` framing                 |
| P(EB certified)       | ≈ 0.51                 | $(1-0.05)^{13} = 0.95^{13} \approx 0.5133$: the next block comes 14 or more slots later, none in the 13 between |
| Certified EBs/month   | 67,498                 | $0.05 \times 0.5133 \times 2{,}629{,}728$                                                 |

### Egress Formulas

1. **Transaction Data Egress** (dominant — scales with TxkB/s):

   Transactions arrive from ~60 downstream peers and are forwarded to ~25
   upstream peers; each upstream peer fetches from 1 of its ~25 downstream
   connections → 25 × (1/25) = 1 peer on average:

   $$E_{\text{tx}} = \text{TxkB/s} \times 1{,}000 \times 1 \times T_{\text{month}}$$

2. **Vote Egress** (fixed — independent of throughput):

   Votes are pushed (CIP-164 LeiosNotify, ouroboros-consensus PR #2430): a node
   sends each new vote once to every downstream peer, the one it came from
   included, so every inbound peer receives every vote, as it receives every
   header. A pull-based design was considered and deferred for launch
   (ouroboros-leios#1073):

   $$E_{\text{votes}} = 600 \times 91 \times 0.05 \times 60 \times 2{,}629{,}728 \approx 401.2 \text{ GiB}$$

3. **EB Body Egress** (tx hash references, scales with TxkB/s):

   Each tx that an EB carries appears in $1/P(\text{cert}) \approx 1.95$ EB
   bodies on average (non-certified EBs also gossip their tx hashes). EBs carry
   the throughput above the 2.19 TxkB/s that RBs carry. EB bodies are fetched by
   $60 \times M/25$ peers:

   $$E_{\text{eb-body}} = R_{\text{eb}} \times T_{\text{month}} \times \frac{(\text{TxkB/s} - 2.19) \times 1{,}000}{1{,}132 \times 0.05} \times 37 \times \frac{60 M}{25} \times \frac{1}{P(\text{cert})}$$

   with 1,132 B the mainnet mean Tx size over epochs 589–661.

   At M=1 (lean): $E_{\text{eb-body}} \approx (\text{TxkB/s} - 2.19) \times 0.3743 \text{ GiB/month}$

   At M=4 (beefy): $E_{\text{eb-body}} \approx (\text{TxkB/s} - 2.19) \times 1.497 \text{ GiB/month}$

4. **RB Header Egress** (combined RB/EB header, fixed):

   $$E_{\text{rb-hdr}} = 131{,}486 \times 1{,}024 \times 60 \approx 7.5 \text{ GiB}$$

5. **RB Body Egress** (certificates, and the transactions in RBs without one):

   Certified RBs carry a certificate: 54 B plus one bit per seat, 129 B for 600
   seats (a certifying RB body on MusashiNet is 75 B). Every other RB carries
   transactions, and while Leios is active those RBs are full: 90,112 B, as in
   the capacity $f \times [P(\text{cert}) \times \text{EB capacity} + (1 - P(\text{cert})) \times 90{,}112]$.
   Both are fetched like any Praos block, by $60 \times 1/25 = 2.4$ peers.
   Using $N_{\text{cert}} = 67{,}498$/month and $131{,}486 - 67{,}498 = 63{,}988$
   RBs with transactions:

   $E_{\text{rb-cert}} = 67{,}498 \times 129 \times 2.4 \approx 0.019 \text{ GiB}$

   $E_{\text{rb-tx}} = 63{,}988 \times 90{,}112 \times 2.4 \approx 12.9 \text{ GiB}$

   The second term is fixed while Leios is active: RB transactions stay at
   $(1 - P(\text{cert})) \times 4.5$ TxkB/s whatever the throughput, and EBs
   carry the rest.

### Fixed Overhead Summary

| Component       | Lean (M=1)   | Beefy (M=4)  | Notes                                      |
|-----------------|--------------|--------------|---------------------------------------------|
| Vote traffic    | 401.2 GiB    | 401.2 GiB    | 600 seats × 91 B × 0.05 EB/s × 60 peers     |
| RB/EB headers   | 7.5 GiB      | 7.5 GiB      | To all ~60 inbound downstream peers         |
| RB cert bodies  | 0.02 GiB     | 0.02 GiB     | 2.4 peers, Praos block fetch (67,498 certs/mo) |
| RB tx bodies    | 12.9 GiB     | 12.9 GiB     | 2.4 peers, full RBs without a certificate (63,988/mo) |
| **Fixed total** | **421.6 GiB** | **421.6 GiB** | Independent of throughput while Leios is active |

### Monthly Egress at Different Confirmed Throughputs

Lean relay (M=1, 2.4 body-fetch peers):

| TxkB/s        | Tx Data    | Block/EB Bodies | Fixed Overhead | **Total**     | vs Praos  |
| ------------- | ---------- | --------------- | -------------- | ------------- | --------- |
| 4.5 (Praos)   | 11.0 GiB   | 26.5 GiB (blk) | 7.5 GiB (hdr) | **45.0 GiB** | —         |
| 5             | 12.2 GiB | 1.05 GiB (EB) | 421.6 GiB | **434.9 GiB** | **+866%** |
| 50            | 122.5 GiB | 17.89 GiB | 421.6 GiB | **561.9 GiB** | +1,149% |
| 100           | 244.9 GiB | 36.61 GiB | 421.6 GiB | **703.1 GiB** | +1,462% |
| 200           | 489.8 GiB | 74.03 GiB | 421.6 GiB | **985.5 GiB** | +2,090% |
| 300           | 734.7 GiB | 111.46 GiB | 421.6 GiB | **1,267.8 GiB** | +2,717% |

Beefy relay (M=4, 9.6 EB-body-fetch peers; Praos blocks still 2.4):

| TxkB/s        | Tx Data    | Block/EB Bodies | Fixed Overhead | **Total**       | vs Praos  |
| ------------- | ---------- | --------------- | -------------- | --------------- | --------- |
| 4.5 (Praos)   | 11.0 GiB   | 26.5 GiB (blk) | 7.5 GiB (hdr) | **45.0 GiB** | —         |
| 5             | 12.2 GiB | 4.20 GiB (EB) | 421.6 GiB | **438.0 GiB** | **+873%** |
| 50            | 122.5 GiB | 71.57 GiB | 421.6 GiB | **615.6 GiB** | +1,268% |
| 100           | 244.9 GiB | 146.42 GiB | 421.6 GiB | **812.9 GiB** | +1,707% |
| 200           | 489.8 GiB | 296.12 GiB | 421.6 GiB | **1,207.5 GiB** | +2,583% |
| 300           | 734.7 GiB | 445.83 GiB | 421.6 GiB | **1,602.2 GiB** | +3,460% |

> [!Note]
>
> - **Praos row**: tx mempool diffusion (11.0 GiB, 1 peer) + block body
>   re-transmission of the same txs (26.5 GiB, 2.4 peers, one per block) + headers
>   (7.5 GiB, 60 peers). Every confirmed transaction is sent **twice** in Praos.
> - **Votes outweigh the body saving**: at 5 TxkB/s the 26.5 GiB of Praos block
>   bodies becomes 12.9 GiB of RB bodies (the RBs without a certificate) plus
>   1.1 GiB (M=1) to 4.2 GiB (M=4) of EB bodies, but votes add 401.2 GiB, so a
>   Leios relay sends about 9.7× what a Praos relay does.
> - EB body egress covers the throughput above the 2.19 TxkB/s that RBs carry, scaled
>   by 1/P(cert) ≈ 1.95× (non-certified EBs gossip their tx hashes) and by
>   M/25 × 60 peers
> - Vote overhead and headers are unaffected by M: both are pushed to every
>   downstream peer
> - "vs Praos" compares against the Praos relay egress, 45.0 GiB in both tables:
>   M applies to EB bodies only

### Traffic Components at 200 TxkB/s

| Component        | Lean (M=1) | % of Total | Beefy (M=4) | % of Total |
| ---------------- | ---------- | ---------- | ----------- | ---------- |
| Tx Data          | 489.8 GiB  | 49.7%      | 489.8 GiB   | 40.6%      |
| Vote Traffic     | 401.2 GiB  | 40.7%      | 401.2 GiB   | 33.2%      |
| EB Bodies        | 74.0 GiB   | 7.5%       | 296.1 GiB   | 24.5%      |
| RB/EB Headers    | 7.5 GiB    | 0.8%       | 7.5 GiB     | 0.6%       |
| RB Tx Bodies     | 12.9 GiB   | 1.3%       | 12.9 GiB    | 1.1%       |
| RB Cert Bodies   | 0.02 GiB   | < 0.1%     | 0.02 GiB    | < 0.1%     |
| **Total**        | **986 GiB**|            | **1,208 GiB** |            |

On a lean relay (M=1), tx data is about half the egress (50%) and votes
most of the rest (41%). On a beefy relay (M=4), tx data is 41%, votes 33% and
EB bodies 25%. Vote traffic doesn't depend on throughput or M: it grows
with the committee size and the number of downstream peers.

### Monthly Cost by Cloud Provider ($)

Egress is priced per GB (10⁹ bytes); 1 GiB ≈ 1.074 GB. The table prices a lean
relay (M = 1) and subtracts each provider's free tier per node; the cost
estimator defaults to M = 2 and applies no free tier.

| Provider      | Price/GB | Free (GB)    | 4.5 (Praos) | 5 TxkB/s | 50 TxkB/s | 100 TxkB/s | 200 TxkB/s | 300 TxkB/s |
| ------------- | -------- | ------------ | ----------- | --------- | --------- | ---------- | ---------- | ---------- |
| AWS           | $0.090   | 100          | $0.00 | $33.03 | $45.30 | $58.95 | $86.23 | $113.52 |
| GCP           | $0.120   | 0            | $5.80 | $56.04 | $72.41 | $90.60 | $126.97 | $163.35 |
| Azure         | $0.087   | 100          | $0.00 | $31.93 | $43.79 | $56.98 | $83.36 | $109.73 |
| Railway       | $0.100   | 0            | $4.83 | $46.70 | $60.34 | $75.50 | $105.81 | $136.13 |
| Alibaba Cloud | $0.074   | 10           | $2.84 | $33.82 | $43.91 | $55.13 | $77.56 | $99.99 |
| DigitalOcean  | $0.010   | 4,295        | $0.00 | $0.00 | $0.00 | $0.00 | $0.00 | $0.00 |
| Oracle Cloud  | $0.0085  | 10,240       | $0.00 | $0.00 | $0.00 | $0.00 | $0.00 | $0.00 |
| Akamai (Linode) | $0.005 | 5,000        | $0.00 | $0.00 | $0.00 | $0.00 | $0.00 | $0.00 |
| Hetzner       | $0.0011  | 20,000       | $0.00 | $0.00 | $0.00 | $0.00 | $0.00 | $0.00 |
| UpCloud       | $0.000   | 1,024–24,576 | $0.00 | $0.00 | $0.00 | $0.00 | $0.00 | $0.00 |

> [!Note]
>
> - Prices are for US regions (Hetzner: EU) and may vary by location
> - Free allowances, checked on 2026-11-10: AWS and Azure 100 GB a month per
>   account, GCP Premium tier none. Per server, pooled across an account's
>   servers: DigitalOcean 4,000 GiB on the General Purpose g-2vcpu-8gb plan
>   (confirmed 2026-11-14), Akamai 5 TB on the Dedicated G7 8 GB plan,
>   Hetzner 20 TB in the EU
> - Railway, Alibaba Cloud, Oracle Cloud and UpCloud keep their earlier figures;
>   they were not part of the November 2026 check
> - Praos fits within the AWS/Azure 100 GB free tiers; Leios at 5 TxkB/s doesn't,
>   because of vote traffic
> - DigitalOcean, Akamai and Hetzner stay within their included transfer at every
>   throughput shown: a lean relay sends at most 1.36 TB a month

### Data Egress Cost Sources

| Provider     | Price/GB | Source                                                 | Last Updated |
| ------------ | -------- | ------------------------------------------------------ | ------------ |
| AWS          | $0.090   | https://aws.amazon.com/ec2/pricing/                    | Nov 2026     |
| GCP          | $0.120   | https://cloud.google.com/vpc/pricing                   | Nov 2026     |
| Azure        | $0.087   | https://azure.microsoft.com/pricing/details/bandwidth/ | Nov 2026     |
| DigitalOcean | $0.010   | https://www.digitalocean.com/pricing/                  | Nov 2026     |
| Akamai (Linode) | $0.005 | https://www.linode.com/pricing/                        | Nov 2026     |
| Hetzner      | $0.0011  | https://www.hetzner.com/cloud/pricing                  | Nov 2026     |

Note: Prices may vary by region and volume. Some providers offer free tiers or
volume discounts not reflected in these base rates.
