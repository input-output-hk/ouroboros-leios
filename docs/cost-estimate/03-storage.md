# Storage cost estimation per node

> [!Note] 
>
> **Scope**: The tables below cover **blockchain history**: the append-only chain
> data (blocks, EB bodies, transactions) on the bulk disk. The ledger state sits on
> the fast SSD; on an LSM mainnet node the UTxO set takes 3.2 GiB for 10.86 M
> entries, and the estimator grows it with throughput (see "Two storage tiers"
> below).
>
> **100% confirmed throughput assumption:**
> The chain on the bulk disk accumulates only certified (confirmed) transactions.
> Every fetched EB, certified or not, is also held on the fast SSD until it is
> $k$ = 2,160 blocks deep; an uncertified EB's transactions are announced again in
> later EBs.
>
> **Compression note:** cardano-node doesn't compress its ImmutableDB, so the
> calculations represent raw storage requirements without compression.

All values use confirmed throughput in TxkB/s (transaction kilobytes per
second reaching the ledger). Seconds per month: 2,629,728 (365.24 ÷ 12 = 30.437
days), as in the cost estimator.

## Ouroboros Praos

We start with Ouroboros Praos to establish a baseline for storage requirements.
In Praos, storage is primarily used for maintaining the blockchain history.

### Block Components

| Component       | Size (bytes) | Size (KiB) |
| --------------- | ------------ | ---------- |
| Block header    | 1,024        | 1          |
| Block body      | 90,112       | 88         |
| **Total block** | **91,136**   | **89**     |

### Monthly Storage Calculation

| Parameter               | Value    | Formula            |
| ----------------------- | -------- | ------------------ |
| Slot duration           | 1 second | Protocol parameter |
| Active slot coefficient | 0.05     | Protocol parameter |
| **Blocks per second**   | **0.05** |                    |

$$S_{\text{praos}} = 91{,}136 \times 0.05 \times 2{,}629{,}728 \approx 11.16 \text{ GiB/month}$$

The Praos-equivalent confirmed throughput is $0.05 \times 90{,}112 = 4{,}505.6 \approx 4.5 \text{ TxkB/s}$.

At confirmed throughput at or below the Praos capacity ceiling (4.5 TxkB/s),
Linear Leios stores the same transaction bytes as Praos plus protocol overhead
(EB references, RB headers and certificates). The overhead is small: 2.8% of the
total at 5 TxkB/s and about 3% above it, nearly all of it EB references.

## Ouroboros Leios

In Linear Leios (CIP-164), transactions are gossiped via the mempool and
referenced by hash in Endorsement Blocks (EBs). Only the transactions in
**certified** EBs are permanently stored. An EB is certified when a quorum of
votes arrives before the certification deadline.

### Storage Components

| Component           | Description                             | Scales With      |
| ------------------- | --------------------------------------- | ---------------- |
| Tx closure data     | Confirmed transaction bytes             | TxkB/s           |
| EB body (tx references) | 37-byte tx references in certified EBs | TxkB/s above what RBs carry |
| RB (header + cert)  | RB headers, which announce the EBs; certificates in certified RBs | Fixed (0.05/s, 0.026/s) |

> [!Note]
> Votes are ephemeral and not persisted to disk. They are used to produce
> certificates, which are included in the subsequent Ranking Block.

> [!Note]
> **Two storage tiers (November 2026).** With the LSM ledger backend a node splits
> its disk. A fast SSD holds the ledger tables and snapshots, the VolatileDB, and
> the body of every fetched EB with the transactions of the EB closures, each
> once, until it is $k$ = 2,160 blocks deep (≈ 12 h). A bulk disk holds the ImmutableDB. The monthly increments below land on
> the bulk disk. The fast tier is the node's volatile path
> (`--volatile-database-path`), the bulk disk its immutable path
> (`--immutable-database-path`).
>
> An LSM mainnet node (cardano-node 11.0.1, 2026-11-11) uses 4.2 GiB on its volatile
> path: UTxO tables 3.2 GiB for 10.86 M entries, two ledger snapshots of 0.49 GiB, and a
> 20 MiB VolatileDB. The estimator allows twice the UTxO tables (6.4 GiB, so a full LSM
> merge fits while snapshots pin the old runs), three ledger snapshots (1.5 GiB: two
> kept, one being written) and 2,160 full RBs (0.18 GiB), 8.05 GiB, and sizes the
> fast tier at 10 GiB per node, the rest being headroom. UTxO growth comes on top, at one
> new entry per 11.6 kB of transactions (mainnet epochs 589–661: an epoch with 1 MB more
> transactions had 85.9 more net new entries) and 2 × 316 B per entry.
>
> Both disks grow with the chain. The estimator provisions what a node needs today plus a
> margin of growth (2 months by default) and enlarges the disks as the chain grows, since
> cloud volumes resize in place. Its storage cost is the average over the first 12 months:
> month $m$ holds $m - 1$ + margin months of growth, so the average holds
> $(12 - 1)/2 + 2 = 7.5$. The monthly increments below are what that bill rises by each
> month.
>
> Leios adds the recent EBs: the transactions the EB closures carry, (throughput − the
> 2.2 TxkB/s that RBs carry) × 43,200 s, each held once, plus the 37 B references of
> every fetched EB, about 4.2 GiB more at 100 TxkB/s. The estimator prices the two tiers
> separately; the provider table below prices the monthly increment at each provider's
> bulk-disk price (November 2026).

### Storage Formulas

1. **Transaction Closure Storage** (dominant):

   $$S_{\text{tx}} = \text{TxkB/s} \times 1{,}000 \times T_{\text{month}}$$

   where $T_{\text{month}} = 2{,}629{,}728$ seconds/month.

2. **EB Body Storage** (tx hash references, certified EBs only):

   Only certified EB bodies are stored. Each certified EB body is correspondingly
   larger: it must reference $1/P_{\text{cert}}$ more transactions than a
   world where all EBs were certified, so the $P_{\text{cert}}$ factor cancels
   and total stored bytes are independent of certification probability. EBs
   reference only the transactions RBs don't carry: while Leios is active the RBs
   without a certificate are full, carrying $(1 - P_{\text{cert}}) \times 4.5 \approx 2.19$
   TxkB/s.

   $$S_{\text{eb-body}} = \frac{(\text{TxkB/s} - 2.19) \times 1{,}000}{S_{\text{tx-avg}}} \times 37 \text{ bytes/s} \times T_{\text{month}}$$

   where:
   - $S_{\text{tx-avg}}$ = average transaction size (1,132 bytes, the mainnet mean over epochs 589–661)
   - 37 bytes per tx reference (a 32 B hash plus the Tx size)

   CIP-164 has no separate EB header: the RB header announces the EB, and it is
   stored with the RB below.

3. **RB Storage** (header + certificate, fixed):

   $$S_{\text{rb}} = (0.05 \times 1{,}024 + 0.0257 \times 129) \times T_{\text{month}} = 0.134 \text{ GiB/month}$$

   where every RB has a 1,024 B header and only certified RBs (0.0257/s) carry a
   certificate: 54 B plus one bit per committee seat, 129 B for 600 seats. A
   certifying RB body on MusashiNet is 75 B with a 21 B bitfield (KleioScan, block 95445).

### Storage Calculation at 5 TxkB/s (Leios Baseline)

1. **Tx closure**: $5{,}000 \times 2{,}629{,}728 = 13{,}148{,}640{,}000 \text{ bytes} \approx 12.25 \text{ GiB}$

2. **EB body** (tx references): $\frac{5{,}000 - 2{,}193}{1{,}132} \times 37 \times 2{,}629{,}728 = 2.48 \times 37 \times 2{,}629{,}728 \approx 0.225 \text{ GiB}$

3. **RB**: $0.134 \text{ GiB}$ (fixed; 1,024 B headers + 129 B certificates)

4. **Total**: $12.25 + 0.225 + 0.134 \approx 12.60 \text{ GiB/month}$

This is approximately 13% more than Praos (11.16 GiB), mostly because 5 TxkB/s
carries 11% more transactions than 4.5. The Leios overhead (EB references, RB
headers and certificates) adds 0.36 GiB, 2.8% of the total.

### Monthly Storage at Different Confirmed Throughputs

| TxkB/s      | Tx/s | Tx Closure | EB Body    | RB        | Total         | vs Praos |
|-------------|------|------------|------------|-----------|---------------|----------|
| 4.5 (Praos) | 4    | 11.03 GiB  | —          | 0.13 GiB  | **11.16 GiB** | —        |
| 5           | 4    | 12.25 GiB  | 0.225 GiB  | 0.134 GiB | 12.60 GiB     | +13%     |
| 50          | 44   | 122.5 GiB  | 3.827 GiB  | 0.134 GiB | 126.4 GiB     | +1,033%  |
| 100         | 88   | 244.9 GiB  | 7.830 GiB  | 0.134 GiB | 252.9 GiB     | +2,166%  |
| 200         | 177  | 489.8 GiB  | 15.835 GiB | 0.134 GiB | 505.8 GiB     | +4,432%  |
| 300         | 265  | 734.7 GiB  | 23.840 GiB | 0.134 GiB | 758.7 GiB     | +6,698%  |

> [!Note]
>
> - The 4.5 (Praos) row shows the Praos protocol baseline: full blocks, bodies
>   and headers, no EB/vote/cert overhead
> - Tx/s assumes average transaction size of 1,132 bytes
> - EB body storage grows with throughput because higher-throughput EBs reference
>   more transactions (37 bytes each); the 2.19 TxkB/s that RBs carry need none
> - These are monthly increments; total accumulated storage grows over time
> - CIP-164 Table 8 cross-check: its 526 GB at 200 TxkB/s is the transaction
>   bytes alone (200,000 B/s × 2,628,000 s). Our total, 505.8 GiB ≈ 543 GB, adds
>   the EB references and RB headers and certificates (16.0 GiB, about 17 GB)
>   and uses a 2,629,728 s month

### Storage Component Analysis at 200 TxkB/s

| Component            | Storage    | % of Total |
|----------------------|------------|------------|
| Tx Closure Data      | 489.8 GiB  | 96.8%      |
| EB Body (references) | 15.835 GiB | 3.1%       |
| RB headers and certificates | 0.134 GiB  | < 0.1%     |

Transaction closure data dominates at all throughput levels. The overhead of
Linear Leios is dominated by tx references in EB bodies at ~3.1%, which could
even be avoided. The certificate overhead is not avoidable but makes up less
than 0.1%.

## Cost Analysis

### Monthly Storage Cost by Cloud Provider ($)

AWS EBS, Azure managed disks and DigitalOcean volumes bill per GiB; GCP, Akamai
and Hetzner prices are taken per GB (10⁹ bytes; 1 GiB ≈ 1.074 GB). Units checked
2026-11-14.

| Provider        | Price       | Free | 4.5 (Praos) | 5 TxkB/s | 50 TxkB/s | 100 TxkB/s | 200 TxkB/s | 300 TxkB/s |
| --------------- | ----------- | ---- | ----------- | --------- | --------- | ---------- | ---------- | ---------- |
| AWS             | $0.045/GiB  | 0    | $0.50      | $0.57     | $5.69     | $11.38     | $22.76     | $34.14     |
| GCP             | $0.040/GB   | 0    | $0.48      | $0.54     | $5.43     | $10.86     | $21.72     | $32.59     |
| Azure           | $0.040/GiB  | 0    | $0.45      | $0.50     | $5.06     | $10.12     | $20.23     | $30.35     |
| DigitalOcean    | $0.100/GiB  | 0    | $1.12      | $1.26     | $12.64    | $25.29     | $50.58     | $75.87     |
| Akamai (Linode) | $0.100/GB   | 0    | $1.20      | $1.35     | $13.57    | $27.15     | $54.31     | $81.47     |
| Hetzner         | $0.0641/GB  | 0    | $0.77      | $0.87     | $8.70     | $17.40     | $34.81     | $52.22     |

> [!Note]
>
> - Bulk-disk prices: AWS st1, GCP pd-standard, Azure Standard HDD, DigitalOcean
>   Volumes, Akamai Block Storage, Hetzner Volume (€0.0572 at 1 EUR = 1.1214 USD).
>   Each is billed from the first GB; the plans' included local disks hold the fast
>   tier
> - Costs above represent the monthly increment only; total storage costs grow
>   as blockchain history accumulates

## Storage Cost Sources

| Provider        | Price       | Source                                                     | Last Updated |
| --------------- | ----------- | ---------------------------------------------------------- | ------------ |
| AWS             | $0.045/GiB  | https://aws.amazon.com/ebs/pricing/                        | Nov 2026     |
| GCP             | $0.040/GB   | https://cloud.google.com/compute/disks-image-pricing       | Nov 2026     |
| Azure           | $0.040/GiB  | https://azure.microsoft.com/pricing/details/managed-disks/ | Nov 2026     |
| DigitalOcean    | $0.100/GiB  | https://www.digitalocean.com/pricing/                      | Nov 2026     |
| Akamai (Linode) | $0.100/GB   | https://www.linode.com/pricing/                            | Nov 2026     |
| Hetzner         | $0.0641/GB  | https://www.hetzner.com/cloud/pricing                      | Nov 2026     |

Note: Prices may vary by region and volume. Some providers offer free tiers or
volume discounts not reflected in these base rates.
