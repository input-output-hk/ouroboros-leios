# Storage cost estimation per node

> [!Note] 
>
> **Scope**: This document covers **blockchain history** storage only —
> the append-only chain data (blocks, EBs, transactions). It does not model
> ledger state storage (UTxO set on disk under UTxO-HD, currently ~200 GiB
> and growing with network usage independent of throughput). Ledger state
> growth is orthogonal to the protocol comparison and not proportional to
> confirmed TxkB/s.
>
> **100% confirmed throughput assumption:**
> Storage accumulates only for certified (confirmed) transactions —
> uncertified EB contents are discarded and re-gossiped in subsequent rounds.
>
> **Compression note:** While early experiments show that >70% compression is
> feasible on mainnet data, this analysis does not include compression benefits.
> The calculations represent raw storage requirements without compression.

All values use confirmed throughput in TxkB/s (transaction kilobytes per
second reaching the ledger). Seconds per month: 2,628,000 (30.4167 days).

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

$$S_{\text{praos}} = 91{,}136 \times 0.05 \times 2{,}628{,}000 \approx 11.02 \text{ GiB/month}$$

The Praos-equivalent confirmed throughput is $0.05 \times 90{,}112 = 4{,}505.6 \approx 4.5 \text{ TxkB/s}$.

At confirmed throughput at or below the Praos capacity ceiling (4.5 TxkB/s),
Linear Leios stores the same transaction bytes as Praos plus fixed protocol
overhead (EB headers, RBs with certificates). The overhead is small (~24% at
5 TxkB/s) and amortized as throughput grows.

## Ouroboros Leios

In Linear Leios (CIP-164), transactions are gossiped via the mempool and
referenced by hash in Endorsement Blocks (EBs). Only the transactions in
**certified** EBs are permanently stored. An EB is certified when a quorum of
votes arrives before the certification deadline.

### Storage Components

| Component           | Description                             | Scales With      |
| ------------------- | --------------------------------------- | ---------------- |
| Tx closure data     | Confirmed transaction bytes             | TxkB/s           |
| EB body (tx hashes) | 32-byte tx references in certified EBs  | TxkB/s           |
| EB headers          | Headers of certified EBs only           | Fixed (0.024/s)  |
| RB (header + cert)  | Ranking blocks with embedded certificate| Fixed (0.05/s)   |

> [!Note]
> Votes are ephemeral and not persisted to disk. They are used to produce
> certificates, which are included in the subsequent Ranking Block.

### Storage Formulas

1. **Transaction Closure Storage** (dominant):

   $$S_{\text{tx}} = \text{TxkB/s} \times 1{,}000 \times T_{\text{month}}$$

   where $T_{\text{month}} = 2{,}628{,}000$ seconds/month.

2. **EB Body Storage** (tx hash references, certified EBs only):

   Only certified EB bodies are stored. Each certified EB body is correspondingly
   larger — it must reference $1/P_{\text{cert}}$ more transactions than a
   world where all EBs were certified — so the $P_{\text{cert}}$ factor cancels
   and total stored bytes are independent of certification probability:

   $$S_{\text{eb-body}} = \frac{\text{TxkB/s} \times 1{,}000}{S_{\text{tx-avg}}} \times 32 \text{ bytes/s} \times T_{\text{month}}$$

   where:
   - $S_{\text{tx-avg}}$ = average transaction size (1,500 bytes)
   - 32 bytes per tx hash reference

   Note: EB headers do not share this cancellation — their size is fixed at
   240 bytes regardless of body fill, so only storing certified EB headers
   (at $R_{\text{cert}} = 0.024$/s) genuinely reduces header storage by $P_{\text{cert}}$.

3. **EB Header Storage** (certified EBs only, fixed):

   Uncertified EBs are discarded after the certification deadline; only certified
   EB headers are kept on disk.

   $$S_{\text{eb-hdr}} = R_{\text{cert}} \times 240 \times T_{\text{month}} = 0.024 \times 240 \times 2{,}628{,}000 \approx 0.014 \text{ GiB/month}$$

4. **RB Storage** (header + certificate, fixed):

   $$S_{\text{rb}} = 0.05 \times 9{,}024 \times T_{\text{month}} = 1.105 \text{ GiB/month}$$

   where 9,024 bytes = 1,024 B header + 8,000 B certificate (`cert-size-bytes-constant`).

### Storage Calculation at 5 TxkB/s (Leios Baseline)

1. **Tx closure**: $5{,}000 \times 2{,}628{,}000 = 13{,}140{,}000{,}000 \text{ bytes} \approx 12.24 \text{ GiB}$

2. **EB body** (tx hashes): $\frac{5{,}000}{1{,}500} \times 32 \times 2{,}628{,}000 = 3.33 \times 32 \times 2{,}628{,}000 \approx 0.261 \text{ GiB}$

3. **EB headers**: $0.014 \text{ GiB}$ (certified only, $R_{\text{cert}} = 0.024$/s)

4. **RB**: $1.105 \text{ GiB}$ (fixed; 1,024 B header + 8,000 B cert)

5. **Total**: $12.24 + 0.261 + 0.014 + 1.105 \approx 13.62 \text{ GiB/month}$

This is approximately 24% more than Praos (11.02 GiB). The fixed RB+cert overhead
(1.134 GiB) accounts for most of the difference at low throughput.

### Monthly Storage at Different Confirmed Throughputs

| TxkB/s      | Tx/s | Tx Closure | EB Body    | EB Headers | RB        | Total         | vs Praos |
|-------------|------|------------|------------|------------|-----------|---------------|----------|
| 4.5 (Praos) | 3    | 11.02 GiB  | —          | —          | —         | **11.02 GiB** | —        |
| 5           | 3    | 12.24 GiB  | 0.261 GiB  | 0.01 GiB   | 1.105 GiB | 13.62 GiB     | +24%     |
| 50          | 33   | 122.4 GiB  | 2.613 GiB  | 0.01 GiB   | 1.105 GiB | 126.1 GiB     | +1,045%  |
| 100         | 67   | 244.8 GiB  | 5.226 GiB  | 0.01 GiB   | 1.105 GiB | 251.1 GiB     | +2,180%  |
| 200         | 133  | 489.5 GiB  | 10.453 GiB | 0.01 GiB   | 1.105 GiB | 501.1 GiB     | +4,447%  |
| 300         | 200  | 734.3 GiB  | 15.679 GiB | 0.01 GiB   | 1.105 GiB | 751.1 GiB     | +6,714%  |

> [!Note]
>
> - The 4.5 (Praos) row shows the Praos protocol baseline (block history only,
>   no EB/vote/cert overhead)
> - Tx/s assumes average transaction size of 1,500 bytes
> - EB body storage grows with throughput because higher-throughput EBs reference
>   more transaction hashes (32 bytes each)
> - These are monthly increments; total accumulated storage grows over time
> - CIP-164 Table 8 cross-check: 526 GB at 200 TxkB/s → our total 501 GiB ≈
>   538 GB (minor difference from rounding and avg tx size assumptions)

### Storage Component Analysis at 200 TxkB/s

| Component            | Storage    | % of Total |
|----------------------|------------|------------|
| Tx Closure Data      | 489.5 GiB  | 97.7%      |
| RB with certificates | 1.105 GiB  | 0.2%       |
| EB Body (hashes)     | 10.453 GiB | 2.1%       |
| EB Headers           | 0.01 GiB   | < 0.1%     |

Transaction closure data dominates at all throughput levels. The overhead of
Linear Leios is dominated by tx hash references in EB bodies at ~2%, which could
even be avoided. The certificate overhead is not avoidable but only makes up
0.2%.

## Cost Analysis

### Monthly Storage Cost by Cloud Provider ($)

Storage is billed per GB (10⁹ bytes); 1 GiB ≈ 1.074 GB.

| Provider        | Price/GB | Free (GB) | 4.5 (Praos) | 5 TxkB/s | 50 TxkB/s | 100 TxkB/s | 200 TxkB/s | 300 TxkB/s |
| --------------- | -------- | --------- | ----------- | --------- | --------- | ---------- | ---------- | ---------- |
| AWS             | $0.080   | 100       | $0.00       | $0.00     | $2.71     | $13.34     | $34.58     | $55.83     |
| GCP             | $0.040   | 0         | $0.47       | $0.59     | $5.36     | $10.67     | $21.29     | $31.92     |
| Azure           | $0.075   | 100       | $0.00       | $0.00     | $2.54     | $12.50     | $32.42     | $52.34     |
| DigitalOcean    | $0.100   | 100       | $0.00       | $0.00     | $3.39     | $16.67     | $43.22     | $69.79     |
| Linode          | $0.100   | 1,024     | $0.00       | $0.00     | $0.00     | $0.00      | $0.00      | $0.00      |
| Hetzner         | $0.063   | 0         | $0.74       | $0.92     | $8.44     | $16.80     | $33.53     | $50.26     |

> [!Note]
>
> - Linode includes up to 1,024 GB storage free with compute instances; all
>   throughput levels fit within this allowance for the first ~1.4 months before
>   cumulative history exceeds the free tier
> - Costs above represent the monthly increment only; total storage costs grow
>   as blockchain history accumulates
> - AWS free tier is 100 GB/month on gp3 EBS volumes (new accounts only)

## Storage Cost Sources

| Provider        | Price/GB | Source                                                     | Last Updated |
| --------------- | -------- | ---------------------------------------------------------- | ------------ |
| AWS             | $0.080   | https://aws.amazon.com/ebs/pricing/                        | 2023         |
| GCP             | $0.040   | https://cloud.google.com/compute/disks-image-pricing       | Feb 2025     |
| Azure           | $0.075   | https://azure.microsoft.com/pricing/details/managed-disks/ | Dec 2024     |
| DigitalOcean    | $0.100   | https://www.digitalocean.com/pricing/                      | Apr 2025     |
| Linode          | $0.100   | https://www.linode.com/pricing/                            | Apr 2023     |
| Hetzner         | $0.063   | https://www.hetzner.com/cloud/pricing                      | Apr 2026     |

Note: Prices may vary by region and volume. Some providers offer free tiers or
volume discounts not reflected in these base rates.
