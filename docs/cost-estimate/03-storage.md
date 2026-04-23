# Storage cost estimation per node

> [!Note] 
>
> **100% confirmed throughput assumption:**
>
> This analysis assumes fully utilized confirmed throughput for a conservative
> upper bound on costs. Storage accumulates only for certified (confirmed)
> transactions — uncertified EB contents are discarded and re-gossiped in
> subsequent rounds.
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

### Ledger State

In addition to blockchain history, nodes maintain ledger state on disk
(UTxO-HD prerequisite for Leios):

- Current approximate size: 200 GiB (as of April 2025)
- Growth rate depends on the net UTxO set change over time (not directly
  proportional to throughput)

## Ouroboros Leios

In Linear Leios (CIP-164), transactions are gossiped via the mempool and
referenced by hash in Endorsement Blocks (EBs). Only the transactions in
**certified** EBs are permanently stored. An EB is certified when a quorum of
votes arrives before the certification deadline; $P(\text{certified}) \approx 0.48$.

### Storage Components

| Component           | Description                             | Scales With      |
| ------------------- | --------------------------------------- | ---------------- |
| Tx closure data     | Confirmed transaction bytes             | TxkB/s           |
| EB body (tx hashes) | 32-byte tx references in certified EBs  | TxkB/s           |
| EB headers          | One EB header per RB opportunity        | Fixed (0.05/s)   |
| RB (header + cert)  | Ranking blocks with embedded certificate| Fixed (0.05/s)   |

> [!Note]
> Votes are ephemeral and not persisted to disk. They are used to produce
> certificates, which are included in the subsequent Ranking Block.

### Storage Formulas

1. **Transaction Closure Storage** (dominant):

   $$S_{\text{tx}} = \text{TxkB/s} \times 1{,}000 \times T_{\text{month}}$$

   where $T_{\text{month}} = 2{,}628{,}000$ seconds/month.

2. **EB Body Storage** (tx hash references, stored for all EBs):

   In the asymptotic steady-state model, every transaction eventually appears
   in exactly one persisted EB body. The P(certified) factor cancels — whether
   we count all EBs at rate $R_{\text{eb}}$ or only certified EBs with a
   correspondingly larger body, the total stored hash-reference bytes are the
   same:

   $$S_{\text{eb-body}} = \frac{\text{TxkB/s} \times 1{,}000}{S_{\text{tx-avg}}} \times 32 \text{ bytes/s} \times T_{\text{month}}$$

   where:
   - $S_{\text{tx-avg}}$ = average transaction size (1,500 bytes)
   - 32 bytes per tx hash reference

3. **EB Header Storage** (all EBs, fixed):

   $$S_{\text{eb-hdr}} = 0.05 \times 240 \times T_{\text{month}} = 0.029 \text{ GiB/month}$$

4. **RB Storage** (header + certificate, fixed):

   $$S_{\text{rb}} = 0.05 \times 9{,}024 \times T_{\text{month}} = 1.105 \text{ GiB/month}$$

   where 9,024 bytes = 1,024 B header + 8,000 B certificate (`cert-size-bytes-constant`).

### Storage Calculation at 4.5 TxkB/s (Praos-equivalent)

1. **Tx closure**: $4{,}500 \times 2{,}628{,}000 = 11{,}826{,}000{,}000 \text{ bytes} \approx 11.01 \text{ GiB}$

2. **EB body** (tx hashes): $\frac{4{,}500}{1{,}500} \times 32 \times 2{,}628{,}000 = 3 \times 32 \times 2{,}628{,}000 \approx 0.235 \text{ GiB}$

3. **EB headers**: $0.029 \text{ GiB}$ (fixed)

4. **RB**: $1.105 \text{ GiB}$ (fixed; 1,024 B header + 8,000 B cert)

5. **Total**: $11.01 + 0.235 + 0.029 + 1.105 \approx 12.38 \text{ GiB/month}$

This is approximately 12% more than Praos (11.02 GiB) at equivalent throughput.

### Monthly Storage at Different Confirmed Throughputs

| TxkB/s | Tx/s | Tx Closure  | EB Body    | EB Headers | RB        | Total       | vs Praos |
| ------ | ---- | ----------- | ---------- | ---------- | --------- | ----------- | -------- |
| 4.5    | 3    | 11.01 GiB   | 0.235 GiB  | 0.03 GiB   | 1.105 GiB | 12.38 GiB   | +12%     |
| 50     | 33   | 122.4 GiB   | 2.613 GiB  | 0.03 GiB   | 1.105 GiB | 126.1 GiB   | +1,045%  |
| 100    | 67   | 244.8 GiB   | 5.226 GiB  | 0.03 GiB   | 1.105 GiB | 251.2 GiB   | +2,180%  |
| 150    | 100  | 367.2 GiB   | 7.840 GiB  | 0.03 GiB   | 1.105 GiB | 376.2 GiB   | +3,314%  |
| 200    | 133  | 489.5 GiB   | 10.453 GiB | 0.03 GiB   | 1.105 GiB | 501.1 GiB   | +4,447%  |
| 250    | 167  | 611.9 GiB   | 13.066 GiB | 0.03 GiB   | 1.105 GiB | 626.1 GiB   | +5,580%  |
| 300    | 200  | 734.3 GiB   | 15.679 GiB | 0.03 GiB   | 1.105 GiB | 751.1 GiB   | +6,714%  |

> [!Note]
>
> - Tx/s assumes average transaction size of 1,500 bytes
> - EB body storage grows with throughput because higher-throughput EBs reference
>   more transaction hashes (32 bytes each)
> - These are monthly increments; total accumulated storage grows over time
> - CIP-164 Table 8 cross-check: 394 GB at 150 TxkB/s → our total 376 GiB ≈
>   404 GB; 526 GB at 200 TxkB/s → our total 501 GiB ≈ 538 GB (minor
>   difference from rounding and avg tx size assumptions)

### Storage Component Analysis at 200 TxkB/s

| Component        | Storage    | % of Total |
| ---------------- | ---------- | ---------- |
| Tx Closure Data  | 489.5 GiB  | 97.7%      |
| EB Body (hashes) | 10.453 GiB | 2.1%       |
| RB               | 1.105 GiB  | 0.2%       |
| EB Headers       | 0.03 GiB   | < 0.1%     |

Transaction closure data dominates at all throughput levels. The EB body
(tx hash references) adds ~2% overhead.

## Cost Analysis

### Monthly Storage Cost by Cloud Provider ($)

Storage is billed per GB (10⁹ bytes); 1 GiB ≈ 1.074 GB.

| Provider        | Price/GB | Free (GB) | 4.5 TxkB/s | 50 TxkB/s | 100 TxkB/s | 150 TxkB/s | 200 TxkB/s | 250 TxkB/s | 300 TxkB/s |
| --------------- | -------- | --------- | ---------- | --------- | ---------- | ---------- | ---------- | ---------- | ---------- |
| AWS             | $0.080   | 100       | $0.00      | $2.71     | $13.34     | $23.96     | $34.58     | $45.20     | $55.83     |
| GCP             | $0.040   | 0         | $0.52      | $5.36     | $10.67     | $15.98     | $21.29     | $26.60     | $31.92     |
| Azure           | $0.075   | 100       | $0.00      | $2.54     | $12.50     | $22.46     | $32.42     | $42.38     | $52.34     |
| DigitalOcean    | $0.100   | 100       | $0.00      | $3.39     | $16.67     | $29.95     | $43.22     | $56.50     | $69.79     |
| Linode          | $0.100   | 1,024     | $0.00      | $0.00     | $0.00      | $0.00      | $0.00      | $0.00      | $0.00      |
| Hetzner         | $0.063   | 0         | $0.83      | $8.44     | $16.80     | $25.17     | $33.53     | $41.89     | $50.26     |

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
