# Compute (RAM) cost estimation per node

> [!Note] 
> This analysis compares memory requirements between Ouroboros Praos and Linear
> Leios (CIP-164). For detailed technical background on the UTxO DB design,
> see the [technical report](https://github.com/IntersectMBO/ouroboros-consensus/tree/main/docs/tech-reports/utxo-db).

All values use confirmed throughput in TxkB/s (transaction kilobytes per
second reaching the ledger).

UTxO-HD is assumed to have shipped for this comparison. It is an independent
improvement that moves the UTxO set from RAM to disk (an LSM-tree backed store)
and benefits both protocols equally. Leios does not require UTxO-HD more than
Praos does; other than more capacity allowing the utxo set to grow quicker. This
analysis uses **UTxO-HD for both** protocols, as this is the relevant deployment
scenario: UTxO-HD is planned for deployment before Leios, and Leios would
realistically be deployed on top of it.

Without UTxO-HD, the UTxO set (currently ~4–8 GB) would remain in RAM for
both protocols, adding 4–16+ GB to the totals below and making the 4 GB tier
insufficient. That scenario is not modeled here.

## Ouroboros Praos (with UTxO-HD)

With UTxO-HD deployed, Praos no longer keeps the full UTxO set in RAM. The
in-memory footprint is bounded by the hot UTxO cache and other fixed overheads.

### Memory Component Sizes

| Component          | Typical Size | Scaling Factor               |
|--------------------|--------------|------------------------------|
| Base Node Process  | 500 MB       | Fixed                        |
| Hot UTxO Cache     | 200–500 MB   | Configurable                 |
| Indexes            | 100–300 MB   | Logarithmic with ledger size |
| Stake Data         | 200–500 MB   | Linear with stake pools      |
| Block Processing   | 100–200 MB   | Scales with block size       |
| Other Runtime Data | 100–300 MB   | Varies                       |

Fixed subtotal (mid-range): ~1,200 MB ≈ **1.2 GB → 4 GB tier**

## Ouroboros Leios (with UTxO-HD)

Leios uses the same UTxO-HD-backed ledger store as Praos. The additional
Leios-specific RAM components are:

### Key Memory Components

$$M_{\text{leios}} = M_{\text{praos}} + M_{\text{tx-cache}} + M_{\text{consensus}}$$

where beyond the Praos base:

- $M_{\text{tx-cache}}$ = LeiosTxCache: recently seen transactions (scales with throughput)
- $M_{\text{consensus}}$ = Votes in-flight, pending EBs and certificates (50–100 MB, fixed)

### LeiosTxCache

In Linear Leios, transactions are gossiped via the mempool before being
referenced by hash in EBs. Nodes keep a cache of recently seen transactions
to serve peers requesting tx bodies when validating EBs. This cache is bounded
by a time window (approximately 1 hour to cover the full EB → RB pipeline):

$$M_{\text{tx-cache}} = \text{TxkB/s} \times 1{,}000 \text{ B/s} \times 3{,}600 \text{ s}$$

| TxkB/s      | Tx Cache Size               |
|-------------|-----------------------------|
| 4.5 (Praos) | — (not applicable to Praos) |
| 5           | 18 MB                       |
| 50          | 180 MB                      |
| 100         | 360 MB                      |
| 200         | 720 MB                      |
| 300         | 1,080 MB                    |

### Memory Component Sizes (Leios-specific additions)

| Component          | Size           | Scaling Behavior                    |
|--------------------|----------------|-------------------------------------|
| LeiosTxCache       | 18 MB–1,080 MB | Linear with confirmed TxkB/s (1 hr) |
| Consensus Overhead | 50–100 MB      | Fixed (votes in-flight, certs, EBs) |

### RAM Calculation at Different Confirmed Throughputs

Praos base fixed overhead (with UTxO-HD, mid-range estimates):
- Base process: 500 MB
- Hot UTxO cache: 300 MB
- Indexes: 200 MB
- Stake data: 300 MB
- Block/other: 200 MB
- **Praos fixed subtotal: ~1,500 MB ≈ 1.5 GB**

Leios adds consensus overhead (~100 MB) to get ~1.6 GB fixed base.

| TxkB/s      | Tx/s | Tx Cache | Base (GB)       | Total RAM (GB) | Tier Needed |
| ----------- | ---- | -------- | --------------- | -------------- | ----------- |
| 4.5 (Praos) | 3    | —        | 1.5 (Praos)     | **~1.5**       | 4 GB        |
| 5           | 3    | 18 MB    | 1.6 (Leios)     | 1.6            | 4 GB        |
| 50          | 33   | 180 MB   | 1.6             | 1.8            | 4 GB        |
| 100         | 67   | 360 MB   | 1.6             | 2.0            | 4 GB        |
| 200         | 133  | 720 MB   | 1.6             | 2.3            | 4 GB        |
| 300         | 200  | 1,080 MB | 1.6             | 2.7            | 4 GB        |

> [!Note]
>
> - Both Praos and Leios use the 4 GB tier with UTxO-HD deployed
> - The only RAM difference between Praos and Leios is the LeiosTxCache
>   (18 MB–1,080 MB) and consensus overhead (~100 MB) — Leios uses
>   100–1,180 MB more RAM than Praos at the same throughput
> - Tx/s assumes average transaction size of 1,500 bytes
> - GHC runtime overhead (GC, thunks) adds ~20–30% above these estimates
> - Without UTxO-HD, both protocols would need 4–16+ GB additional RAM for
>   the in-memory UTxO set

## Monthly Cost by Cloud Provider ($)

A 4 GB RAM instance is sufficient for both protocols at all throughput levels.
An 8 GB instance is recommended for production deployments to accommodate GHC
runtime overhead and load spikes.

| Provider     | 4 GB RAM | 8 GB RAM | Notes                          |
| ------------ | -------- | -------- | ------------------------------ |
| AWS          | $20.79   | $41.59   | t3 series                      |
| GCP          | $35.95   | $71.91   | n2-standard series             |
| Azure        | $19.50   | $39.00   | Standard_B series              |
| DigitalOcean | $16.28   | $32.56   | Basic Droplets                 |
| Linode       | $21.75   | $43.51   | Dedicated CPU instances        |
| Hetzner      | $4.39    | $7.14    | EUR prices at 1 EUR = 1.10 USD |

> [!Note]
> Monthly costs calculated as: hourly rate × 730 hours/month.
> Prices are for US/EU regions and may vary by location.

### Cost Comparison: Praos vs Leios (both with UTxO-HD)

| Protocol | RAM Required  | Monthly Cost Range  |
| -------- | ------------- | ------------------- |
| Praos    | ~1.5 GB       | $4–$36 (4 GB tier)  |
| Leios    | 1.6–2.7 GB    | $4–$36 (4 GB tier)  |

With UTxO-HD, both Praos and Leios fit comfortably in the same 4 GB RAM tier.
The additional Leios components (LeiosTxCache + consensus overhead) are small
relative to the UTxO-HD savings compared to in-memory UTxO.

## RAM Cost Sources

| Provider     | Instance Type  | Source                                                        | Last Updated |
|--------------|----------------|---------------------------------------------------------------|--------------|
| AWS          | t3 series      | https://aws.amazon.com/ec2/pricing/                           | Apr 2025     |
| GCP          | n2-standard    | https://cloud.google.com/compute/vm-instance-pricing          | Apr 2025     |
| Azure        | Standard_B2s   | https://azure.microsoft.com/pricing/details/virtual-machines/ | Apr 2025     |
| DigitalOcean | Basic Droplets | https://www.digitalocean.com/pricing/droplets                 | Apr 2025     |
| Linode       | Dedicated CPU  | https://www.linode.com/pricing/                               | Apr 2025     |
| Hetzner      | CX23/CX33      | https://www.hetzner.com/cloud/pricing                         | Apr 2026     |

> [!Note]
> Prices shown are based on standard/on-demand rates. Many providers offer
> significant discounts for reserved instances or longer-term commitments.
