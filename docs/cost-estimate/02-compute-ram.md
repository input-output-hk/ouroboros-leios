# Compute (RAM) cost estimation per node

> [!Note] 
> This analysis compares memory requirements between Ouroboros Praos and Linear
> Leios (CIP-164). For detailed technical background on the UTxO DB design,
> see the [technical report](https://github.com/IntersectMBO/ouroboros-consensus/tree/main/docs/tech-reports/utxo-db).

All values use confirmed throughput in TxkB/s (transaction kilobytes per
second reaching the ledger).

## Ouroboros Praos

In Ouroboros Praos, the entire ledger state is stored in memory, creating a
direct correlation between ledger size and RAM requirements.

### Memory Component Sizes

| Component            | Typical Size | Scaling Factor             |
| -------------------- | ------------ | -------------------------- |
| Base Node Process    | 500 MB       | Fixed                      |
| UTxO Set             | 4–8 GB       | Linear with network usage  |
| Stake Data           | 200–500 MB   | Linear with stake pools    |
| Mempool              | 64–128 MB    | Configurable               |
| Block Processing     | 100–200 MB   | Scales with block size     |
| Other Runtime Data   | 200–500 MB   | Varies                     |

At today's ledger size (~8 million UTxO entries), Praos requires approximately
13–16 GB of RAM. As UTxO growth continues, RAM requirements grow proportionally.

At Praos-equivalent load (4.5 TxkB/s), Leios processes the same transactions
and needs the same LeiosTxCache size, but uses fundamentally less RAM because
UTxO-HD moves the UTxO set to disk. Praos requires ~16 GB RAM for the
in-memory UTxO set; Leios requires only ~4 GB regardless of UTxO growth.

## Ouroboros Leios

Linear Leios (CIP-164) solves the memory scaling problem by requiring UTxO-HD,
which moves most of the UTxO set to disk. The in-memory footprint is bounded
regardless of ledger history size.

### Key Memory Components

$$M_{\text{leios}} = M_{\text{base}} + M_{\text{utxo-cache}} + M_{\text{indexes}} + M_{\text{tx-cache}} + M_{\text{stake}} + M_{\text{consensus}}$$

where:

- $M_{\text{base}}$ = Base process memory (500 MB)
- $M_{\text{utxo-cache}}$ = Hot UTxO cache for recent reads (200–500 MB, configurable)
- $M_{\text{indexes}}$ = In-memory indexes and Bloom filters (100–300 MB)
- $M_{\text{tx-cache}}$ = LeiosTxCache: recently seen transactions (scales with throughput)
- $M_{\text{stake}}$ = Stake distribution data (200–500 MB, ~3,000 pools)
- $M_{\text{consensus}}$ = Votes in-flight, pending EBs and certificates (50–100 MB, fixed)

### LeiosTxCache

In Linear Leios, transactions are gossiped via the mempool before being
referenced by hash in EBs. Nodes keep a cache of recently seen transactions
to serve peers requesting tx bodies when validating EBs. This cache is bounded
by a time window (approximately 1 hour to cover the full EB → RB pipeline):

$$M_{\text{tx-cache}} = \text{TxkB/s} \times 1{,}000 \text{ B/s} \times 3{,}600 \text{ s}$$

| TxkB/s      | Tx Cache Size |
| ----------- | ------------- |
| 4.5 (Praos) | N/A (Leios cache not used; Praos keeps full UTxO in-memory: ~16 GB total) |
| 5           | 18 MB         |
| 50          | 180 MB        |
| 100         | 360 MB        |
| 200         | 720 MB        |
| 300         | 1,080 MB      |

### Memory Component Sizes

| Component              | Size           | Scaling Behavior                        |
| ---------------------- | -------------- | --------------------------------------- |
| Base Node Process      | 500 MB         | Fixed                                   |
| Hot UTxO Cache         | 200–500 MB     | Configurable; bounded by UTxO-HD design |
| Indexes & Bloom Filters| 100–300 MB     | Logarithmic with ledger size            |
| LeiosTxCache           | 16 MB–1,080 MB | Linear with confirmed TxkB/s (1 hr)     |
| Stake Data             | 200–500 MB     | Linear with stake pool count            |
| Consensus Overhead     | 50–100 MB      | Fixed (votes in-flight, certs, EBs)     |

### RAM Calculation at Different Confirmed Throughputs

Base fixed overhead (mid-range estimates):
- Base process: 500 MB
- UTxO cache: 300 MB
- Indexes: 200 MB
- Stake data: 300 MB
- Consensus overhead: 100 MB
- **Fixed subtotal: ~1,400 MB ≈ 1.4 GB**

| TxkB/s        | Tx/s | Tx Cache | Base (GB) | Total RAM (GB) | Tier Needed |
| ------------- | ---- | -------- | --------- | -------------- | ----------- |
| 4.5 (Praos)   | 3    | N/A      | ~15–16    | **~16**        | 16 GB       |
| 5             | 3    | 18 MB    | 1.4       | 1.5            | 4 GB        |
| 50            | 33   | 180 MB   | 1.4       | 1.6            | 4 GB        |
| 100           | 67   | 360 MB   | 1.4       | 1.8            | 4 GB        |
| 200           | 133  | 720 MB   | 1.4       | 2.1            | 4 GB        |
| 300           | 200  | 1,080 MB | 1.4       | 2.5            | 4 GB        |

> [!Note]
>
> - The 4.5 (Praos) row reflects Praos memory requirements (full UTxO in RAM);
>   all Leios rows use UTxO-HD, making the 4 GB tier sufficient
> - Tx/s assumes average transaction size of 1,500 bytes
> - A 4 GB tier provides comfortable headroom for all Leios throughput levels
> - GHC runtime overhead (GC, thunks) adds ~20–30% above these estimates
> - UTxO-HD is a prerequisite for Linear Leios; without it, the UTxO set grows
>   to 4–16+ GB in RAM as in Praos

## Monthly Cost by Cloud Provider ($)

A 4 GB RAM instance is sufficient for all throughput levels up to 300 TxkB/s.
An 8 GB instance is recommended for production deployments to accommodate GHC
runtime overhead and load spikes.

| Provider     | 4 GB RAM | 8 GB RAM | 16 GB RAM | Notes                          |
| ------------ | -------- | -------- | --------- | ------------------------------ |
| AWS          | $20.79   | $41.59   | $83.18    | t3 series                      |
| GCP          | $35.95   | $71.91   | $143.82   | n2-standard series             |
| Azure        | $19.50   | $39.00   | $78.00    | Standard_B series              |
| DigitalOcean | $16.28   | $32.56   | $65.12    | Basic Droplets                 |
| Linode       | $21.75   | $43.51   | $87.02    | Dedicated CPU instances        |
| Hetzner      | $4.39    | $7.14    | $12.42    | EUR prices at 1 EUR = 1.10 USD |

> [!Note]
> Monthly costs calculated as: hourly rate × 730 hours/month.
> Prices are for US/EU regions and may vary by location.
> 16 GB RAM tier shown for Praos comparison; Leios uses the 4 GB tier.

### Cost Comparison: Praos vs Leios

| Protocol | RAM Required  | Monthly Cost Range     |
| -------- | ------------- | ---------------------- |
| Praos    | 13–16 GB      | $12–$144 (16 GB tier)  |
| Leios    | 1.5–2.5 GB    | $4–$36 (4 GB tier)     |

Leios with UTxO-HD reduces RAM costs by approximately 75–85% by moving the
UTxO set to SSD storage, partially offsetting the fixed vote/cert overhead.

## RAM Cost Sources

| Provider      | Instance Type      | Source                                                 | Last Updated |
| ------------- | ------------------ | ------------------------------------------------------ | ------------ |
| AWS           | t3 series          | https://aws.amazon.com/ec2/pricing/                    | Apr 2025     |
| GCP           | n2-standard        | https://cloud.google.com/compute/vm-instance-pricing   | Apr 2025     |
| Azure         | Standard_B2s       | https://azure.microsoft.com/pricing/details/virtual-machines/ | Apr 2025 |
| DigitalOcean  | Basic Droplets     | https://www.digitalocean.com/pricing/droplets          | Apr 2025     |
| Linode        | Dedicated CPU      | https://www.linode.com/pricing/                        | Apr 2025     |
| Hetzner       | CX23/CX33          | https://www.hetzner.com/cloud/pricing                  | Apr 2026     |

> [!Note]
> Prices shown are based on standard/on-demand rates. Many providers offer
> significant discounts for reserved instances or longer-term commitments.
