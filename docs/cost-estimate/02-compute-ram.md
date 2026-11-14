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
both protocols, adding 4–16+ GB to the totals below; cardano-node 11.1.3 asks
for 24 GB of RAM with its in-memory backend. That scenario is not modeled here.

## Ouroboros Praos (with UTxO-HD)

With UTxO-HD deployed, Praos no longer keeps the full UTxO set in RAM. What it
still holds was measured on an LSM mainnet node:

### Measured Memory

| Measurement | Value | Source |
|-------------|-------|--------|
| Resident memory of our LSM mainnet node at the chain tip (cardano-node 11.0.1, V2LSM, no memory limit, sampled every minute for 2 h) | 5.58 GB, flat; GHC heap 5.5 GB; live data 1.4–3.1 GB (median 1.9 GB) | Node metrics and `/proc`, 2026-11-10 |
| Recommended RAM for an LSM block producer with a mainnet-sized UTxO set and delegation map | 8 GiB | Cardano Performance & Tracing team, cardano-node 11.2.1 (2026-11-10) |
| cardano-node minimum system requirements | 8 GB with the `OnDisk` backend (pending confirmation); 24 GB in memory | [cardano-node 11.1.3 release notes](https://github.com/IntersectMBO/cardano-node/releases/tag/11.1.3) |

Praos base: ~5.6 GB measured **→ 8 GiB tier**

## Ouroboros Leios (with UTxO-HD)

Leios uses the same UTxO-HD-backed ledger store as Praos. The additional
Leios-specific RAM components are:

### Key Memory Components

$$M_{\text{leios}} = M_{\text{praos}} + M_{\text{tx-cache}} + M_{\text{recent}} + M_{\text{consensus}}$$

where beyond the Praos base:

- $M_{\text{tx-cache}}$ = LeiosTxCache: a fixed table of $2^{22}$ slots, about 160 MiB
  (`Ouroboros/Consensus/Node.hs` on the `leios-prototype` branch of ouroboros-consensus)
- $M_{\text{recent}}$ = the ledger's in-memory record of the last $k$ = 2,160 blocks
  (about 12 hours), which grows with the transactions those blocks carry
- $M_{\text{consensus}}$ = votes in flight, pending EBs and certificates (50–100 MB, fixed)

### What grows with throughput

The LeiosTxCache stays the same size at any throughput, and transaction bytes are
stored in the LeiosDb on disk. What grows is the record of the last $k$ blocks: at
M1 capacity they carry about 1.1 M transactions, at M2 about 3.0 M.

The feasibility report measures the growth on its cluster, which keeps a
mainnet-sized ledger in memory: the resident set is 12.9 GB with 260 kB EBs and
13.8 to 14.1 GB with 1 MB EBs, **0.9 to 1.2 GB more** for that step. No LSM node
has been measured with Leios EBs yet.

### RAM by Parameter Set

Praos base: **~5.6 GB**, the measured resident memory of an LSM mainnet node
(above).

| Parameter set     | RAM (GB)      | Basis                                                                       | 8 GiB tier (8.6 GB) |
| ----------------- | ------------- | --------------------------------------------------------------------------- | ------------------- |
| Praos             | 5.6           | Measured on an LSM mainnet node                                             | Fits                |
| M0 (260 kB EBs)   | about 5.9     | Praos + LeiosTxCache (0.17 GB) + consensus overhead (0.1 GB); not measured  | Fits                |
| M1 (1 MB EBs)     | about 7       | M0 + the 0.9–1.2 GB step the feasibility report measured from 260 kB to 1 MB | Fits                |
| M2 (3 MB EBs)     | about 9–10    | Extrapolated from that step; not measured                                   | May not fit         |

> [!Note]
>
> - The Praos base is measured, GHC runtime included; every Leios figure above
>   is an estimate until an LSM node is measured with 1 and 3 MB EBs
> - The cost estimator keeps 8 GiB per node at every parameter set; at M2 a
>   12 GiB node would add about $27 a month to a pool of three nodes on
>   Hyperscale prices, $30 on Discount
> - Without UTxO-HD, both protocols would need 4–16+ GB additional RAM for
>   the in-memory UTxO set

## Monthly Cost by Cloud Provider ($)

An 8 GiB instance covers Praos and Leios up to M1: the measured ~5.6 GB plus
Leios's additions, with room for load spikes. At M2 it may not (see above).

| Provider        | 4 GB RAM | 8 GB RAM | Notes                                                  |
| --------------- | -------- | -------- | ------------------------------------------------------ |
| AWS             | $10.64   | $21.28   | $2.66/GiB-month, from m7i.large                        |
| GCP             | $8.52    | $17.04   | $2.13/GiB-month, from e2-standard-2                    |
| Azure           | $7.60    | $15.20   | $1.90/GiB-month, from D2as v6                          |
| DigitalOcean    | $11.08   | $22.16   | $2.77/GiB-month, from g-2vcpu-8gb                      |
| Akamai (Linode) | $12.28   | $24.56   | $3.07/GiB-month, from Dedicated G7 8 GB                |
| Hetzner         | $6.96    | $13.92   | $1.74/GiB-month, from CCX13; EUR at 1 EUR = 1.1214 USD |

> [!Note]
> RAM's share of each provider's 2 vCPU / 8 GiB instance price, the split the cost
> estimator's presets use (on-demand list prices checked on 2026-11-10; see the
> README, "November 2026 update"). Prices are for US regions (Hetzner: Germany) and
> may vary by location.

### Cost Comparison: Praos vs Leios (both with UTxO-HD)

| Protocol | RAM Required  | Monthly Cost Range  |
| -------- | ------------- | ------------------- |
| Praos    | ~5.6 GB       | $14–$25 (8 GiB tier) |
| Leios    | about 5.9–7 GB up to M1; about 9–10 GB at M2 (estimates) | $14–$25 (8 GiB tier) up to M1 |

With UTxO-HD, Praos and Leios up to M1 fit in the same 8 GiB RAM tier. The
additional Leios components are small relative to the UTxO-HD savings compared
to in-memory UTxO; at M2 they may need a larger tier.

## RAM Cost Sources

| Provider     | Instance Type  | Source                                                        | Last Updated |
|--------------|----------------|---------------------------------------------------------------|--------------|
| AWS          | m7i.large      | https://aws.amazon.com/ec2/pricing/                           | Nov 2026     |
| GCP          | e2-standard-2  | https://cloud.google.com/compute/vm-instance-pricing          | Nov 2026     |
| Azure        | D2as v6        | https://azure.microsoft.com/pricing/details/virtual-machines/ | Nov 2026     |
| DigitalOcean | g-2vcpu-8gb    | https://www.digitalocean.com/pricing/droplets                 | Nov 2026     |
| Akamai (Linode) | Dedicated G7 8 GB | https://www.linode.com/pricing/                         | Nov 2026     |
| Hetzner      | CCX13          | https://www.hetzner.com/cloud/pricing                         | Nov 2026     |

> [!Note]
> Prices shown are based on standard/on-demand rates. Many providers offer
> significant discounts for reserved instances or longer-term commitments.
