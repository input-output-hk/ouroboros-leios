# Leios Node Operating Costs Analysis

## Overview

This document provides a list of cost items used for our analysis of the
operational costs associated with running a Leios node. As a baseline we use
Ouroboros Praos for comparisons. All cost estimates are for **Linear Leios
(CIP-164)** and assume fully confirmed transaction throughput (TxkB/s:
transaction kilobytes per second reaching the ledger). Costs are central
estimates for the launch design: 600 votes per EB (one per committee seat), each
vote pushed to every downstream peer, individual BLS vote verification, and 100%
confirmed block utilization. Egress is likely understated: some of the traffic a
relay sends is not modelled yet (see [04-egress.md](./04-egress.md)). CPU costs use
**mainnet-average demand** (including organic Plutus usage as measured on
Cardano mainnet); Plutus-heavy workloads will cost more.

### November 2026 update

The [cost estimator](https://leios.cardano-scaling.org/cost-estimator/) was updated
with the smallest set of changes that bring it in line with the current protocol,
implementation and prices. The figures in 01 and 03 to 05 and the tables below were
regenerated from the estimator's model, and the provider prices in 01 to 05 and in the
tables below are the November 2026 ones listed under **Prices**.

- **Committee:** 600 seats of a stake-based committee (CIP-164), one vote per seat per
  EB: a launch choice, below CIP-164's recommended 900, to limit vote traffic. 600 seats
  cover about 95% of active stake (CIP-164 Table 7a: 590 seats at epoch 649, 20 points of
  headroom over the 75% quorum); 900 seats would add about $43 a month on Hyperscale
  prices at every parameter set, nothing on Discount. Vote 91 B (88 B vote plus 3 B framing; ouroboros-consensus golden test), vote
  validation 0.67 ms (one BLS check). Certificate 54 B + one bit per seat (129 B; a
  certifying RB body on MusashiNet is 75 B with a 21 B bitfield), validated in 0.9 ms
  + 1.9 µs per seat. These replace the wFA+LS figures (164 B, 2.9 ms, 8,000 B, 157.2 ms).
- **Vote traffic as implemented:** a node pushes each vote once to every downstream
  peer (CIP-164 LeiosNotify; ouroboros-consensus PR #2430; pull-based diffusion
  deferred for launch, ouroboros-leios#1073). This replaces the spanning-tree × 2
  model: about 401 GiB a month per relay at 60 downstream peers, against 24 GiB before.
- **Downstream peers:** 60 per relay, down from 100: a mid-level pool's relay. The
  best-connected relays of large pools carry about 100 (MusashiNet's IOG relays: 92 hot
  downstream and 115 inbound peers on average, 7 days to 2026-11-12). The figures in this
  README are for a mid-level pool; at 100 peers Hyperscale adds $56 to $63 a month more,
  and Discount doesn't change.
- **Fetch multiplicity:** 2 by default, up from 1. The Leios fetch logic requests an EB
  from every peer that offers it before it arrives. The egress devnet measured about 1.5
  to 2 copies of each EB body, and MusashiNet's relays downloaded each EB body 3.25 times
  (7 days to 2026-11-12). It applies to EB bodies only: Praos blocks, certificates
  included, are fetched from one peer (BlockFetch's MaxConcurrencyDeadline, default 1), so
  they always use M = 1. The tables in 04 show lean (M = 1) and beefy (M = 4) EB fetching.
- **No Leios below Praos capacity:** CIP-164 announces EBs only when transactions don't
  fit in the RB, so at or below 4.5 TxkB/s there are no EBs, votes or certificates.
- **Split storage:** each node puts its volatile path (`--volatile-database-path`) on a
  fast SSD and its immutable path (`--immutable-database-path`) on a bulk disk. The SSD
  is 10 GiB per node: the UTxO set's LSM tables twice over (2 × 3.2 GiB, so a full merge
  fits), three ledger snapshots (3 × 0.49 GiB) and the VolatileDB (2,160 full RBs) need
  8.05 GiB, and the rest is headroom. On top come the UTxO growth at the average load (one
  new entry per 11.6 kB of transactions, 2 × 316 B each on the SSD) and, with Leios, the
  fetched EB bodies and the EB closures' transactions, each once, until 2,160 blocks deep.
  The bulk disk holds the immutable chain (235 GB, plus its growth). Sizes come from an
  LSM mainnet node (cardano-node 11.0.1, 2026-11-11), which uses 4.2 GiB on its volatile
  path. The UTxO growth rate is mainnet's over epochs 589–661 (db-sync): an epoch with
  1 MB more transactions had 85.9 more net new entries, although over the whole year the
  UTxO set shrank slightly (−7.9 entries per MB).
- **Disks grow with the chain:** a pool provisions what its nodes need today plus a margin of
  growth (2 months by default) and enlarges the disks as the chain grows, since cloud volumes
  resize in place; a full day at M2 capacity adds about 7 GB per node. The storage line is
  the average over the first 12 months (both are inputs): month *m* holds *m* − 1 + margin
  months of growth, so the average holds (12 − 1) ÷ 2 + 2 = 7.5. Beside it the page shows
  the first month's bill and how much it rises each month: at M2 and 100% load on
  Hyperscale prices, $88 in the first month, rising $28 a month, $245 on average. The
  estimator on main provisions a full year of growth from the first month.
- **Compression:** 0% by default, down from 50%. cardano-node doesn't compress its
  ImmutableDB, so any saving needs a compressing filesystem; the input stays for operators
  who run one. The methodology docs (03) already assume no compression.
- **RAM:** 8 GiB per node, the LSM-backend baseline, priced per GiB. It is not yet
  measured with Leios on an LSM node: the feasibility report's cluster grew by 0.9 to
  1.2 GB of resident memory from 260 kB to 1 MB EBs, so M2's 3 MB EBs may need more than
  8 GiB (see [02-compute-ram.md](./02-compute-ram.md)).
- **CPU:** vCPU is provisioned, not billed by use, so it is a fixed number per node: 2 by
  default (cardano-node 11.1.3's minimum, two cores), the same for Praos and Leios, raised
  only if the peak with headroom needs more. The CPU card sets a block producer's use
  against it (relays don't vote, so they skip closure validation), and the time one core
  takes to validate an EB at the peak against the voting period.
  Validation costs come from the
  [feasibility report](https://github.com/input-output-hk/ouroboros-leios/pull/1156) on
  c5d hosts, the oldest class it measured: 0.147 ms to reapply a Tx (its voting loop) and
  20 ms per closure (the fixed part it uses to rebuild validation times).
  They replace the CIP-164 model's reapply (0.3539 ms per EB + 0.00002151 ms/B), which the
  report finds 10 to 20 times under the voting path, and voters now validate every
  announced EB's closure before voting. On adoption, chain selection validates a block
  body in full (ouroboros-consensus `ApplyVal`), as Praos does today, and reapplies a
  certified EB's closure (`ValidateNone`): Praos pays the full apply twice per Tx, Leios
  a second time only for Txs in RB bodies. Tx apply stays at 0.6201 ms, the mainnet mean with
  scripts included. The report measures no scripts: 0.34 to 0.36 ms with the voting-loop fix
  (ouroboros-consensus 7b91f3619), 0.65 to 3.42 ms without it, so these figures assume the
  fix is in the release. The 0.147 ms reapply is the lowest voting-loop reading in the
  report; its regressions give 0.19 to 0.21 ms. At M2 capacity a block producer's
  validation work needs 0.19 vCPU with 2× headroom (the report measures 0.20 to 0.31 cores
  sustained for a whole node, without headroom), and a worst-case EB (2,650 Txs, every one
  applied) validates on one core in 1.66 s of the 4 s voting period, or 9.1 s at the
  report's 3.42 ms without the fix.
- **Protocol and capacity:** buttons load a parameter set: Praos only (as if Leios had
  never been deployed), or the mainnet graduation steps M0, M1 and M2
  (maxEndorserBlockTxsSize 260 kB, 1 MB, 3 MB; maxEndorserBlockReferencesSize × 40/260;
  L_diff 7 s), for capacities of 8.87, 27.9 and 79.2 TxkB/s (1.97×, 6.18×, 17.6× mainnet's
  4.51 TxkB/s). The fields hold only what can be set: the active slot coefficient and slot
  length, L_hdr / L_vote / L_diff, committee size, maxBlockBodySize, the EB caps and the
  fee parameters (minFeeA 44 lovelace/B, minFeeB 155,381 lovelace). The capacity can be
  typed in TxkB/s or × mainnet, which sizes the EB caps for it: maxEndorserBlockTxsSize to
  what certified EBs must carry beyond the RBs, maxEndorserBlockReferencesSize to one
  37 B reference per Tx of average size (a 32 B hash plus the Tx size, measured on every EB
  of two P&T cluster runs, 2026-11-06 and 2026-11-09). Derived values are read-only.
- **Load:** utilization buttons (10, 25, 50, 75, 100% of capacity, all the time) or
  Spikes: a few high-load hours per epoch at full capacity (5 by default), the rest at a
  load Praos alone can carry (100% of Praos capacity by default). Nodes are provisioned
  for the peak (vCPU, IOPS, peak bandwidth, the EBs held on the fast SSD); egress, chain
  growth and UTxO growth follow the epoch's average.
- **Costs only:** the estimator covers what it costs to run a pool at a given load. A
  pool's income depends on its stake, fixed cost, margin and pledge, and today mostly on
  reserve rewards, so it belongs in a separate rewards calculator. The revenue analysis
  further down this README keeps its April 2026 assumptions (rewards, node count,
  reserve depletion), with November costs, the measured mean fee and $0.20/ADA.
- **Praos-only baseline:** under the total, the costs panel shows what the same pool would
  pay if Leios had never been deployed: Praos alone carrying the same load, capped at
  Praos capacity, on the same LSM node with the same prices and topology. The difference
  is "Added by Leios", and "idle" when the load always fits in RBs.
- **Transaction Fees (system level):** a panel below the costs shows the most
  transaction fees the whole chain can collect per epoch at Praos capacity and at the
  selected capacity, and the transaction fees at the modelled load's average throughput
  (minFeeA × bytes + minFeeB × Txs at the average Tx size), priced at 1.47× that
  minimum for script execution, reference scripts and overpayment: what mainnet paid
  over epochs 589–661 (db-sync, failed transactions excluded). These are what
  transactions pay,
  system level: not staking rewards, and not a pool's income. For reference the panel
  also shows what mainnet collected over a year, epochs 589–661 (2025-10-16 to
  2026-10-16, db-sync): 3,506,912 ADA from 11.6 M transactions (796 ADA of it collateral
  forfeited by failed transactions), 48,040 ADA per epoch on
  average (median 41,273), 0.302 ADA per transaction. Over the same epochs mainnet
  carried about 0.42 TxkB/s, 9.2% of Praos capacity.
  Three rows compare growth over Praos alone at the same demand: fees at this load ÷ the
  fees Praos would collect (capped at its capacity), this pool's total cost ÷ its
  Praos-only baseline, and the first over the second. Above 1, fees grow faster than
  running costs: at M0 and 100% load, 1.97 ÷ 1.40 = 1.40 on Hyperscale prices, 1.82 on
  Discount. Reserve rewards, not fees, are most of a pool's income today.
- **Average Tx size:** 1,132 B, up from 800 B: the mean over mainnet epochs 589–661
  (11.6 M transactions, db-sync to 2026-10-19). The mean is the figure that turns bytes
  per second into transactions per second.
- **Units:** storage and egress are computed in GiB and priced per GB, converted at
  1.074 GB per GiB; the current chain size is given in GB. Disk prices billed per GiB
  (AWS EBS, Azure managed disks, DigitalOcean volumes) are divided by 1.074 before
  averaging (units checked 2026-11-14). The earlier estimator priced GiB as GB throughout,
  about 7% low where a provider bills per GB.
- **Prices:** each estimator preset is the average of the on-demand list prices of its
  group, checked on 2026-11-10 on each provider's pricing page (US regions; Hetzner
  Germany, EUR at the ECB rate of 1.1214). vCPU and RAM prices split a 2 vCPU / 8 GiB
  shape, approximately for AWS (2 × $26.80 + 8 × $2.66 = $74.88 against m7i.large's
  $73.58). Akamai's come from its Dedicated G7 8 GB plan (4 vCPU, $86); its G6 Dedicated
  8 GB costs $72 for the same shape, and a 2 vCPU G8 Dedicated 8 GB plan exists. vCPU and
  RAM prices cancel in "Added by Leios". IOPS and discount egress use the average of what a node pays, 0, because all
  three providers in each group include more than a node uses.
  The discount providers save on egress, not on CPU or disk: on dedicated-CPU plans their
  vCPU costs about the same as the hyperscalers', and with no hard-drive volumes their bulk
  disk is SSD block storage at about twice the price. Discount comes out cheaper only where
  egress outweighs disk: while Leios is active, up to about 28 TxkB/s (M0 at 75 to 100% load,
  M1 from 25%, M2 at 10 and 25%). It costs more at the Praos baseline, and above that
  throughput, where the growing chain fills the disk.

| Price | Hyperscale (AWS / GCP / Azure) | Min | Average (preset) | Max | Discount (DigitalOcean / Akamai / Hetzner) | Min | Average (preset) | Max |
|---|---|---:|---:|---:|---|---:|---:|---:|
| vCPU ($/vCPU-mo) | 26.80 / 15.92 / 25.50 | 15.92 | **22.74** | 26.80 | 20.44 / 30.71 / 17.42 | 17.42 | **22.86** | 30.71 |
| RAM ($/GiB-mo) | 2.66 / 2.13 / 1.90 | 1.90 | **2.23** | 2.66 | 2.77 / 3.07 / 1.74 | 1.74 | **2.53** | 3.07 |
| Fast SSD ($/GB-mo) | 0.0745 / 0.100 / 0.0748 | 0.0745 | **0.0831** | 0.100 | 0 / 0 / 0 (plan's local disk) | 0 | **0** | 0 |
| Bulk disk ($/GB-mo) | 0.0419 / 0.040 / 0.0373 | 0.0373 | **0.0397** | 0.0419 | 0.0931 / 0.10 / 0.0641 | 0.064 | **0.0857** | 0.10 |
| IOPS ($/IOPS-mo) | 3,000 included per volume | 0 | **0** | 0 | not billed | 0 | **0** | 0 |
| Egress ($/GB) | 0.090 / 0.120 / 0.087 | 0.087 | **0.099** | 0.120 | 12–60 TB included per pool | 0 | **0** | 0 |

Disk prices are per GB. AWS (gp3 $0.080, st1 $0.045), Azure ($0.0803, $0.040) and
DigitalOcean ($0.10) list theirs per GiB, divided by 1.074 above; GCP, Akamai and Hetzner
are taken per GB. The previous presets were vCPU 20 (both), storage 0.12 / 0.10, IOPS 0.05 / 0, egress
0.09 / 0, with no RAM. The provider table below uses these per-provider prices: vCPU
and RAM per unit (2 vCPU, 8 GiB RAM), storage growth at the bulk-disk price, and no
IOPS charge.

### Leios at Praos-equivalent load

At confirmed throughput at or below the Praos capacity ceiling (4.5 TxkB/s),
Linear Leios processes the same transaction volume and incurs the same
per-transaction Apply cost. The difference is fixed protocol overhead (vote
validation, certificate validation, and vote and EB diffusion), present whenever
Leios runs, whatever the throughput above Praos capacity. At near-Praos load this overhead dominates; as
throughput grows, it is amortized over more confirmed transactions and the
cost per TxkB/s converges.

The **4.5 (Praos)** column in the tables below shows actual Praos protocol costs
(no EB/vote/cert overhead). The **5 TxkB/s** column is the Leios baseline: just
above Praos-equivalent load, where the fixed overhead is fully visible. Both
columns assume UTxO-HD deployed — UTxO-HD is orthogonal to the Praos vs Leios
comparison and benefits both protocols equally (see
[02-compute-ram.md](./02-compute-ram.md)).

### EB Certification Probability

CIP-164 proposes timing parameters $L_{\text{hdr}}=1$, $L_{\text{vote}}=4$,
$L_{\text{diff}}=7$ slots. An EB announced in an RB at slot $s$ can only be
certified by the next RB, and only if that RB comes at slot $s' \geq s + 3 L_{\text{hdr}} + L_{\text{vote}} + L_{\text{diff}} = s + 14$.
If an RB arrives in the 13 slots between, the EB is discarded. Since each slot
independently produces a block with probability $f = 0.05$ (Bernoulli process):

$$P(\text{EB certified}) = (1 - f)^{13} = 0.95^{13} \approx 0.513$$

as in CIP-164 and the feasibility report. All EBs incur EB body and vote traffic
regardless of certification outcome, scaling those costs by $1/P(\text{cert}) \approx 2\times$
relative to a 100%-certified world. Every fetched EB, certified or not, is also
written to the fast SSD and kept until it is $k$ = 2,160 blocks deep (about 12 hours),
each transaction once; only certified EBs reach the immutable chain on the bulk disk.

The $L_{\text{diff}} = 7$ slot value already includes a safety margin (calculated
minimum: 4 slots). At lower throughput targets, tighter timings may be safe,
raising $P(\text{cert})$ and reducing overhead proportionally.

> [!Important]
> These estimates model expected steady-state behavior. To make nodes resilient
> against adversarial conditions — such as EB flooding, which drives up vote
> verification (CPU), in-flight EB buffering (RAM), and traffic simultaneously —
> higher capacity than the steady-state numbers suggest will be recommended.

## Cost Items

| Cost Item                             | Unit      | Description                                |
|---------------------------------------|-----------|--------------------------------------------|
| [Compute (vCPU)](./01-compute-cpu.md) | $/vCPU/mo | Cost per virtual CPU per month             |
| [Compute (RAM)](./02-compute-ram.md)  | $/GiB/mo  | Cost per gibibyte of RAM per month         |
| [Storage](./03-storage.md)            | $/GB/mo   | Cost per gigabyte of disk per month        |
| [Egress](./04-egress.md)              | $/GB      | Cost per gigabyte of data transferred out  |
| [IOPS](./05-iops.md)                  | $/IOPS/mo | Cost per IOPS per month                    |

Follow the links above to see detailed cost estimates per item.

## Aggregated Total Cost Table

The table below provides an aggregated summary of all cost categories across
different cloud providers based on confirmed throughput in TxkB/s. Both
**4.5 (Praos)** and all Leios columns assume UTxO-HD deployed (8 GiB RAM tier);
see [02-compute-ram.md](./02-compute-ram.md) for why UTxO-HD is orthogonal. Egress
is a lean relay's (fetch multiplicity M = 1) with each provider's free tier subtracted
per node, and storage is one month of chain growth, so the table sits below the
estimator, which defaults to M = 2, applies no free tier and averages the growing disks
over a year.

| Provider         | Cost Item           | 4.5 (Praos) | 5 TxkB/s    | 50 TxkB/s   | 100 TxkB/s  | 200 TxkB/s  | 300 TxkB/s  |
|------------------|---------------------|-------------|-------------|-------------|-------------|-------------|-------------|
| **AWS**          | Compute (vCPU)      | $53.60      | $53.60      | $53.60      | $53.60      | $53.60      | $53.60      |
|                  | Compute (RAM)       | $21.28      | $21.28      | $21.28      | $21.28      | $21.28      | $21.28      |
|                  | Storage             | $0.50       | $0.57       | $5.69       | $11.38      | $22.76      | $34.14      |
|                  | Egress              | $0.00       | $33.03      | $45.30      | $58.95      | $86.23      | $113.52     |
|                  | IOPS                | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       |
|                  | **Total (AWS)**     | **$75.38**  | **$108.48** | **$125.87** | **$145.21** | **$183.87** | **$222.54** |
| **GCP**          | Compute (vCPU)      | $31.84      | $31.84      | $31.84      | $31.84      | $31.84      | $31.84      |
|                  | Compute (RAM)       | $17.04      | $17.04      | $17.04      | $17.04      | $17.04      | $17.04      |
|                  | Storage             | $0.48       | $0.54       | $5.43       | $10.86      | $21.72      | $32.59      |
|                  | Egress              | $5.80       | $56.04      | $72.41      | $90.60      | $126.97     | $163.35     |
|                  | IOPS                | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       |
|                  | **Total (GCP)**     | **$55.16**  | **$105.46** | **$126.72** | **$150.34** | **$197.57** | **$244.82** |
| **Azure**        | Compute (vCPU)      | $51.00      | $51.00      | $51.00      | $51.00      | $51.00      | $51.00      |
|                  | Compute (RAM)       | $15.20      | $15.20      | $15.20      | $15.20      | $15.20      | $15.20      |
|                  | Storage             | $0.45       | $0.50       | $5.06       | $10.12      | $20.23      | $30.35      |
|                  | Egress              | $0.00       | $31.93      | $43.79      | $56.98      | $83.36      | $109.73     |
|                  | IOPS                | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       |
|                  | **Total (Azure)**   | **$66.65**  | **$98.63**  | **$115.05** | **$133.30** | **$169.79** | **$206.28** |
| **DigitalOcean** | Compute (vCPU)      | $40.88      | $40.88      | $40.88      | $40.88      | $40.88      | $40.88      |
|                  | Compute (RAM)       | $22.16      | $22.16      | $22.16      | $22.16      | $22.16      | $22.16      |
|                  | Storage             | $1.12       | $1.26       | $12.64      | $25.29      | $50.58      | $75.87      |
|                  | Egress              | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       |
|                  | IOPS                | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       |
|                  | **Total (DO)**      | **$64.16**  | **$64.30**  | **$75.68**  | **$88.33**  | **$113.62** | **$138.91** |
| **Akamai (Linode)** | Compute (vCPU)   | $61.42      | $61.42      | $61.42      | $61.42      | $61.42      | $61.42      |
|                  | Compute (RAM)       | $24.56      | $24.56      | $24.56      | $24.56      | $24.56      | $24.56      |
|                  | Storage             | $1.20       | $1.35       | $13.57      | $27.15      | $54.31      | $81.47      |
|                  | Egress              | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       |
|                  | IOPS                | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       |
|                  | **Total (Akamai)**  | **$87.18**  | **$87.33**  | **$99.55**  | **$113.13** | **$140.29** | **$167.45** |
| **Hetzner**      | Compute (vCPU)      | $34.84      | $34.84      | $34.84      | $34.84      | $34.84      | $34.84      |
|                  | Compute (RAM)       | $13.92      | $13.92      | $13.92      | $13.92      | $13.92      | $13.92      |
|                  | Storage             | $0.77       | $0.87       | $8.70       | $17.40      | $34.81      | $52.22      |
|                  | Egress              | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       |
|                  | IOPS                | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       |
|                  | **Total (Hetzner)** | **$49.53**  | **$49.63**  | **$57.46**  | **$66.16**  | **$83.57**  | **$100.98** |

> [!Note]
> All costs are monthly estimates in USD ($) based on confirmed throughput in
> TxkB/s (transaction kilobytes per second reaching the ledger).
>
> - UTxO-HD assumed for both protocols (8 GiB RAM tier); see
>   [02-compute-ram.md](./02-compute-ram.md). UTxO-HD is orthogonal to the Praos
>   vs Leios comparison. Above M1 (about 28 TxkB/s) Leios RAM is not measured and
>   may need more than 8 GiB
> - Compute (vCPU) uses the 2-core tier for Leios rows; 4 cores recommended
>   for production headroom (see [01-compute-cpu.md](./01-compute-cpu.md))
> - At higher throughput, egress dominates for premium cloud providers;
>   budget providers (DigitalOcean, Akamai, Hetzner) pay nothing for it, because
>   their included transfer covers it
> - Fixed vote overhead (600 seats × 91 B × 0.05 EB/s × 60 peers) contributes
>   ~401 GiB/month in egress per relay whenever Leios runs, regardless of
>   confirmed throughput: every vote is pushed to every downstream peer, so
>   relays with more peers carry proportionally more
> - Leios at 5 TxkB/s sends about 10× the egress of Praos (see
>   [04-egress.md](./04-egress.md)), almost all of it votes: beyond the free
>   tiers of AWS, GCP and Azure, but within the included transfer of budget
>   providers.

> [!Important] 
> Storage costs shown above represent only one month of blockchain data. As
> blockchain history accumulates over time, storage requirements and associated
> costs will continuously increase.

> [!Note] 
> Storage and data transfer are computed in GiB (2³⁰ bytes) and priced per GB
> (10⁹ bytes), at 1.074 GB per GiB; prices that providers bill per GiB are
> converted first. RAM is sized and priced per GiB.

## Cost/Revenue Analysis

This section analyzes potential revenue from transaction fees based on the
current Cardano mainnet fee calculation formula at different throughput levels.

### Fee Calculation Formula

Cardano calculates transaction fees using the formula:

$$\text{Fee} = \text{minFeeA} \times \text{size} + \text{minFeeB}$$

Where:
- minFeeA = 44 Lovelace per byte (0.000044 ADA per byte): the fee per byte
- minFeeB = 155,381 Lovelace (0.155381 ADA): the fixed fee per transaction
- $\text{size}$ = transaction size in bytes

That is the minimum, set by size alone. At the mainnet average of 1,132 bytes it
comes to 0.205 ADA, but transactions pay more: Plutus transactions are also charged
for script execution. Over mainnet epochs 589–661 (db-sync, failed transactions
excluded) the 11.6 M transactions paid 3,506,117 ADA, a mean of **0.302 ADA per
transaction**, 1.47× the size-based minimum. Plutus transactions (29.5%) paid
0.522 ADA on average, the others 0.210 ADA. The tables below use the measured mean.

### Throughput and Revenue at Different Confirmed Rates

| TxkB/s      | Tx/s (1,132 B avg) | Monthly Txs | Fee/Tx (ADA) | Monthly Revenue (ADA) |
|-------------|--------------------|-------------|--------------|-----------------------|
| 4.5 (Praos) | 4                  | 10,453,866  | 0.302263     | 3,159,817             |
| 5           | 4                  | 11,615,406  | 0.302263     | 3,510,908             |
| 50          | 44                 | 116,154,064 | 0.302263     | 35,109,076            |
| 100         | 88                 | 232,308,127 | 0.302263     | 70,218,151            |
| 200         | 177                | 464,616,254 | 0.302263     | 140,436,303           |
| 300         | 265                | 696,924,382 | 0.302263     | 210,654,454           |

> [!Important]
> The revenue figures above represent **total network revenue**, while cost
> figures in the [Aggregated Total Cost Table](#aggregated-total-cost-table)
> represent costs for **individual nodes**. In a decentralized network with
> approximately 3,000 stake pool operators (SPOs), each typically running
> multiple nodes, the total network infrastructure cost would be significantly
> higher. A proper economic analysis must consider that:
>
> 1. Each SPO only receives a portion of the total fees, proportional to their
>    stake in the network
> 2. The total network infrastructure cost would be ~9,000+ nodes (3,000 SPOs ×
>    3 nodes each, plus additional relay infrastructure)
> 3. Revenue distribution mechanisms and network parameters ultimately determine
>    individual operator profitability

### TPS Breakeven Analysis for Network Infrastructure

To maintain the current network reward structure as the Reserve depletes, we
can calculate the required confirmed throughput to cover the operational costs
of all network participants.

Assumptions:
- Approximately 3,000 stake pool operators (SPOs) in the network
- Each SPO operates 1 block producer and 2 relay nodes (9,000 total nodes)
- Additional infrastructure for dApps and services (~1,000 nodes)
- Total network nodes: 10,000
- Current monthly rewards: ~48 million ADA
- ADA price assumed at $0.20/ADA (November 2026)

> [!Note]
> The tables in this section assume that every ADA of fees is available to pay for
> infrastructure and rewards. CIP-164 states the caveat for its own version of this
> analysis: "only about 20% of fees currently accrue to SPOs, but the table assumes
> 100% would accrue to them"; keeping the current 80%-20% split would take five times
> the fees listed.

#### Infrastructure Cost Estimates

Using the [Aggregated Total Cost Table](#aggregated-total-cost-table), we
estimate total network infrastructure costs based on an average across providers
(both protocols with UTxO-HD).

| TxkB/s      | Cost per Node (Avg) | Network Cost (10,000 nodes) |
|-------------|---------------------|-----------------------------|
| 4.5 (Praos) | ~$66                 | $660,000                    |
| 5 (Leios)   | ~$86                 | $860,000                    |
| 50          | ~$100                | $1,000,000                  |
| 100         | ~$116                | $1,160,000                  |
| 200         | ~$148                | $1,480,000                  |
| 300         | ~$180                | $1,800,000                  |

#### Required Confirmed Throughput for Infrastructure Cost Coverage

| Infrastructure Cost (USD) | Required ADA (at $0.20/ADA) | TPS (Avg Tx) | TxkB/s |
|---------------------------|-----------------------------|--------------|--------|
| $660,000                  | 3,300,000                   | 4.15         | 4.70   |
| $860,000                  | 4,300,000                   | 5.41         | 6.12   |
| $1,000,000                | 5,000,000                   | 6.29         | 7.12   |
| $1,160,000                | 5,800,000                   | 7.30         | 8.26   |
| $1,480,000                | 7,400,000                   | 9.31         | 10.54  |
| $1,800,000                | 9,000,000                   | 11.32        | 12.82  |

At 200 TxkB/s, total network infrastructure costs (~$1.48M/month) represent
about 5% of total fee revenue at that throughput (~140M ADA × $0.20 ≈
$28.1M/month), demonstrating strong economic viability.

#### Required Throughput for Current Reward Maintenance

To maintain current reward levels (~48 million ADA monthly) through transaction
fees as the Reserve depletes:

| Year | Reserve Depletion | Rewards from Fees (ADA) | Required Tx/s | Required TxkB/s |
|------|-------------------|-------------------------|---------------|-----------------|
| 2025 | ~0%               | 0                       | 0             | 0               |
| 2026 | ~13%              | 6,240,000               | 7.9           | 8.9             |
| 2027 | ~24%              | 11,520,000              | 14.5          | 16.4            |
| 2028 | ~34%              | 16,320,000              | 20.5          | 23.2            |
| 2029 | ~43%              | 20,640,000              | 26.0          | 29.4            |
| 2030 | ~50%              | 24,000,000              | 30.2          | 34.2            |

> [!Important]
> By 2029, to compensate for Reserve depletion, the network would need to
> process approximately 26 Tx/s (~29 TxkB/s). This is well within the Leios
> operating range.
