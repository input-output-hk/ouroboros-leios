# Topology Analysis Report

Analysis of: topology-v4-mainnet.yaml (and topology-v4-mini.yaml)

v4 is the **per-pool** fused mainnet topology: every active stake pool from
the May 2026 Koios snapshot is represented as exactly one node, with no
separate relay endpoints.  Each node is its own block producer; the
"relay" abstraction is folded into the pool-node itself.  Edges are
hybrid: ~44% are literal copies of available blockperf
peer-graph edges measurements, with the remainder sampled from available measured
ASN-pair peering propensity.  Latencies are sampled from RIPE Atlas.

## Network Statistics

### topology-v4-mainnet.yaml

| Metric | Value |
|--------|-------|
| Total nodes | 2685 |
| Block producers | 2685 |
| Relay nodes | 0 |
| Total connections | 95713 |
| Network diameter | 4 hops |
| Average connections per node | 35.65 |
| Clustering coefficient | 0.038 |
| Average latency | 95.1ms ms |
| Maximum latency | 700.0ms ms |
| Stake-weighted latency | 0.0ms ms |
| Bidirectional connections | 6722 |
| Asymmetry ratio | 85.95% |

### topology-v4-mini.yaml

| Metric | Value |
|--------|-------|
| Total nodes | 250 |
| Block producers | 250 |
| Relay nodes | 0 |
| Total connections | 8572 |
| Network diameter | 3 hops |
| Average connections per node | 34.29 |
| Clustering coefficient | 0.319 |
| Average latency | 91.6ms ms |
| Maximum latency | 700.0ms ms |
| Stake-weighted latency | 0.0ms ms |
| Bidirectional connections | 674 |
| Asymmetry ratio | 84.27% |

## Stake Distribution

### topology-v4-mainnet.yaml

| Metric | Value |
|--------|-------|
| Total stake | 21150214046 |
| Gini coefficient | 0.841 |

#### Top 5 Stake Holders

| Node | Stake | % of Total | Ticker | Provider | Country |
|------|--------|------------|--------|----------|---------|
| node-0 | 114016430 | 0.54% | TW001 | OVH | FR |
| node-1 | 90570452 | 0.43% | LBF4 | Unresolved | — |
| node-2 | 89419068 | 0.42% | — | Unresolved | — |
| node-3 | 81187761 | 0.38% | KILN9 | OVH | FR |
| node-4 | 77631783 | 0.37% | KILN4 | OVH | FR |

#### Geographic Stake Distribution (top 10 countries)

| Region | Nodes | Total Stake | % of Network |
|--------|------:|------------:|-------------:|
| DE     |   534 | 4,916,723,197 |       23.25% |
| US     |   842 | 4,632,216,996 |       21.90% |
| FR     |   151 | 1,955,160,083 |        9.24% |
| ?      |   431 | 1,603,221,007 |        7.58% |
| NL     |    62 |   995,052,756 |        4.70% |
| SE     |    25 |   992,834,513 |        4.69% |
| JP     |    85 |   984,722,236 |        4.66% |
| IE     |    32 |   715,180,817 |        3.38% |
| KR     |    36 |   696,387,368 |        3.29% |
| CA     |    77 |   578,377,637 |        2.73% |

### topology-v4-mini.yaml

| Metric | Value |
|--------|-------|
| Total stake | 14325095468 |
| Gini coefficient | 0.150 |

#### Top 5 Stake Holders

| Node | Stake | % of Total | Ticker | Provider | Country |
|------|--------|------------|--------|----------|---------|
| node-0 | 114016430 | 0.80% | TW001 | OVH | FR |
| node-1 | 90570452 | 0.63% | LBF4 | Unresolved | — |
| node-2 | 89419068 | 0.62% | — | Unresolved | — |
| node-3 | 81187761 | 0.57% | KILN9 | OVH | FR |
| node-4 | 77631783 | 0.54% | KILN4 | OVH | FR |

> The mini variant retains the top-250 pools by stake.  Total covered
> stake is 14.33 B ADA, i.e. 67.7% of the full network's 21.15 B ADA.
> Gini is low (0.150) because the top-250 cohort clusters near pool
> saturation (≈ 77 M ADA) — they're all big pools.

#### Geographic Stake Distribution (top 10 countries)

| Region | Nodes | Total Stake | % of Network |
|--------|------:|------------:|-------------:|
| DE     |    64 | 3,429,254,425 |       23.94% |
| US     |    45 | 2,336,600,663 |       16.31% |
| FR     |    24 | 1,453,593,389 |       10.15% |
| ?      |    21 | 1,350,478,260 |        9.43% |
| SE     |    13 |   926,203,844 |        6.47% |
| NL     |    15 |   828,986,884 |        5.79% |
| JP     |    13 |   785,342,651 |        5.48% |
| IE     |    10 |   620,942,805 |        4.33% |
| CH     |     7 |   534,691,003 |        3.73% |
| GB     |     7 |   444,544,347 |        3.10% |

## Geographic Validation

✅ No geographic violations found

## How v4 differs from v1 / v2 / v3

| Dimension | v1 (pseudo-mainnet) | v2 (mini-mainnet) | v3 (micro-mainnet) | **v4 (fused, per-pool)** |
|---|---|---|---|---|
| Nodes | 10,000 | 750 | 100 | **2,685 / 250** |
| BPs | 2,657 | 216 | 22 | **2,685 (= every node)** |
| Relays | 7,343 | 534 | 78 | **0** |
| Stake (ADA) | 22.85 B (synthetic) | 12.70 B (synthetic) | 1.62 B (synthetic) | **21.15 B (real Koios epoch 630)** |
| Edges (mainnet variant) | 298,756 | — | — | **95,713** |
| Edge source | RIPE Atlas via CF | RIPE Atlas via CF | RIPE Atlas via CF | **blockperf (~44% literal) + propensity** |
| Latency source | RIPE Atlas | RIPE Atlas | RIPE Atlas | **RIPE Atlas asn_rtt_stat** |
| Identity per node | synthetic | synthetic | synthetic | **real `pool_id_bech32`** |
| Cardano security model | BP + relays separated | BP + relays separated | BP + relays separated | **collapsed (each pool = one node)** |
| Geographic placement | from synthetic ASN/country | same | same | **real region of primary endpoint** |

For most macro studies (throughput, voting convergence, spatial efficiency,
stake-weighted failure scenarios) v4 is the right choice — its node count
(≈ 2,685) matches the real **active pool count** in the Koios snapshot
exactly, every node carries its real `pool_id_bech32`, and the
stake distribution is taken verbatim from epoch 630.
