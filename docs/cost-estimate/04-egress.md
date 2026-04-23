# Egress cost estimation per node

Network egress is metered for most cloud providers even though many have some
monthly budget that is free. In the following example calculation, we try to be
as precise as possible given today's
[p2p default configuration](https://book.world.dev.cardano.org/environments/mainnet/config.json)
of the node.

All values use confirmed throughput in TxkB/s (transaction kilobytes per
second reaching the ledger). Seconds per month: 2,628,000 (30.4167 days).

## Ouroboros Praos

We start with Ouroboros Praos to have a baseline. The following numbers are from
Cardano Mainnet, April 2025.

| Component  | Size (bytes) | Size (KiB) |
| ---------- | ------------ | ---------- |
| Header (H) | 1,024        | 1          |
| Body (B)   | 90,112       | 88         |

### Blocks per Month

| Parameter               | Value       | Formula                                 |
| ----------------------- | ----------- | --------------------------------------- |
| Active slot coefficient | 0.05        | Protocol parameter                      |
| Seconds per month       | 2,628,000   | $30.4167 \times 24 \times 60 \times 60$ |
| **Blocks per month**    | **131,400** | $0.05 \times 2{,}628{,}000$             |

### Network Topology Assumptions

For our calculations, we consider two types of nodes:

- Relay nodes: Connect to other relays
- Edge nodes: Connect to relay nodes but not to other edge nodes

We make the following assumptions about the network:

- [Default p2p configuration](https://book.world.dev.cardano.org/environments/mainnet/config.json):
  20 (upstream) peers per relay node
- ~3 edge nodes per relay node
- Block propagation model:
  - Headers: Propagated to all peers (20 relay + 3 edge = 23 peers)
  - Bodies: Requested by ~10% of relay peers (2 out of 20) + all 3 edge peers

### Praos Relay Node Egress Calculation

1. **Header egress** (23 peers):
   $131{,}400 \times 1{,}024 \times 23 = 3{,}094 \text{ MB} \approx 2.95 \text{ GiB}$

2. **Body egress to edge nodes** (3 peers):
   $131{,}400 \times 90{,}112 \times 3 \approx 33.08 \text{ GiB}$

3. **Body egress to relay nodes** (2 peers):
   $131{,}400 \times 90{,}112 \times 2 \approx 22.05 \text{ GiB}$

4. **Total relay egress**: $\approx 58.08 \text{ GiB/month}$

## Ouroboros Leios

In Linear Leios (CIP-164), transactions are gossiped via the mempool. EBs carry
only 32-byte tx hash references; actual transaction data is propagated
independently as transactions arrive. Only confirmed (certified) transaction data
counts toward throughput, but transactions are gossiped once on arrival — the
node does not know in advance which EBs will be certified.

### Block Size Components

| Component                     | Size (bytes) | Size (KiB) |
| ----------------------------- | ------------ | ---------- |
| Endorsement Block (EB) Header | 240          | 0.2        |
| EB Body (32 B per tx ref)     | varies       | varies     |
| Vote bundle (per voter)       | 105          | 0.1        |
| Ranking Block (RB) Header     | 1,024        | 1          |
| RB Body (certificate)         | 7,168        | 7          |

### Protocol Rates

| Parameter             | Value                  | Source                                          |
| --------------------- | ---------------------- | ----------------------------------------------- |
| EB/RB rate            | 0.05/s                 | Active slot coefficient                         |
| EBs per month         | 131,400                | $0.05 \times 2{,}628{,}000$                     |
| Votes per EB          | 600                    | `vote-generation-probability`; wFA+LS committee |
| Vote size             | 164 bytes              | `vote-bundle-size-bytes-per-eb`; non-persistent |
| P(EB certified)       | ≈ 0.48                 | Poisson timing model                            |
| Certified EBs/month   | 63,072                 | $0.05 \times 0.48 \times 2{,}628{,}000$         |

### Network Topology Assumptions

Same assumptions as Praos:

- 20 relay peers + 3 edge nodes per relay
- Transaction data propagation (mempool gossip):
  - Bodies requested by 2 relay peers + 3 edge peers = **5 peers**
  - (Same model as Praos block body propagation)
- EB/RB headers: propagated to all 23 peers
- EB/RB bodies: requested by 2 relay peers
- Votes: propagated to 1 requesting peer (lightweight gossip)

### Egress Formulas

1. **Transaction Data Egress** (dominant — scales with TxkB/s):

   Transactions are gossiped once per node when they arrive. Each tx body is
   served to ~5 requesting peers (2 relay + 3 edge):

   $$E_{\text{tx}} = \text{TxkB/s} \times 1{,}000 \times 5 \times T_{\text{month}}$$

2. **Vote Egress** (fixed — independent of throughput):

   $$E_{\text{votes}} = N_{\text{votes/EB}} \times V_{\text{size}} \times R_{\text{eb}} \times 1 \times T_{\text{month}}$$

   where 1 peer requests each vote bundle.

   $$E_{\text{votes}} = 600 \times 164 \times 0.05 \times 2{,}628{,}000 = 12.94 \times 10^9 \text{ bytes} \approx 12.05 \text{ GiB}$$

3. **EB Body Egress** (tx hash references — scales with TxkB/s):

   Each EB body contains 32-byte tx references. EB body size = $\frac{\text{TxkB/s} \times 1{,}000}{1{,}500 \times 0.05} \times 32$ bytes.

   $$E_{\text{eb-body}} = R_{\text{eb}} \times T_{\text{month}} \times \frac{\text{TxkB/s} \times 1{,}000}{1{,}500 \times 0.05} \times 32 \times 2$$

   Simplifying: $E_{\text{eb-body}} \approx \text{TxkB/s} \times 0.1121 \text{ GiB/month}$

4. **EB Header Egress** (fixed):

   $$E_{\text{eb-hdr}} = 131{,}400 \times 240 \times 23 = 725{,}976{,}000 \text{ bytes} \approx 0.676 \text{ GiB}$$

5. **RB Header Egress** (fixed):

   $$E_{\text{rb-hdr}} = 131{,}400 \times 1{,}024 \times 23 = 3{,}093 \text{ MB} \approx 2.95 \text{ GiB}$$

6. **RB Body Egress** (certificate, fixed):

   $$E_{\text{rb-body}} = 131{,}400 \times 7{,}168 \times 2 = 1{,}884 \text{ MB} \approx 1.75 \text{ GiB}$$

### Fixed Overhead Summary

| Component       | Monthly Egress | Notes                                   |
| --------------- | -------------- | --------------------------------------- |
| Vote traffic    | 12.05 GiB      | 600 voters × 164 B × 0.05 EB/s         |
| RB headers      | 2.95 GiB       | To all 23 peers                         |
| RB bodies       | 1.96 GiB       | To 2 relay peers (8,000 B cert each)    |
| EB headers      | 0.68 GiB       | To all 23 peers                         |
| **Fixed total** | **17.64 GiB**  | Independent of throughput               |

### Monthly Egress at Different Confirmed Throughputs

| TxkB/s | Tx Data     | EB Bodies | Fixed Overhead | **Total**     | vs Praos |
| ------ | ----------- | --------- | -------------- | ------------- | -------- |
| 4.5    | 55.07 GiB   | 0.50 GiB  | 17.64 GiB      | **73.21 GiB** | +26%     |
| 50     | 612.2 GiB   | 5.61 GiB  | 17.64 GiB      | **635.5 GiB** | +994%    |
| 100    | 1,224.4 GiB | 11.21 GiB | 17.64 GiB      | **1,253 GiB** | +2,057%  |
| 150    | 1,836.5 GiB | 16.82 GiB | 17.64 GiB      | **1,871 GiB** | +3,121%  |
| 200    | 2,448.7 GiB | 22.42 GiB | 17.64 GiB      | **2,489 GiB** | +4,185%  |
| 250    | 3,060.9 GiB | 28.03 GiB | 17.64 GiB      | **3,107 GiB** | +5,249%  |
| 300    | 3,673.1 GiB | 33.63 GiB | 17.64 GiB      | **3,724 GiB** | +6,314%  |

> [!Note]
>
> - Transaction data egress dominates at all but the lowest throughput levels
> - Vote overhead (38.54 GiB/month) is fixed — it represents the cost of
>   running 3,000 voters at 0.05 EB/s regardless of how many txs are confirmed
> - This is a worst-case analysis: vote count = all 3,000 active pools; in
>   practice, a committee-based scheme would reduce this significantly
> - "vs Praos" compares against Praos relay egress of 58.08 GiB/month

### Traffic Components at 200 TxkB/s

| Component        | Egress    | % of Total |
| ---------------- | --------- | ---------- |
| Tx Data          | 2,449 GiB | 98.4%      |
| EB Bodies        | 22.4 GiB  | 0.9%       |
| Vote Traffic     | 12.1 GiB  | 0.5%       |
| RB Headers       | 2.95 GiB  | 0.1%       |
| RB Bodies        | 1.96 GiB  | 0.1%       |
| EB Headers       | 0.68 GiB  | < 0.1%     |

At target throughput (200 TxkB/s), transaction data dominates egress (98.4%).
Vote traffic (fixed at 600 voters × 164 B × 0.05 EB/s) is a small floor cost.

### Monthly Cost by Cloud Provider ($)

Egress is billed per GB (10⁹ bytes); 1 GiB ≈ 1.074 GB.

| Provider      | Price/GB | Free (GB)  | 4.5 TxkB/s | 50 TxkB/s | 100 TxkB/s | 150 TxkB/s | 200 TxkB/s | 250 TxkB/s | 300 TxkB/s |
| ------------- | -------- | ---------- | ---------- | --------- | ---------- | ---------- | ---------- | ---------- | ---------- |
| AWS           | $0.090   | 100        | $0.00      | $52.43    | $112.14    | $171.85    | $231.58    | $291.28    | $351.00    |
| GCP           | $0.120   | 0          | $9.43      | $81.90    | $161.52    | $241.13    | $320.78    | $400.38    | $480.00    |
| Azure         | $0.087   | 100        | $0.00      | $50.68    | $108.40    | $166.12    | $223.82    | $281.48    | $339.17    |
| Railway       | $0.100   | 0          | $7.86      | $68.25    | $134.57    | $200.94    | $267.31    | $333.69    | $399.93    |
| Alibaba Cloud | $0.074   | 10         | $5.08      | $49.77    | $98.84     | $147.96    | $197.07    | $246.21    | $295.31    |
| DigitalOcean  | $0.010   | 1,000      | $0.00      | $0.00     | $3.46      | $10.09     | $16.73     | $23.36     | $30.00     |
| Oracle Cloud  | $0.0085  | 10,240     | $0.00      | $0.00     | $0.00      | $0.00      | $0.00      | $0.00      | $0.00      |
| Linode        | $0.005   | 1,024      | $0.00      | $0.00     | $1.61      | $4.93      | $8.25      | $11.56     | $14.88     |
| Hetzner       | $0.00108 | 1,024      | $0.00      | $0.00     | $0.35      | $1.06      | $1.78      | $2.50      | $3.21      |
| UpCloud       | $0.000   | 1,024–24,576 | $0.00    | $0.00     | $0.00      | $0.00      | $0.00      | $0.00      | $0.00      |

> [!Note]
>
> - Prices are for US regions and may vary by location
> - Free allowances vary by plan tier; values shown are typical baseline
>   included transfer for standard instances
> - At high throughput (100+ TxkB/s), egress becomes a major cost item on
>   premium cloud providers (AWS, GCP, Azure); budget providers (Hetzner,
>   Linode) are significantly cheaper due to generous included transfer

### Data Egress Cost Sources

| Provider     | Price/GB | Source                                                 | Last Updated |
| ------------ | -------- | ------------------------------------------------------ | ------------ |
| AWS          | $0.090   | https://aws.amazon.com/ec2/pricing/                    | Apr 2025     |
| GCP          | $0.120   | https://cloud.google.com/vpc/pricing                   | Apr 2025     |
| Azure        | $0.087   | https://azure.microsoft.com/pricing/details/bandwidth/ | Apr 2025     |
| DigitalOcean | $0.010   | https://www.digitalocean.com/pricing/                  | Apr 2025     |
| Linode       | $0.005   | https://www.linode.com/pricing/                        | Apr 2025     |
| Hetzner      | $0.00108 | https://www.hetzner.com/cloud/pricing                  | Apr 2025     |

Note: Prices may vary by region and volume. Some providers offer free tiers or
volume discounts not reflected in these base rates.
