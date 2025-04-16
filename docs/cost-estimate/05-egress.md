# Egress cost estimation per node

Network egress is metered for most cloud providers even though many have some monthly budget that's free.
In the following example calculation, we try to be as precise as possible given today's [p2p default configuration](https://book.world.dev.cardano.org/environments/mainnet/config.json) of the node.

## Ouroboros Praos

We start with Ouroboros Praos to have a baseline. The following numbers are from Cardano Mainnet, April 2025.

| Component  | Size (bytes) | Size (KiB) |
|------------|--------------|------------|
| Header (H) | 1,024        | 1 |
| Body   (B) | 90,112       | 88 |

### Blocks per Month Calculation

| Parameter | Value | Formula |
|-----------|-------|---------|
| Epoch length | 5 days (432,000 slots) | Given |
| Active slot coefficient | 0.05 | Given |
| Blocks per epoch | 21,600 | $432,000 \times 0.05$ |
| Epochs per month | ~6.0833 | $\frac{365}{5 \times 12}$ |
| **Blocks per month** | **131,400** | $21,600 \times 6.0833$ |

> [!Note]
> On Cardano Mainnet one slot equals the duration of one second.

### Network Topology Assumptions

For our calculations, we consider a network with two types of nodes:
- Relay nodes: Connect to multiple edge nodes and other relays
- Edge nodes: Connect to relay nodes but not to other edge nodes

We make the following assumptions about the network:
- [Default p2p configuration](https://book.world.dev.cardano.org/environments/mainnet/config.json): 20 peers per node
- Network ratio: ~3 edge nodes per relay node
- Block propagation model:
  - Headers: Propagated to 100% of peers
  - Bodies: Requested by ~10% of peers (2 out of 20)

### Base Egress Formulas

For any node type, we can calculate egress using these formulas:

1. **Header Egress**:
   $$E_{headers} = N_{blocks} \times H \times P_{total}$$
   where:
   - $N_{blocks}$ = Number of blocks per month
   - $H$ = Header size in bytes
   - $P_{total}$ = Total number of peers

2. **Body Egress**:
   $$E_{bodies} = N_{blocks} \times B \times P_{requesting}$$
   where:
   - $B$ = Body size in bytes
   - $P_{requesting}$ = Number of peers requesting bodies

### Edge Node Egress Calculation

Edge nodes have minimal egress compared to relay nodes. Their egress consists of:
1. Transaction data sent to relay nodes
2. Block body responses when requested

Using our base formulas with a typical edge node configuration:
- Total peers ($P_{total}$) = 1 (single relay connection)
- Requesting peers ($P_{requesting}$) = 1 (when relay requests body)

The monthly egress for a typical edge node:
$$E_{edge} = N_{blocks} \times B \approx 131,400 \times 90,112 \text{ bytes} \approx 11.03 \text{ GiB/month}$$

This forms our baseline for minimal node egress in a Praos network.

### Relay Node Egress Calculation

Using our assumptions:
- Total peers ($P_{total}$) = 20
- Edge nodes per relay = 3
- Relay peers = 20
- Requesting relay peers = 2

1. **Header egress to edge nodes**:
   $$E_{headers}^{edge} = 131,400 \times 1,024 \times 3 = 403,983,360 \text{ bytes} \approx 0.39 \text{ GiB}$$

2. **Body egress to edge nodes**:
   $$E_{bodies}^{edge} = 131,400 \times 90,112 \times 3 = 35,522,167,680 \text{ bytes} \approx 33.09 \text{ GiB}$$

3. **Header egress to relay nodes**:
   $$E_{headers}^{relay} = 131,400 \times 1,024 \times 20 = 2,693,222,400 \text{ bytes} \approx 2.51 \text{ GiB}$$

4. **Body egress to relay nodes**:
   $$E_{bodies}^{relay} = 131,400 \times 90,112 \times 2 = 23,681,445,120 \text{ bytes} \approx 22.06 \text{ GiB}$$

5. **Total relay node egress**:
   $$E_{total} = E_{headers}^{edge} + E_{bodies}^{edge} + E_{headers}^{relay} + E_{bodies}^{relay}$$
   $$E_{total} = 0.39 + 33.09 + 2.51 + 22.06 \approx 58.05 \text{ GiB/month}$$

This shows how relay nodes handle significantly more egress than edge nodes due to their role in the network topology.

## Ouroboros Leios

### Block Size Breakdown

#### Input Blocks (IB)
- Header: 304 bytes
  - ProducerId: 32 bytes
  - SlotNo: 64 bytes
  - VRF proof: 80 bytes
  - Body hash: 32 bytes
  - RB Ref: 32 bytes
  - Signature: 64 bytes
- Body: 98,304 bytes (96 KiB)

#### Endorsement Blocks (EB)
- Header: 240 bytes
  - ProducerId: 32 bytes
  - SlotNo: 64 bytes
  - VRF proof: 80 bytes
  - Signature: 64 bytes
- Body: 32 bytes per IB reference

#### Votes
- Size: 150 bytes per vote
- Votes per pipeline: 600
- Votes per EB: 600 votes × 1.5 EBs = 900 votes per stage

#### Ranking Blocks (RB)
- Header: 1,024 bytes (1 KiB)
- Body: 90,112 bytes (88 KiB)

### Monthly Traffic Calculation

#### Base Parameters
- Seconds per month: 2,592,000 (30 days)
- Stage length: 20 slots
- EBs per stage: 1.5
- RBs per stage: 1 (every 20 slots)

#### Example Calculation (1 IB/s, 20 peers, 100% header propagation, 25% body requests)
```
IB Headers: 2,592,000 seconds × 304 bytes × 20 peers = 14.69 GiB
IB Bodies: 2,592,000 seconds × 98,304 bytes × 5 peers = 1.18 TiB
EB Headers: 1 IB/s × 240 bytes × 1.5 EBs × 20 peers × 129,600 stages = 869.38 MiB
EB Bodies: 1 IB/s × 32 bytes × 1.5 EBs × 5 peers × 129,600 stages = 579.59 MiB
Votes: 194,400 seconds × 150 bytes × 900 votes × 20 peers = 524.88 GiB
RB Headers: 129,600 seconds × 1,024 bytes × 20 peers = 2.47 GiB
RB Bodies: 129,600 seconds × 90,112 bytes × 5 peers = 54.43 GiB
Total: 1.75 TiB

Note: 
- IB traffic dominates due to larger body size (98,304 bytes = 96 KiB)
- EB traffic is minimal due to small body size (32 bytes per reference)
- Vote traffic is significant due to high volume (900 votes per stage)
- RB traffic is moderate, similar to Praos block size
```

### Monthly Traffic per Node

| IB/s | IB Headers | IB Bodies | EB Headers | EB Bodies | Votes | RB Headers | RB Bodies | Total | vs Praos (A) |
|------|------------|-----------|------------|-----------|-------|------------|-----------|-------|--------------|
| 1    | 14.69 GiB  | 1.18 TiB  | 869.38 MiB | 579.59 MiB | 524.88 GiB | 2.47 GiB   | 54.43 GiB  | 1.75 TiB | +2,670% |
| 5    | 73.45 GiB  | 5.90 TiB  | 869.38 MiB | 2.90 GiB   | 2.62 TiB   | 2.47 GiB   | 54.43 GiB  | 8.52 TiB | +13,260% |
| 10   | 146.90 GiB | 11.80 TiB | 869.38 MiB | 5.80 GiB   | 5.25 TiB   | 2.47 GiB   | 54.43 GiB  | 17.03 TiB | +26,590% |
| 20   | 293.80 GiB | 23.60 TiB | 869.38 MiB | 11.60 GiB  | 10.50 TiB  | 2.47 GiB   | 54.43 GiB  | 34.06 TiB | +53,130% |
| 30   | 440.70 GiB | 35.40 TiB | 869.38 MiB | 17.40 GiB  | 15.75 TiB  | 2.47 GiB   | 54.43 GiB  | 51.09 TiB | +79,670% |

### Monthly Cost by Cloud Provider ($)

| Provider         | Price/GB | Free Allowance (GB) | 1 IB/s | 5 IB/s | 10 IB/s | 20 IB/s | 30 IB/s | vs Praos (A) |
|------------------|----------|---------------------|---------|---------|----------|----------|----------|--------------|
| Google Cloud     | $0.120   | 0                   | $230.40 | $1,088.40| $2,167.20| $4,325.40| $6,483.60| +8,340% |
| Railway          | $0.100   | 0                   | $192.00 | $907.00 | $1,806.00| $3,604.00| $5,403.00| +7,000% |
| AWS              | $0.090   | 100                 | $172.80 | $816.30 | $1,625.40| $3,243.60| $4,862.70| +6,300% |
| Microsoft Azure  | $0.087   | 100                 | $167.04 | $788.73 | $1,570.89| $3,135.09| $4,699.29| +6,084% |
| Alibaba Cloud    | $0.074   | 10                  | $142.08 | $670.74 | $1,335.78| $2,665.38| $3,995.08| +5,170% |
| DigitalOcean     | $0.010   | 100–10,000          | $19.20  | $90.70  | $180.60  | $360.40  | $540.30  | +699% |
| Oracle Cloud     | $0.0085  | 10,240              | $16.32  | $77.09  | $153.51  | $306.34  | $459.26  | +594% |
| Linode           | $0.005   | 1,024–20,480        | $9.60   | $45.35  | $90.30   | $180.20  | $270.15  | +350% |
| Hetzner          | $0.00108 | 1,024               | $2.07   | $9.80   | $19.50   | $38.92   | $58.35   | +75% |
| UpCloud          | $0.000   | 1,024–24,576        | $0.00   | $0.00   | $0.00    | $0.00    | $0.00    | 0% |

Note: Percentage increases are calculated against Praos scenario A (20 peers) baseline of 63.64 GiB/month and $7.73/month (using average cost across providers)

### Data Egress Cost Sources

| Provider | Price/GB | Source | Last Updated |
|----------|----------|---------|--------------|
| Google Cloud | $0.120 | https://cloud.google.com/vpc/pricing | Feb 2025 |
| Railway | $0.100 | https://railway.app/pricing | - |
| AWS | $0.090 | https://aws.amazon.com/ec2/pricing/ | 2023 |
| Microsoft Azure | $0.087 | https://azure.microsoft.com/pricing/details/bandwidth/ | Dec 2024 |
| Alibaba Cloud | $0.074 | https://www.alibabacloud.com/pricing | 2024 |
| DigitalOcean | $0.010 | https://www.digitalocean.com/pricing/ | - |
| Oracle Cloud | $0.0085 | https://www.oracle.com/cloud/pricing/ | Dec 2024 |
| Linode | $0.005 | https://www.linode.com/pricing/ | Apr 2023 |
| Hetzner | $0.00108 | https://www.hetzner.com/cloud/pricing | 2024 |
| UpCloud | $0.000 | https://upcloud.com/pricing/ | - |

Note: Prices may vary by region and volume. Some providers offer free tiers or volume discounts not reflected in these base rates. The table shows the standard outbound data transfer rates for the most commonly used regions.
