# Egress cost estimation per node

Network egress is metered for most cloud providers even though many have some
monthly budget that's free. In the following example calculation, we try to be
as precise as possible given today's
[p2p default configuration](https://book.world.dev.cardano.org/environments/mainnet/config.json)
of the node.

## Ouroboros Praos

We start with Ouroboros Praos to have a baseline. The following numbers are from
Cardano Mainnet, April 2025.

| Component  | Size (bytes) | Size (KiB) |
| ---------- | ------------ | ---------- |
| Header (H) | 1,024        | 1          |
| Body (B)   | 90,112       | 88         |

### Blocks per Month Calculation

| Parameter               | Value                  | Formula                     |
| ----------------------- | ---------------------- | --------------------------- |
| Epoch length            | 5 days (432,000 slots) | Protocol parameter          |
| Active slot coefficient | 0.05                   | Protocol parameter          |
| Blocks per epoch        | 21,600                 | $$432,000 \times 0.05$$     |
| Epochs per month        | ~6.0833                | $$\frac{365}{5 \times 12}$$ |
| **Blocks per month**    | **131,400**            | $$21,600 \times 6.0833$$    |

> [!NOTE]
> On Cardano Mainnet one slot equals the duration of one second.

### Network Topology Assumptions

For our calculations, we consider two types of nodes:

- Relay nodes: Connect to other relays
- Edge nodes: Connect to relay nodes but not to other edge nodes

We make the following assumptions about the network:

- [Default p2p configuration](https://book.world.dev.cardano.org/environments/mainnet/config.json):
  20 (upstream) peers per relay node
- ~3 edge nodes per relay node
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

Edge nodes have minimal egress compared to relay nodes. Their egress consists
of:

1. Transaction data sent to relay nodes
2. Block body responses when requested

Using our base formulas with a typical edge node configuration:

- Total peers ($P_{total}$) = 1 (single relay connection)
- Requesting peers ($P_{requesting}$) = 1 (when relay requests body)

The monthly egress for a typical edge node:

$$
E_{edge} = N_{blocks} \times B \approx 131,400 \times 90,112 \text{ bytes} \approx 11.03 \text{ GiB/month}
$$

This forms our baseline for minimal node egress in a Praos network.

### Relay Node Egress Calculation

Using our assumptions:

- Total peers ($P_{total}$) = 20
- Edge nodes per relay = 3
- Relay peers = 20
- Requesting peers = 2

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

## Ouroboros Leios

We analyze Ouroboros Leios with the same network topology assumptions as Praos,
but with its unique block types and propagation model.

### Block Size Components

| Component                     | Size (bytes) | Size (KiB) |
| ----------------------------- | ------------ | ---------- |
| Input Block (IB) Header       | 304          | 0.3        |
| Input Block (IB) Body         | 98,304       | 96         |
| Endorsement Block (EB) Header | 240          | 0.2        |
| Endorsement Block (EB) Body   | 32           | 0.03       |
| Vote                          | 150          | 0.15       |
| Ranking Block (RB) Header     | 1,024        | 1          |
| Ranking Block (RB) Body       | 7,168        | 7          |

> [!NOTE]
> The EB body size consists only of the IB reference (32 bytes per reference).
> The RB body in Leios contains exactly one certificate of size 7 * 1024 = 7,168 bytes,
> not the full 88 KiB as in Praos.

### Blocks per Month Calculation

For a fair comparison with Praos, we use the same block rate (0.05 blocks/s) for
Leios' IBs. This ensures that both protocols are compared under similar
conditions, with Leios producing the same number of IBs per month as Praos
produces blocks per month (131,400).

| Parameter         | Value       | Formula                                 |
| ----------------- | ----------- | --------------------------------------- |
| Stage length      | 20 slots    | Protocol parameter                      |
| EBs per stage     | 1.5         | Protocol parameter                      |
| Days per month    | 30.4167     | $\frac{365}{12}$                        |
| Seconds per month | 2,628,000   | $30.4167 \times 24 \times 60 \times 60$ |
| Stages per month  | 131,400     | $\frac{2,628,000}{20}$                  |
| **IBs per month** | **131,400** | $0.05 \text{ IB/s} \times 2,628,000$    |
| **EBs per month** | **197,100** | $1.5 \times 131,400$                    |
| **RBs per month** | **131,400** | $1 \times 131,400$                      |

### Network Topology Assumptions

We maintain the same network assumptions as Praos:

- Default p2p configuration: 20 peers per node
- Network ratio: ~3 edge nodes per relay node
- Block propagation model:
  - Headers: Propagated to 100% of peers
  - Bodies: Requested by ~10% of peers (2 out of 20)
  - Votes: Propagated only to downstream peers that request them (typically 1 peer requests each vote)

### Base Egress Formulas

For any node type, we calculate egress using these formulas:

1. **IB Header Egress**:

   $$E_{ib\_headers} = N_{ibs} \times H_{ib} \times P_{total}$$
   where:
   - $N_{ibs}$ = Number of IBs per month
   - $H_{ib}$ = IB header size in bytes
   - $P_{total}$ = Total number of peers

2. **IB Body Egress**:

   $$E_{ib\_bodies} = N_{ibs} \times B_{ib} \times P_{requesting}$$
   where:
   - $B_{ib}$ = IB body size in bytes
   - $P_{requesting}$ = Number of peers requesting bodies

3. **EB Header Egress**:

   $$E_{eb\_headers} = N_{ebs} \times H_{eb} \times P_{total}$$
   where:
   - $N_{ebs}$ = Number of EBs per month
   - $H_{eb}$ = EB header size in bytes

4. **EB Body Egress**:

   $$E_{eb\_bodies} = N_{ebs} \times N_{ib\_refs} \times R_{ib} \times P_{requesting}$$
   where:
   - $N_{ebs}$ = Number of EBs per month (197,100)
   - $N_{ib\_refs}$ = Number of IB references per EB (1, due to stage length and
     IB rate)
   - $R_{ib}$ = Size of IB reference in bytes (32)
   - $P_{requesting}$ = Number of peers requesting bodies (2)

5. **Vote Egress**:

   $$E_{votes} = N_{ebs} \times V \times N_{voters} \times P_{requesting\_votes}$$
   where:
   - $N_{ebs}$ = Number of EBs per month (197,100)
   - $V$ = Vote size in bytes
   - $N_{voters}$ = Number of voters (600)
   - $P_{requesting\_votes}$ = Number of peers requesting votes (typically 1)

6. **RB Header Egress**:

   $$E_{rb\_headers} = N_{rbs} \times H_{rb} \times P_{total}$$
   where:
   - $N_{rbs}$ = Number of RBs per month
   - $H_{rb}$ = RB header size in bytes

7. **RB Body Egress**:

   $$E_{rb\_bodies} = N_{rbs} \times C_{rb} \times P_{requesting}$$
   where:
   - $N_{rbs}$ = Number of RBs per month
   - $C_{rb}$ = Certificate size (7,168 bytes)
   - $P_{requesting}$ = Number of peers requesting bodies

### Edge Node Egress Calculation

The edge node egress calculation for Leios is identical to that of Praos, as
edge nodes only handle block body responses and transaction data. See the
[Edge Node Egress Calculation](#edge-node-egress-calculation) section in the
Praos part for details.

### Relay Node Egress Calculation

Using our assumptions:

- Total peers ($P_{total}$) = 20
- Edge nodes per relay = 3
- Relay peers = 20
- Requesting peers = 2

#### Relay-to-Edge Traffic

1. **IB header egress to edge nodes**:

   $$E_{ib\_headers}^{edge} = 131,400 \times 304 \times 3 = 119,825,280 \text{ bytes} \approx 0.112 \text{ GiB}$$

2. **IB body egress to edge nodes**:

   $$E_{ib\_bodies}^{edge} = 131,400 \times 98,304 \times 3 = 38,747,566,080 \text{ bytes} \approx 36.09 \text{ GiB}$$

3. **EB header egress to edge nodes**:

   $$E_{eb\_headers}^{edge} = 197,100 \times 240 \times 3 = 141,912,000 \text{ bytes} \approx 0.132 \text{ GiB}$$

4. **EB body egress to edge nodes**:

   $$E_{eb\_bodies}^{edge} = 197,100 \times 32 \times 3 = 18,921,600 \text{ bytes} \approx 0.018 \text{ GiB}$$

5. **RB header egress to edge nodes**:

   $$E_{rb\_headers}^{edge} = 131,400 \times 1,024 \times 3 = 403,939,200 \text{ bytes} \approx 0.376 \text{ GiB}$$

6. **RB body egress to edge nodes**:

   $$E_{rb\_bodies}^{edge} = 131,400 \times 7,168 \times 3 = 2,827,571,200 \text{ bytes} \approx 2.633 \text{ GiB}$$

Total relay-to-edge traffic:

$$\approx 0.112 + 36.09 + 0.132 + 0.018 + 0.376 + 2.633 \approx 39.36 \text{ GiB/month}$$

#### Relay-to-Relay Traffic

1. **IB header egress to relay nodes**:

   $$E_{ib\_headers}^{relay} = 131,400 \times 304 \times 20 = 798,835,200 \text{ bytes} \approx 0.744 \text{ GiB}$$

2. **IB body egress to relay nodes**:

   $$E_{ib\_bodies}^{relay} = 131,400 \times 98,304 \times 2 = 25,831,711,200 \text{ bytes} \approx 24.06 \text{ GiB}$$

3. **EB header egress to relay nodes**:

   $$E_{eb\_headers}^{relay} = 197,100 \times 240 \times 20 = 946,080,000 \text{ bytes} \approx 0.881 \text{ GiB}$$

4. **EB body egress to relay nodes**:

   $$E_{eb\_bodies}^{relay} = 197,100 \times 32 \times 2 = 12,614,400 \text{ bytes} \approx 0.012 \text{ GiB}$$

5. **Vote egress to relay nodes**:

   $$E_{votes}^{relay} = 197,100 \times 150 \times 600 \times 1 = 17,739,000,000 \text{ bytes} \approx 16.52 \text{ GiB}$$

6. **RB header egress to relay nodes**:

   $$E_{rb\_headers}^{relay} = 131,400 \times 1,024 \times 20 = 2,689,536,000 \text{ bytes} \approx 2.505 \text{ GiB}$$

7. **RB body egress to relay nodes**:

   $$E_{rb\_bodies}^{relay} = 131,400 \times 7,168 \times 2 = 1,883,596,800 \text{ bytes} \approx 1.754 \text{ GiB}$$

Total relay-to-relay traffic:

$$\approx 0.744 + 24.06 + 0.881 + 0.012 + 16.52 + 2.505 + 1.754 \approx 46.48 \text{ GiB/month}$$

#### Total Relay Node Egress

$$E_{total} = 39.36 + 46.48 \approx 85.84 \text{ GiB/month}$$

### Traffic Components by Size (Descending)

| Component                       | Size (GiB) | Percentage of Total |
| ------------------------------- | ---------- | ------------------- |
| IB body egress to edge nodes    | 36.09      | 42.0%               |
| IB body egress to relay nodes   | 24.06      | 28.0%               |
| Vote egress to relay nodes      | 16.52      | 19.2%               |
| RB body egress to edge nodes    | 2.63       | 3.1%                |
| RB header egress to relay nodes | 2.51       | 2.9%                |
| RB body egress to relay nodes   | 1.75       | 2.0%                |
| EB header egress to relay nodes | 0.88       | 1.0%                |
| IB header egress to relay nodes | 0.74       | 0.9%                |
| RB header egress to edge nodes  | 0.38       | 0.4%                |
| EB header egress to edge nodes  | 0.13       | 0.2%                |
| IB header egress to edge nodes  | 0.11       | 0.1%                |
| EB body egress to edge nodes    | 0.02       | 0.02%               |
| EB body egress to relay nodes   | 0.01       | 0.01%               |


This breakdown shows IB body propagation dominates the network traffic, accounting for 70.0% of the total egress (42.0% to edge nodes and 28.0% to relay nodes). Vote propagation is the third largest component at 19.2% of the total traffic. All other components contribute less than 4% each to the total traffic.

> [!Important] 
> The above traffic breakdown is based on the baseline Leios
> configuration of 0.05 IB/s, which is equivalent to Praos's block rate for fair
> comparison. However, it's crucial to note that different components scale
> differently with higher IB/s rates:
>
> | IB/s Rate | Vote Traffic | IB Body to Edge Nodes | IB Body to Relay Nodes | Total Traffic |
> |-----------|--------------|------------------------|------------------------|---------------|
> | 0.05      | 16.52 GiB (19.2%) | 36.09 GiB (42.0%) | 24.06 GiB (28.0%) | 85.84 GiB |
> | 1         | 16.52 GiB (1.4%) | 0.72 TiB (61.2%) | 0.48 TiB (40.8%) | 1.18 TiB |
> | 10        | 16.52 GiB (0.1%) | 7.22 TiB (60.6%) | 4.81 TiB (40.4%) | 11.91 TiB |
> | 20        | 16.52 GiB (0.1%) | 14.44 TiB (60.0%) | 9.62 TiB (40.0%) | 24.01 TiB |
> | 30        | 16.52 GiB (0.0%) | 21.65 TiB (60.0%) | 14.44 TiB (40.0%) | 36.04 TiB |
>
> As shown above, at 30 IB/s (600 times the baseline rate), IB body traffic dominates at over 99% of the total traffic,
> while vote traffic—initially a significant component at 0.05 IB/s—becomes less than 0.1% of the total.

### Monthly Traffic per Node

| IB/s | IB Headers | IB Bodies | EB Headers | EB Bodies | Votes     | RB Headers | RB Bodies | Total      | vs Praos |
| ---- | ---------- | --------- | ---------- | --------- | --------- | ---------- | --------- | ---------- | -------- |
| 0.05 | 0.86 GiB   | 60.15 GiB | 1.01 GiB   | 0.03 GiB  | 16.52 GiB | 2.88 GiB   | 4.39 GiB  | 85.84 GiB  | +48%     |
| 1    | 17.12 GiB  | 1.17 TiB  | 1.01 GiB   | 0.03 GiB  | 16.52 GiB | 2.88 GiB   | 4.39 GiB  | 1.18 TiB   | +2,089%  |
| 5    | 85.60 GiB  | 5.86 TiB  | 1.01 GiB   | 0.03 GiB  | 16.52 GiB | 2.88 GiB   | 4.39 GiB  | 5.95 TiB   | +11,350% |
| 10   | 171.20 GiB | 11.73 TiB | 1.01 GiB   | 0.03 GiB  | 16.52 GiB | 2.88 GiB   | 4.39 GiB  | 11.91 TiB  | +22,743% |
| 20   | 342.40 GiB | 23.45 TiB | 1.01 GiB   | 0.03 GiB  | 16.52 GiB | 2.88 GiB   | 4.39 GiB  | 23.80 TiB  | +45,529% |
| 30   | 513.60 GiB | 35.18 TiB | 1.01 GiB   | 0.03 GiB  | 16.52 GiB | 2.88 GiB   | 4.39 GiB  | 35.69 TiB  | +68,314% |

> [!NOTE]
> These calculations assume fully utilized block space for Input Blocks (IBs). In practice, if blocks are not fully utilized, the actual egress for IB bodies would be proportionally lower based on the actual block utilization rate.

### Monthly Cost by Cloud Provider ($)

| Provider        | Price/GB | Free Allowance (GB) | 0.05 IB/s | 1 IB/s  | 5 IB/s  | 10 IB/s   | 20 IB/s   | 30 IB/s   | vs Praos |
| --------------- | -------- | ------------------- | --------- | ------- | ------- | --------- | --------- | --------- | -------- |
| Google Cloud    | $0.120   | 0                   | $10.30    | $141.60 | $714.00 | $1,429.20 | $2,856.00 | $4,282.80 | +48%     |
| Railway         | $0.100   | 0                   | $8.58     | $118.00 | $595.00 | $1,191.00 | $2,380.00 | $3,569.00 | +48%     |
| AWS             | $0.090   | 100                 | $0.00     | $108.00 | $535.50 | $1,071.90 | $2,142.00 | $3,212.10 | +48%     |
| Microsoft Azure | $0.087   | 100                 | $0.00     | $104.40 | $518.50 | $1,036.17 | $2,070.60 | $3,105.03 | +48%     |
| Alibaba Cloud   | $0.074   | 10                  | $5.61     | $87.32  | $440.30 | $881.34   | $1,761.20 | $2,641.06 | +48%     |
| DigitalOcean    | $0.010   | 100–10,000          | $0.00     | $11.80  | $59.50  | $119.10   | $238.00   | $356.90   | +48%     |
| Oracle Cloud    | $0.0085  | 10,240              | $0.00     | $0.00   | $50.58  | $101.24   | $202.30   | $303.37   | +48%     |
| Linode          | $0.005   | 1,024–20,480        | $0.00     | $5.90   | $29.75  | $59.55    | $119.00   | $178.45   | +48%     |
| Hetzner         | $0.00108 | 1,024               | $0.00     | $0.00   | $6.43   | $12.87    | $25.70    | $38.54    | +48%     |
| UpCloud         | $0.000   | 1,024–24,576        | $0.00     | $0.00   | $0.00   | $0.00     | $0.00     | $0.00     | 0%       |

Note: Percentage increases are calculated against Praos scenario A (20 peers)
baseline of 63.64 GiB/month and $7.73/month (using average cost across
providers)

### Data Egress Cost Sources

| Provider        | Price/GB | Source                                                 | Last Updated |
| --------------- | -------- | ------------------------------------------------------ | ------------ |
| Google Cloud    | $0.120   | https://cloud.google.com/vpc/pricing                   | Feb 2025     |
| Railway         | $0.100   | https://railway.app/pricing                            | -            |
| AWS             | $0.090   | https://aws.amazon.com/ec2/pricing/                    | 2023         |
| Microsoft Azure | $0.087   | https://azure.microsoft.com/pricing/details/bandwidth/ | Dec 2024     |
| Alibaba Cloud   | $0.074   | https://www.alibabacloud.com/pricing                   | 2024         |
| DigitalOcean    | $0.010   | https://www.digitalocean.com/pricing/                  | -            |
| Oracle Cloud    | $0.0085  | https://www.oracle.com/cloud/pricing/                  | Dec 2024     |
| Linode          | $0.005   | https://www.linode.com/pricing/                        | Apr 2023     |
| Hetzner         | $0.00108 | https://www.hetzner.com/cloud/pricing                  | 2024         |
| UpCloud         | $0.000   | https://upcloud.com/pricing/                           | -            |

Note: Prices may vary by region and volume. Some providers offer free tiers or
volume discounts not reflected in these base rates. The table shows the standard
outbound data transfer rates for the most commonly used regions.

no reserves fully filled blocks how many tx fees needed for covering SPO cost
