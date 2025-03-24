# Egress cost estimation per node

## Ouroboros Praos

### Back of envelope calculation

#### Blocks/ month
- epoch length 5 days (432,000 slots)
- active slot coefficient 0.05
- yielding 21,600 blocks per epoch
- ~6.0833 epochs per month (365/5/12)
- **131,400 blocks per month**

#### Total block data
- block size 90,112 bytes (88KB)
- assume 50% filled → 45,056 bytes (44kB)
- **131,400 blocks x 45,056 bytes = 5,920,362,240 bytes ~5.92GB**

#### Egress traffic for p2p block propagation
- Peers (P): assume:
```
    (A) 20 peers from TargetNumberOfActivePeers default configuration
    (B) ~35 downstream peers per node
```

- assuming efficient gossip?, it sends to (P-1)/2 peers:
```
    (A) 9.5
    (B) 17 
```

#### Node traffic
```    
    (A) 131,400 blocks x 45,056 bytes x 9.5 = 5,920,362,240 bytes = ~56.24GB
    (B) 131,400 blocks x 45,056 bytes x 17 = 5,920,362,240 bytes  = ~100.65GB
```
 
- additional traffic from transactions (5-10GB?) and consensus (~1-2GB?)

#### Final total egress per month/ node
```
    (A) Low end:  56.24 + 5 + 1   = 62.24 GB
    (B) High end: 100.65 + 10 + 2 = 112.65 GB
```

## Ouroboros Leios

### Back of envelope calculation

#### Blocks/ month
- 30 days = 2,592,000 seconds
- Input Blocks (IBs): 5.0 * 2,592,000 = 12,960,000 IBs/month
- Endorsement Blocks (EBs): 1.5 * 2,592,000 = 3,888,000 EBs/month
- Ranking Blocks (RBs): 0.05 * 2,592,000 = 129,600 RBs/month

#### Total block data
- IBs: 12,960,000 * (304 + 98,304) = ~1.28 TB
  - Head (304 bytes) from `ib-head-size-bytes: 304`:
    - ProducerId: 32 bytes
    - SlotNo: 64 bytes
    - VRF proof: 80 bytes
    - Body hash: 32 bytes
    - RB Ref: 32 bytes
    - Signature: 64 bytes
  - Body (98,304 bytes) from `ib-body-avg-size-bytes: 98304`
- EBs: 3,888,000 * (240 + 32) = ~1.06 GB
  - Constant (240 bytes) from `eb-size-bytes-constant: 240`:
    - ProducerId: 32 bytes
    - SlotNo: 64 bytes
    - VRF proof: 80 bytes
    - Signature: 64 bytes
  - Per IB (32 bytes) from `eb-size-bytes-per-ib: 32` (IB hash)
- RBs: 129,600 * (1,024 + 90,112) = ~11.82 GB
  - Head (1,024 bytes) from `rb-head-size-bytes: 1024`
  - Body (90,112 bytes) from `rb-body-max-size-bytes: 90112`

#### Egress traffic for p2p propagation
Using same peer assumptions as Praos:
```
(A) 20 peers → 9.5 peers for gossip
(B) 35 peers → 17 peers for gossip
```

#### Node traffic
```
(A) Low end:
    - IBs: 1.28 TB * 9.5 = 12.16 TB
    - EBs: 1.06 GB * 9.5 = 10.07 GB
    - RBs: 11.82 GB * 9.5 = 112.29 GB
    Total: ~12.28 TB

(B) High end:
    - IBs: 1.28 TB * 17 = 21.76 TB
    - EBs: 1.06 GB * 17 = 18.02 GB
    - RBs: 11.82 GB * 17 = 200.94 GB
    Total: ~21.98 TB
```

## Estimated Egress Costs by Cloud Provider (March 2025)

| Cloud Provider         | Egress Cost ($/GB) | Free Allowance (GB/mo) | Praos A (62.24 GB) Cost ($) | Praos B (112.65 GB) Cost ($) | Leios A (12.28 TB) Cost ($) | Leios B (21.98 TB) Cost ($) |
|-----------------------|--------------------|------------------------|----------------------------|-----------------------------|----------------------------|-----------------------------|
| AWS                   | 0.09              | 100                    | 0                          | 1.14                        | 1,123.20                    | 1,978.20                    |
| Microsoft Azure       | 0.087             | 100                    | 0                          | 1.10                        | 1,085.76                    | 1,911.24                    |
| Google Cloud          | 0.114             | 0                      | 7.10                       | 12.84                       | 1,399.92                    | 2,505.72                    |
| Alibaba Cloud         | 0.074             | 10                     | 3.87                       | 7.60                        | 908.72                      | 1,626.52                    |
| Railway               | 0.1               | 0                      | 6.22                       | 11.27                       | 1,228.00                    | 2,198.00                    |
| DigitalOcean          | 0.01              | 100–10,000             | 0                          | 0.13                        | 122.80                      | 219.80                      |
| Oracle Cloud          | 0.0085            | 10,240                 | 0                          | 0                           | 104.38                      | 186.83                      |
| Linode                | 0.005             | 1,024–20,480           | 0                          | 0                           | 61.40                       | 109.90                      |
| Hetzner               | 0.00108           | 1,024                  | 0                          | 0                           | 13.26                       | 23.74                       |
| UpCloud               | 0                 | 1,024–24,576           | 0                          | 0                           | 0                           | 0                           |

## Additional IB Production Rate Scenarios

### 10 IBs/second
| Cloud Provider         | Egress Cost ($/GB) | Free Allowance (GB/mo) | Low (20 peers) Cost ($) | High (35 peers) Cost ($) |
|-----------------------|--------------------|------------------------|------------------------|-------------------------|
| AWS                   | 0.09              | 100                    | 2,246.40               | 3,956.40                |
| Microsoft Azure       | 0.087             | 100                    | 2,171.52               | 3,822.48                |
| Google Cloud          | 0.114             | 0                      | 2,799.84               | 5,011.44                |
| Alibaba Cloud         | 0.074             | 10                     | 1,817.44               | 3,253.04                |
| Railway               | 0.1               | 0                      | 2,456.00               | 4,396.00                |
| DigitalOcean          | 0.01              | 100–10,000             | 245.60                 | 439.60                  |
| Oracle Cloud          | 0.0085            | 10,240                 | 208.76                 | 373.66                  |
| Linode                | 0.005             | 1,024–20,480           | 122.80                 | 219.80                  |
| Hetzner               | 0.00108           | 1,024                  | 26.52                  | 47.48                   |
| UpCloud               | 0                 | 1,024–24,576           | 0                      | 0                       |