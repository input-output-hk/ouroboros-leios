# Ouroboros Leios vs. Top Blockchains

Cardano’s upcoming *Ouroboros Leios* protocol promises to supercharge its scalability, targeting 100–1,000 transactions per second (TPS) while keeping its decentralized roots. But how does it fare against heavyweights like Solana, Ethereum, and Bitcoin, especially for use cases like microtransactions, DeFi, or voting? We’ve crafted a scorecard comparing these blockchains across seven key metrics - Throughput, Fee Predictability, Fee Loss Protection, Latency, Decentralization, Security, and Scalability. With a nod to Solana’s user experience (UX) struggles around fee loss, let’s see why Leios could shine.

## Leios vs. Solana, Ethereum, Bitcoin

We scored each blockchain on a 0–10 scale, with higher scores indicating better performance. Here’s how they stack up:

| **Metric**              | **Leios (Cardano)** | **Solana** | **Ethereum** | **Bitcoin** |
|-------------------------|---------------------|------------|--------------|-------------|
| **Throughput**          | 8                  | 4          | 3            | 2           |
| **Fee Predictability**  | 8                  | 5          | 2            | 6           |
| **Fee Loss Protection** | 9                  | 3          | 4            | 7           |
| **Latency**             | 5                  | 8          | 6            | 1           |
| **Decentralization**    | 9                  | 4          | 7            | 8           |
| **Security**            | 8                  | 7          | 8            | 9           |
| **Scalability**         | 8                  | 6          | 5            | 3           |
| **Total Score**         | **55/70**          | **37/70**  | **35/70**    | **36/70**   |

## Scoring Criteria and Rationale

### Leios (Cardano)
- **Throughput (8)** - Leios targets 100–1,000 TPS via parallel Input Blocks and pipelining, a massive leap from Praos’ 5–10 TPS. Simulations show 1,000 TPS is feasible, but it’s still in development, so not a perfect 10.
- **Fee Predictability (8)** - Leios softens Cardano’s strict determinism with solutions like collateralization, where winning transactions may pay slightly higher fees (~1–2 ADA vs. 0.2 ADA). Fees stay mostly predictable, unlike volatile markets.
- **Fee Loss Protection (9)** - A proposed pre-validation certificate system rejects conflicting transactions before Input Block inclusion, ensuring no fees for unprocessed transactions. Minor conflict risks at 1,000 TPS prevent a 10.
- **Latency (5)** - Finality takes ~3–5 minutes (1–3 with Peras), slower than competitors due to pipelined stages. Suitable for voting or supply chains but less ideal for DeFi’s instant needs.
- **Decentralization (9)** - Retains Cardano’s ~3,000 stake pools, ensuring broad access via stake-weighted VRF. Slight centralization risks at high TPS keep it from 10.
- **Security (8)** - Inherits Praos’ proven security against 50% stake attacks. Concurrent processing adds complexity, but rigorous analysis and endorsement thresholds maintain robustness. Not yet deployed, so not 10.
- **Scalability (8)** - Scales to 1,000 TPS on L1 without sharding, preserving global state. Storage (~28 GB/year) and bandwidth costs need optimization, limiting to 8.

### Solana
- **Throughput (4)** - Delivers ~2,000–3,000 TPS (theoretical 65,000 TPS), but congestion drops effective TPS, hurting DeFi and microtransaction UX. Real-world issues lower the score.
- **Fee Predictability (5)** - Localized fee markets keep fees low (~$0.00025), but spikes during congestion (e.g., NFT drops) create uncertainty, frustrating users.
- **Fee Loss Protection (3)** - Dropped transactions during congestion (common in 2023–2024) cost fees without results, a major UX pain point. Jito and upgrades help but don’t eliminate losses.
- **Latency (8)** - ~0.4-second block time offers fast finality, great for DeFi and voting, though dropped transactions can delay effective confirmation.
- **Decentralization (4)** - ~2,000 validators, but high hardware needs concentrate control, risking censorship for identity or voting use cases.
- **Security (7)** - Resilient to most attacks, but validator concentration and past outages (e.g., 2022) expose weaknesses. Less rigorous than Cardano’s peer-reviewed model.
- **Scalability (6)** - High theoretical TPS, but congestion and centralization limit practical scaling. L2 or sharding isn’t native, unlike Leios’ L1 approach.

### Ethereum
- **Throughput (3)** - ~15–30 TPS (post-merge, pre-sharding). L2s (e.g., Arbitrum) boost TPS but add complexity, unsuitable for microtransactions or voting.
- **Fee Predictability (2)** - Gas fees ($1–$100 during congestion) are volatile, disrupting DeFi and supply chain UX. L2s reduce costs but vary widely.
- **Fee Loss Protection (4)** - Failed transactions (e.g., outbid gas) cost fees, frustrating users. L2s improve but don’t eliminate losses, impacting small transactions.
- **Latency (6)** - ~12-second block time, ~1–2 minute finality. L2s can be faster but vary, less ideal for real-time voting or DeFi.
- **Decentralization (7)** - ~500,000 validators post-merge, but L2 reliance and staking costs centralize some control. Less open than Cardano’s stake pools.
- **Security (8)** - Proven secure post-merge, with a large validator base. L2s introduce risks, but the core chain is robust.
- **Scalability (5)** - L2s and future sharding (post-2025) improve scalability, but complexity and fragmentation limit L1 potential compared to Leios.

### Bitcoin
- **Throughput (2)** - ~7 TPS, too low for microtransactions, DeFi, or identity. Lightning Network adds capacity but is complex for mass adoption.
- **Fee Predictability (6)** - Fees (~$1–$5) vary with mempool size but are less volatile than Ethereum. Predictable for transfers but not complex use cases.
- **Fee Loss Protection (7)** - Failed transactions rarely cost fees unless mempool is full. Lightning introduces risks, but the core chain protects users.
- **Latency (1)** - ~10-minute block time, ~1-hour finality, unusable for real-time DeFi, voting, or supply chains.
- **Decentralization (8)** - ~10,000 nodes, highly decentralized, but mining pools concentrate some control, less open than Cardano.
- **Security (9)** - Most battle-tested, resisting attacks via PoW. Energy inefficiency doesn’t impact security score.
- **Scalability (3)** - Limited by block size and PoW. Lightning helps but can’t scale to Leios’ TPS or support dApps.

## Solana’s UX Context - A Fee Loss Pain Point

Solana’s UX struggles with fee loss from dropped transactions, especially during congestion (e.g., NFT drops), where users pay ~$0.00025 without results, feeling like “playing roulette.” X posts highlight frustration, with users abandoning platforms after losses. Localized fee markets and smart wallets (e.g., Meso’s gasless UX) mitigate some issues, but dropped transactions persist, hurting trust for microtransactions and DeFi. Leios counters this with pre-validation certificates, rejecting conflicts before Input Block inclusion, ensuring no fees for unprocessed transactions. Its elastic capacity avoids Solana’s congestion, enhancing reliability for voting and supply chains, though its ~3–5 minute finality is slower but more predictable.

## Why Leios Takes the Lead

Leios tops the scorecard with 55/70, excelling in throughput (100–1,000 TPS), fee loss protection (no fees for rejections), and decentralization (~3,000 stake pools). This makes it ideal for microtransactions, DeFi, voting, identity, and supply chains, where reliability and trust matter. Solana (37/70) offers speed but falters on fee loss and centralization, Ethereum (35/70) on fees and complexity, and Bitcoin (36/70) on TPS and latency. Leios’ UX, with clear feedback and no-fee rejections, could outshine Solana’s dropped transaction woes, positioning Cardano as a user-friendly, scalable blockchain.

## What’s Next?

Leios is still in R&D, with testnets and community votes ahead to finalize its design. Want to weigh in? Share your thoughts on [Cardano’s forums](https://forum.cardano.org/). Curious how Leios could power your favorite use case? Let’s keep the conversation going!
