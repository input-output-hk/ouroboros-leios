---
title: Weekly Summary – May 26, 2025
authors:
- will
tags: [progress, update, weekly, overcollateralization, transaction-duplication, conflict-analysis, rust-simulation, transaction-lifecycle, data-processing, optimization]
---

The Leios team completed a significant analysis of overcollateralization schemes and continued advancing the Rust simulation infrastructure. They also focused on understanding transaction duplication and conflict probabilities in shardless scenarios while enhancing simulation tooling to better track transaction lifecycle events.

## Overcollateralization analysis

- Completed comprehensive analysis of shardless overcollateralization, where transactions are randomly sampled from the memory pool
- Found that probabilities of duplication and conflicts are minimized when the concurrency period is as short as possible
- Determined that conflict probability is always greater than duplication probability
- Identified that longer transaction residence times correspond to lower probabilities of duplication or conflict, where transaction residency time is defined as the average time a transaction stays in the memory pool before reaching an IB (calculated as memory pool size divided by transaction throughput)
- Discovered that spatial efficiency is greater for longer residence times
- Found that the tradeoff between probabilities of duplication and conflict is insensitive to protocol parameters
- Showed that the expected number of conflicts in IBs scales proportionately with the fraction of conflicting transactions and transaction throughput
- Identified that, at a given throughput, reducing the probability of duplicates or conflicts can be at odds with minimizing the total number of conflicts
- Found that probabilistic computation of conflicts is about 20% lower than naive estimates
- Determined that at 100 TPS with favorable protocol parameters, an overcollateralization factor of nearly 400x is necessary in adversarial scenarios where the memory pool is filled with conflicting transactions
- Concluded that having successful transactions pay for all conflicting ones is too risky due to potential attacks on honest transactions using common UTXO inputs
- Identified that consuming collateral from conflicted transactions in IBs is more viable, though it breaks existing UX guarantees
- Noted ongoing discussions about the realism of creating 400 mutually conflicting transactions, given that individual mempools would not include conflicting transactions, and attack scenarios would require coordination across multiple nodes
- Documented detailed findings in the [overcollateralization analysis notebook](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/overcollateralization-v1.ipynb).

## Simulation development

### Transaction lifecycle analysis

- Analyzed protocol performance across transaction throughput scenarios up to 300 TPS
- Found that the protocol performs well with essentially every transaction reaching the ledger up to 300 TPS, where breakdown occurs
- Noted that the 100-node network is more stressful than a realistic mainnet would be
- Achieved space efficiency above 80% for moderate-throughput scenarios
- Measured average transaction latency of about 100 seconds (95th percentile at 200 seconds) to reach the ledger.

### Rust simulation improvements

- Added 'TXLost' events to the simulation output to detect transaction loss scenarios
- Enhanced the ability to track where Leios can lose transactions with various parameter choices.

## Data processing optimization

- Developed a new [`leios-trace-processor`](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/trace-processor/) tool to replace script-based analyses
- Achieved significantly faster processing of simulation results compared to previous scripts
- Enabled analysis of much longer and larger simulation datasets
- Created standardized CSV output format for transaction lifecycle data, including creation, IB inclusion, EB inclusion, and RB inclusion timestamps.
