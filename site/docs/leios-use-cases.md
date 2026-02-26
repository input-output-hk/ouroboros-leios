# Use cases powered by Ouroboros Leios

Leios aims to increase throughput from approximately 5-10 transactions per second (TPS) to around 100 TPS, with a longer-term target of 1,000 TPS or more, subject to validation and parameter selection. This projected increase in capacity, combined with Cardano’s emphasis on security, predictable fees, and a distributed network of approximately 3,000 stake pools, would expand the range of feasible use cases. The following sections outline five areas where higher throughput could have a meaningful impact.

## Global microtransaction ecosystems

A higher-throughput network enables low-value, cross-border payments to settle quickly and at predictable cost. Examples include small tips to content creators, machine-to-machine payments such as smart device access, or in-game purchases across regions. Increased capacity makes these use cases more practical at scale.

- **Why Leios is suitable** – with a projected range of 100–1,000 TPS, Leios would support millions of low-value transactions per day. At 100 TPS, this equates to approximately 8.6 million transactions daily. Greater throughput can reduce per-transaction costs and improve fee stability. In addition, partial transaction determinism — where fees are predictable, with limited variance in rare contention scenarios — reduces the risk of unexpected costs during periods of high demand.
- **Comparison with other networks** – Bitcoin processes approximately 7 TPS, and transaction fees can range from one to five US dollars during congestion, limiting suitability for microtransactions. Ethereum typically processes 15–30 TPS, with fees that fluctuate significantly depending on network demand. Solana advertises substantially higher throughput, but its validator set is more concentrated, which may raise concerns about operational centralization for certain use cases.
- **Real-world vision** – a decentralized streaming platform could enable users to transfer 0.05 ada per view to creators, with transactions processed promptly and without reliance on centralized intermediaries.

## Decentralized supply chain tracking

Global supply chains require timely, verifiable updates to track goods such as food, medical products, or industrial components. A higher-throughput consensus layer would allow more frequent on-chain recording of events, improving transparency and auditability across jurisdictions.

- **Why Leios is suitable** – supply chains generate continuous data streams, including Internet of Things (IOT) sensor readings and shipping scans. A throughput range of around 100 TPS would support a significantly higher volume of updates than the current baseline of approximately 10 TPS, reducing the risk of backlog during peak periods. Increased capacity, combined with a distributed network of roughly 3,000 stake pools, strengthens resilience and supports tamper-evident, audit-ready records without reliance on a central authority.
- **Comparison with other networks** – Ethereum can experience high fees and congestion during periods of demand, making frequent state updates costly. Bitcoin has comparatively low throughput, limiting its suitability for near-real-time tracking. Solana offers high throughput, but concerns about validator concentration may affect its suitability in highly regulated or audit-sensitive contexts.
- **Real-world vision** – a pharmaceutical manufacturer records each handoff of a vaccine batch on-chain. Regulators and partners can independently verify the product's full lifecycle against a decentralized, tamper-resistant ledger.

## Scalable DeFi with time-sensitive transactions

Decentralized finance (DeFi) requires timely transaction processing, particularly for liquidations, arbitrage, and collateral adjustments. Higher and more predictable throughput would improve reliability during periods of elevated market activity.

- **Why Leios is suitable** – increased capacity reduces the likelihood of congestion during demand spikes, supporting time-sensitive operations such as loan liquidations. A projected throughput range of 100–1,000 TPS would allow significantly more concurrent activity than the current baseline. Partial transaction determinism supports predictable fees, with limited variance in contention scenarios, reducing the risk of failed or unexpectedly expensive transactions. Cardano’s distributed stake pool model also supports open and non-discriminatory transaction inclusion.
- **Comparison with other networks** – Ethereum has experienced congestion and fee spikes during periods of intense DeFi activity, increasing transaction costs and failure rates. Solana provides high throughput but has a comparatively concentrated validator set. Bitcoin does not natively support general-purpose smart contracts required for most DeFi protocols.
- **Real-world vision** – a decentralized exchange such as SundaeSwap processes a surge in trading activity during market volatility. Orders and liquidations are confirmed within expected time bounds, and fees remain predictable, enabling users to manage risk effectively.

## Decentralized identity for large populations

Digital identity systems require secure issuance, verification, and revocation of credentials at scale. A higher-throughput consensus layer would better support population-level identity activity, including frequent updates and attestations.

- **Why Leios is suitable** – A projected capacity of around 100 TPS or more would allow millions of identity-related transactions per day, such as credential issuance and verification, exceeding the current baseline of approximately 10 TPS under Praos. Increased throughput can reduce per-transaction costs, making large-scale deployments more economically viable. Cardano’s decentralized stake pool model also limits reliance on a single controlling entity, which is important for systems handling sensitive identity data. Solutions such as Atala PRISM could benefit from improved scalability at the base layer.
- **Comparison with other networks** – Ethereum may face cost and throughput constraints during periods of high demand. Bitcoin does not natively support the flexible smart contract functionality typically required for decentralized identity frameworks. Solana offers higher throughput but has a more concentrated validator set, which may raise governance and trust considerations in sovereign identity deployments.
- **Real-world vision** – a public authority issues digital credentials to 10 million citizens. Daily verifications for healthcare access or voting eligibility are recorded on-chain, with predictable fees and independently verifiable integrity.

## Real-time voting systems

Secure and transparent voting systems require timely transaction processing, verifiable inclusion, and resistance to censorship. Higher throughput at the consensus layer would better support large-scale participation, whether in public elections or on-chain governance processes.

- **Why Leios is suitable** – a projected capacity of around 100 TPS would allow millions of votes to be recorded per day, significantly increasing the scale supported by the current baseline. Greater throughput reduces the risk of backlogs during periods of high participation. In addition, stake-based mechanisms and endorsement structures are designed to provide verifiable and tamper-evident outcomes, while maintaining censorship resistance under realistic network conditions.
- **Comparison with other networks** – Ethereum may experience congestion during peak demand, affecting transaction finality times and costs. Bitcoin has limited throughput and does not support the flexible smart contract logic required for complex voting systems. Solana provides higher throughput but operates with a comparatively concentrated validator set, which may raise governance considerations in voting contexts.
- **Real-world vision** – delegated representatives (DReps) participate in on-chain governance by casting votes that are recorded and finalized within predictable time bounds. The resulting ledger provides a transparent, independently verifiable record of the decision-making process.

## Why Leios stands out

Leios focuses on increasing throughput while preserving reliability and decentralization. A projected range of 100–1,000 TPS would allow many applications to operate concurrently with lower risk of congestion than today’s baseline. Elastic capacity is intended to absorb temporary demand spikes, which is relevant for time-sensitive use cases such as decentralized finance and voting.

Cardano’s network of approximately 3,000 stake pools supports decentralization at the consensus layer. In addition, partial transaction determinism aims to keep fees largely predictable, with limited variance in contention scenarios. This improves cost transparency for applications such as microtransactions or identity systems, where stable fees are important for usability and planning.

Compared with Ethereum and Bitcoin, which face throughput constraints under heavy load, and Solana, which operates with a comparatively concentrated validator set, Leios emphasizes a balance between scale and distributed participation.

## The road ahead

Leios remains in research and development, with further simulations, prototypes, and public test networks expected before any production deployment. Broader adoption will depend on implementation maturity, ecosystem readiness, and governance approval.

Open challenges, including transaction conflicts and adversarial scenarios, are under active analysis. Proposed mitigations include mechanisms such as collateralization and pre-validation approaches to reduce the impact of double-spend attempts or invalid transactions.

If adopted through Cardano’s governance processes, Leios would expand the network’s capacity while maintaining its existing security and decentralization principles. Community participation from stake pool operators, delegated representatives, developers, and users will be central to evaluating and refining the proposal.
