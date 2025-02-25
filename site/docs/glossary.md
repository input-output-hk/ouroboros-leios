---
sidebar_position: 5
---

# Glossary

- **50% disk compression**: A default estimate in Leios cost calculations that estimates storage savings through compression techniques.

- **Approximate Lower Bound Argument (ALBA)**: A cryptographic technique allowing a prover to succinctly demonstrate knowledge of a large dataset to a verifier, with a small approximation gap enabling efficient proof generation and verification.

- **Boneh-Lynn-Shacham (BLS)**: A cryptographic signature scheme that allows for efficient aggregation of signatures.

- **Central processing unit (CPU) and cumulative distribution function (CDF) usage**: A performance metric that tracks CPU consumption across various simulation stages.

- **Certificate**: A cryptographic proof that attests to the validity of blocks or transactions.

- **Decentralization parameter**: A measure of how distributed the control of the network is among its participants.

- **DeltaQ model**: A framework for analyzing and predicting network quality of service (QoS) used to assess delay, loss, and other performance factors.

- **Diffusion strategy**: The method used to propagate blocks and votes through the network. Strategies include:
  - Oldest-first strategy – prioritizes older blocks for diffusion
  - Freshest-first strategy – prioritizes newer blocks for diffusion
  - Peer-order strategy – requests blocks in the order they were announced by peers.

- **Endorser block (EB)**: A block that references IBs and is produced by nodes that win the EB sortition lottery.

- **Epoch**: A fixed period in the blockchain during which specific processes or calculations are performed.

- **Equivocation**: The act of producing conflicting blocks or messages in a blockchain network.

- **Executable specification**: A formally defined, executable model of a system that ensures an implementation conforms to its intended design.

- **Fait accompli sortition**: A cryptographic selection process that ensures fairness and verifiability when choosing validators.

- **Freshest first**: A policy for prioritizing newer blocks or transactions over older ones.

- **Haskell simulation**: A parallel simulation of the Leios protocol in Haskell, used for latency measurement, event logging, and parameter tuning.

- **Input block (IB)**: A block that contains transactions and is produced by nodes that win the IB sortition lottery.

- **Latency**: The delay between the submission of a transaction and its confirmation on the blockchain.

- **Leios cost calculator**: An online tool that estimates the computational and financial costs of running Leios nodes, supporting both hyperscale and discount cloud providers.

- **Leios transaction lifecycle**: A roadmap defining the different stages a transaction goes through, from submission to final confirmation within the Leios framework.

- **Leios-stage-active-voting-slots**: A parameter that configures the duration of active voting stages in the Leios protocol.

- **Leios-vote-send-recv-stages**: A configuration setting that defines the voting stages in the Leios protocol, including the send and receive phases.

- **Lovelace**: The smallest unit of the Cardano cryptocurrency, named after Ada Lovelace.

- **Mithril**: A protocol for voting and cryptographic proofs in the Leios framework.

- **Musen**: A cryptographic protocol or component used within the Leios framework.

- **Organic topology generator**: A tool that creates network topologies based on real-world stake pool and relay connections to simulate actual network behavior.

- **Pipeline**: A sequence of stages in the Leios protocol where different types of blocks are produced and processed.

- **Praos**: A version of the Ouroboros consensus protocol that Leios builds upon.

- **Quorum**: The minimum number of votes required to certify a block or decision.

- **Ranking block (RB)**: A block that ranks other blocks and is part of the consensus mechanism.

- **Rational arithmetic**: A method used in Leios sortition to replace quad-precision floating-point calculations, improving precision and computational efficiency.

- **Rust simulation**: A simulation of the Leios protocol implemented in Rust, focusing on graph generation, topology creation, and performance visualization.

- **Send-recv voting**: A structured two-stage voting mechanism where nodes send and receive votes.

- **Sharding**: A method of partitioning data to improve scalability and performance.

- **Short-Leios simulation**: A version of the Leios simulation that models ranking block intervals and outputs diffusion latency data.

- **Sortition**: A probabilistic method for selecting nodes to perform specific roles based on their stake.

- **Stake**: The amount of cryptocurrency a node holds, which influences its probability of being selected in sortition.

- **Storage cost amortization**: A feature in the cost calculator that spreads storage costs over time, reducing upfront expenses.

- **Throughput**: The rate at which transactions are processed by the network.

- **Throughput simulator**: A system that models the transaction processing rate of Cardano nodes, aligned with the Leios framework.

- **Verifiable Random Function (VRF)**: A cryptographic function that produces a random output that can be verified.
