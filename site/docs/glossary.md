---
sidebar_position: 5
---

# Glossary

- **50% disk compression**: A default estimate in Leios cost calculations that estimates storage savings through compression techniques.

- **Approximate Lower Bound Argument (ALBA)**: A cryptographic technique allowing a prover to succinctly demonstrate knowledge of a large dataset to a verifier, with a small approximation gap enabling efficient proof generation and verification. One of the proposed certificate schemes for Leios voting.

- **Blacklisting**: A mechanism in Leios mempool design where UTxOs appearing in certified endorser blocks are temporarily marked as unavailable to prevent double-spending until they are included in ranking blocks.

- **Blob Leios**: A variant of Leios that provides data availability without processing Cardano transactions, useful for applications like governance voting or bulletin boards.

- **Boneh-Lynn-Shacham (BLS)**: A cryptographic signature scheme that allows for efficient aggregation of signatures. Used in the proposed Leios voting and certificate system.

- **Central processing unit (CPU) and cumulative distribution function (CDF) usage**: A performance metric that tracks CPU consumption across various simulation stages.

- **Certificate**: A cryptographic proof that attests to the validity of blocks or transactions. In Leios, certificates are created when a quorum of votes is reached for an endorser block and are included in ranking blocks.

- **Collateral marking**: A mechanism where UTxOs used as collateral are explicitly marked to ensure they cannot be transferred while serving as collateral for transaction conflict resolution.

- **Committee**: The set of stake pool operators selected as eligible voters for a particular Leios election, typically consisting of around 500 voters.

- **Conformance events**: Standardized event outputs from Leios simulations used for testing and verification that implementations conform to protocol specifications.

- **Decentralization parameter**: A measure of how distributed the control of the network is among its participants. Currently set to 500 on Cardano mainnet.

- **DeltaQ model**: A framework for analyzing and predicting network quality of service (QoS) used to assess delay, loss, and other performance factors in Leios simulations.

- **Deterministic transactions**: A property of Cardano where transactions either succeed completely or have no effect on the ledger, unlike Ethereum where failed transactions still consume gas fees. Leios aims to preserve this property while enabling high throughput.

- **Diffusion strategy**: The method used to propagate blocks and votes through the network. Strategies include:
  - Oldest-first strategy – prioritizes older blocks for diffusion.
  - Freshest-first strategy – prioritizes newer blocks for diffusion.
  - Peer-order strategy – requests blocks in the order they were announced by peers.

- **Diffusion time**: The time required for a block to propagate to all nodes in the network, typically around 5 seconds for Cardano.

- **Election ID**: An 8-byte identifier used in Leios voting to uniquely identify a specific voting round, typically derived from the slot number.

- **Eligibility proof**: A cryptographic proof that demonstrates a node's right to participate in sortition for block production or voting, using VRF outputs and stake information.

- **Endorser block (EB)**: A block that references one or more input blocks (IBs) and undergoes a voting process for certification. Produced by nodes that win the EB sortition lottery.

- **Epoch**: A fixed period in the blockchain during which specific processes or calculations are performed.

- **Equivocation**: The act of producing conflicting blocks or messages in a blockchain network.

- **Executable specification**: A formally defined, executable model of a system that ensures an implementation conforms to its intended design.

- **Fait accompli sortition**: A cryptographic selection process that creates a hybrid committee containing both deterministic persistent voters and randomly selected non-persistent voters, ensuring fairness and verifiability when choosing validators.

- **Freshest first**: A policy for prioritizing newer blocks or transactions over older ones.

- **Frontrunning**: An attack vector in Leios where a stake pool operator delays input block production to observe other blocks in the same pipeline, potentially gaining information advantage. The opportunity is bounded by stage lengths (several seconds).

- **Full Leios**: The complete version of the Leios protocol that provides robust throughput guarantees by allowing endorser blocks to reference other endorser blocks, unlike Short Leios.

- **Full Sharding**: A Leios ledger design approach where each input block is assigned a shard-id, UTxOs are labeled with shard-ids, and transactions can only spend UTxOs from the same shard, preventing conflicts but introducing inclusion delays.

- **Haskell simulation**: A high-fidelity simulation of the Leios protocol in Haskell, used for latency measurement, event logging, and parameter tuning with detailed TCP implementation.

- **Header diffusion time**: The specific time parameter for propagating block headers through the network, typically faster than full block diffusion.

- **Input block (IB)**: A block that contains transactions and is produced by nodes that win the IB sortition lottery. The basic unit for transaction processing in Leios.

- **IB ordering**: The sequence in which input blocks are arranged within endorser blocks. Currently under specification, with proposals ranging from slot-ascending order to EB producer discretion, with implications for frontrunning prevention.

- **IB sharding**: A mechanism where input blocks are assigned to specific shards based on their VRF values, with parameters controlling shard period length and group count to manage transaction distribution.

- **Late IB inclusion**: An extension to Full Leios that allows referencing input blocks from older pipelines that didn't have endorser blocks, significantly improving transaction inclusion rates.

- **Latency**: The delay between the submission of a transaction and its confirmation on the blockchain.

- **Leios cost calculator**: An online tool that estimates the computational and financial costs of running Leios nodes, supporting both hyperscale and discount cloud providers.

- **Leios transaction lifecycle**: The complete journey of a transaction through the Leios protocol, from submission to final confirmation, typically involving seven stages from memory pool to ranking block inclusion.

- **Leios-stage-active-voting-slots**: A parameter that configures the duration of active voting stages in the Leios protocol.

- **Leios-vote-send-recv-stages**: A configuration setting that defines the voting stages in the Leios protocol, including the send and receive phases.

- **Local sortition**: A mechanism for selecting non-persistent voters for each election using VRF-based random selection, complementing the deterministic persistent voters from Fait Accompli sortition.

- **Lovelace**: The smallest unit of the Cardano cryptocurrency, named after Ada Lovelace.

- **Max window size**: A diffusion protocol parameter that limits the number of blocks that can be requested or held in memory during block propagation.

- **Mempool snapshotting**: The process of capturing the current state of pending transactions for inclusion in a block, taking approximately 72ms in current Cardano implementations.

- **Miniprotocols**: The specific network communication protocols used for different types of block and vote diffusion in Leios, each optimized for particular message types.

- **Mithril**: A protocol for stake-based threshold multisignatures that could be used for voting and cryptographic proofs in the Leios framework.

- **MUSEN**: MUlti-Stage key-Evolving verifiable random fuNctions - a cryptographic protocol that combines VRFs with key evolution and signature aggregation capabilities. One of the proposed certificate schemes for Leios.

- **Non-persistent voters**: Voters selected through local sortition for individual elections, as opposed to persistent voters who participate in all elections during an epoch.

- **One EB per RB**: The current design constraint that each ranking block contains at most one endorsement, simplifying the protocol structure while allowing recursive EBs to represent multiple input blocks.

- **Optimistic validation**: A mechanism that allows transactions to reference UTxOs from not-yet-settled blocks, with the caveat that fees must still be paid if the referenced transaction is not executed.

- **Organic topology generator**: A tool that creates network topologies based on real-world stake pool and relay connections to simulate actual network behavior.

- **Overcollateralization**: A strategy in Leios where transactions pay additional fees to compensate for potential conflicts and duplicates in the mempool, particularly relevant in shardless scenarios. One of the three main ledger design proposals.

- **Persistent voters**: Voters selected deterministically through Fait Accompli sortition who participate in all elections during an epoch, reducing certificate size requirements.

- **Phase 1 validation**: The initial, computationally cheaper validation of a transaction that checks basic formatting and collateral availability before more expensive processing.

- **Phase 2 validation**: The computationally expensive validation of a transaction including full script execution and ledger state updates.

- **Pipeline**: A sequence of stages in the Leios protocol where different types of blocks are produced and processed in parallel to maximize throughput.

- **Praos**: The current version of the Ouroboros consensus protocol that Leios builds upon and extends.

- **Proof of possession**: A cryptographic proof that demonstrates ownership of a private key corresponding to a registered public key, required for BLS key registration in Leios voting.

- **Quorum**: The minimum number of votes required to certify an endorser block, typically set at 60% of the voting committee in Leios.

- **Ranking block (RB)**: A Praos-style block that ranks and orders other blocks as part of the consensus mechanism. Contains certificates for endorsed blocks and maintains the main blockchain.

- **Rational arithmetic**: A method used in Leios sortition to replace quad-precision floating-point calculations, improving precision and computational efficiency.

- **Relay strategy**: The method used by nodes to forward blocks and votes through the network topology, affecting diffusion performance and resource usage.

- **Rust simulation**: A high-performance simulation of the Leios protocol implemented in Rust, focusing on graph generation, topology creation, and performance visualization.

- **Send-recv voting**: A structured two-stage voting mechanism where nodes send and receive votes in separate phases.

- **Shard-id**: An identifier assigned to input blocks and UTxOs in the Full Sharding approach, ensuring that transactions can only spend UTxOs from the same shard to prevent conflicts.

- **Sharding**: A method of partitioning data or transactions to improve scalability and performance and reduce duplication. In Leios ledger design, refers to assigning transactions and UTxOs to specific shards to prevent conflicts.

- **Short Leios**: A simplified variant of Leios that doesn't allow endorser blocks to reference other endorser blocks. If an EB is not certified by a ranking block, it and the input blocks it references are not recorded in the ledger.

- **Simplified Leios**: The most basic variant of Leios with simplified mechanisms for block production and validation.

- **Slot timing relationships**: The critical constraints governing when input blocks from slot N can appear in ranking blocks, ensuring proper diffusion and voting time while preventing future references in the blockchain.

- **Sortition**: A probabilistic method for selecting nodes to perform specific roles (IB production, EB production, voting) based on their stake using verifiable random functions.

- **Spatial efficiency**: The ratio of the size of transactions included in the ledger divided by the total size of input blocks, endorser blocks, and ranking blocks constituting the ledger.

- **Stake**: The amount of cryptocurrency a node holds, which influences its probability of being selected in sortition.

- **Storage cost amortization**: A feature in the cost calculator that spreads storage costs over time, reducing upfront expenses.

- **Temporal efficiency**: The fraction of submitted transactions that successfully make it into the ledger.

- **Throughput**: The rate at which transactions are processed by the network, measured in transactions per second (TPS).

- **Throughput simulator**: A system that models the transaction processing rate of Cardano nodes, aligned with the Leios framework.

- **Tiebreaking rules**: Mechanisms for resolving conflicts when multiple input blocks have the same slot number, potentially using VRF outputs to provide objective randomness and prevent manipulation.

- **Tombstoning**: A storage optimization technique where duplicate or conflicting transactions are marked but not fully stored, saving space while maintaining references for validation.

- **Transaction lifecycle**: The complete process a transaction goes through in Leios, from submission to final inclusion in a ranking block, involving multiple stages and timing constraints.

- **UTxO-HD (UTxO on Hard Disk)**: A Cardano node optimization that reduces RAM requirements by storing UTxO data on disk, potentially reducing the cost of running stake pools and improving network sustainability.

- **UTxO labeling**: A mechanism in the Full Sharding approach where UTxOs are explicitly assigned shard-ids to control which input blocks can spend them, preventing conflicts between concurrent blocks.

- **Validation rules**: The specific criteria that endorser blocks, input blocks, and votes must satisfy to be considered valid, including structural, cryptographic, and timing requirements.

- **Verifiable Random Function (VRF)**: A cryptographic function that produces a random output that can be verified. Used in Leios for sortition and block production.

- **Vote bundling**: The process of aggregating multiple votes for the same endorser block to reduce network traffic and certificate size.

- **Vote weight**: The stake-based weight assigned to each vote in Leios, where persistent voters have weight equal to their stake and non-persistent voters have weight based on expected committee composition.
