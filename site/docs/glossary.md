---
sidebar_position: 5
---

# Glossary

#### 50% disk compression

A default assumption in Leios cost modelling that estimates storage savings through compression techniques.

#### Approximate Lower Bound Argument (ALBA)

A cryptographic technique allowing a prover to succinctly demonstrate knowledge of a large dataset to a verifier. One of the proposed certificate schemes for Leios voting.

#### Blacklisting

A mempool mechanism where UTXOs appearing in certified endorser blocks are temporarily marked as unavailable to prevent double-spending until they are included in a ranking block.

#### Boneh-Lynn-Shacham (BLS)

A cryptographic signature scheme that allows efficient aggregation of multiple signatures into one. Used in Leios for committee voting and certificate creation.

#### Certificate

A compact cryptographic proof that a quorum of votes has been reached for an endorser block. Certificates are included in ranking blocks to provide finality.

#### Committee

The set of stake pool operators selected as eligible voters for a given Leios election (typically ~500 voters).

#### DeltaQ model

A mathematical framework used in Leios simulations to analyse and predict real-world network behaviour (delay, loss, jitter).

#### Deterministic transactions

A core Cardano property preserved in Leios: transactions either succeed completely or have no effect on the ledger (no partial execution or wasted fees).

#### Diffusion strategy

The method used to propagate blocks and votes across the network. Supported strategies include:

-   Oldest-first
-   Freshest-first
-   Peer-order

#### Election ID

An 8-byte identifier used to uniquely identify a voting round (typically derived from the slot number).

#### Endorser block (EB)

A block that references one or more input blocks and undergoes committee voting for certification. Produced approximately every five seconds.

#### Fait accompli sortition

The hybrid sortition mechanism used in Leios that combines deterministic persistent voters with randomly selected non-persistent voters for each election.

#### Freshest-first

A diffusion policy that prioritises newer blocks or transactions.

#### Input block (IB)

The basic unit of transaction collection in Leios. Produced frequently (up to ~5 per second) by nodes that win the IB sortition lottery.

#### Linear Leios

The current production-oriented variant of Ouroboros Leios (CIP-0164). It retains the IB/EB/RB structure but simplifies the design for easier implementation, indexing, and deployment while maintaining high throughput.

#### Mempool snapshotting

The process of capturing the current state of pending transactions for inclusion in an input block (~72 ms in current implementations).

#### Mithril

A stake-based threshold multisignature protocol that may be used for efficient voting and proof aggregation in Leios.

#### MUSEN

MUlti-Stage key-Evolving verifiable random fuNctions – one of the proposed certificate schemes for Leios voting.

#### One EB per RB

Current design constraint in Linear Leios: each ranking block contains at most one endorsed endorser block, keeping the chain linear and simple.

#### Persistent / Non-persistent voters

Persistent voters are selected deterministically for the entire epoch; non-persistent voters are chosen per election via local sortition.

#### Pipeline

A sequence of stages in Leios where input blocks, endorser blocks, and ranking blocks are produced and processed in parallel to maximise throughput.

#### Praos

The current live version of Ouroboros (Ouroboros Praos) that Leios builds upon and extends.

#### Quorum

The minimum number of votes required to certify an endorser block (typically 60% of the committee).

#### Ranking block (RB)

The final anchoring block produced every ~20 seconds using Praos mechanics. It ranks endorsed blocks and provides the secure, linear chain.

#### Send-recv voting

A two-stage voting mechanism (send phase followed by receive phase) used to improve vote propagation reliability.

#### Sharding (input block sharding)

Current Leios approach that assigns input blocks to shards via VRF-derived shard-ids to reduce conflicts. Full ledger sharding is not part of Linear Leios.

#### Sortition

The cryptographic process (using VRFs) for fairly selecting nodes to produce blocks or participate in voting based on stake.

#### Spatial efficiency

The ratio of useful transaction data included in the ledger versus the total size of all blocks (IBs, EBs, RBs).

#### Temporal efficiency

The fraction of submitted transactions that successfully make it into the final ledger.

#### Throughput

The rate at which transactions are processed, measured in transactions per second (TPS). Linear Leios targets up to 1,500+ TPS.

#### UTXO-HD (UTXO on hard disk)

A Cardano node optimisation that stores UTXO data on disk to reduce RAM usage, beneficial for Leios node operators.

#### Verifiable Random Function (VRF)

A cryptographic primitive used in Leios for sortition, leader election, and eligibility proofs. The output is publicly verifiable but unpredictable.

#### Vote bundling

Aggregating multiple votes for the same endorser block to reduce network traffic and certificate size.

#### Vote weight

The stake-weighted value of each vote. Persistent voters carry full stake weight; non-persistent voters carry weight based on expected committee composition.

