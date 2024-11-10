# Model parameters for simulating or otherwise analyzing Leios

This document attempts to provide an overview and a reference of all relevant system parameters for analyzing, simulating, or prototyping the Leios protocol on top of Ouroboros Praos.
The Leios protocol has several open design choices and free parameters that will need to be fixed before proposing its production implementation, which is the reason for performing the aforementioned analyses and tests.

The referenced parameters themselves are presented in machine-readable form in [simulation-model-parameters.json](simulation-model-parameters.json).
Each parameter is given in the natural unit corresponding to its nature:

- sizes are given in bytes
- durations, delays, and latencies are given in seconds
- bandwidths are given in bytes per second
- CPU intensities are given in standard CPU core equivalents

## Node roles and their activities

In this section we look at the participants of the Ouroboros Leios network to enumerate the relevant activities that they are expected to perform.
We then characterise said activities in the next section.

### Block Producer

Block producers form the backbone of the Cardano network as they provide the actual functionality and thus create the value of the whole enterprise.
Their activities are:

- reception of transactions
- storing of transactions in the mempool
- validating of transactions against the latest ledger state
- executing the VRF lotteries for input blocks, endorser blocks, and ranking blocks
- creating input blocks
- storing input blocks
- sending input blocks
- receiving input blocks
- validating input blocks
- creating endorser blocks
- storing endorser blocks
- sending endorser blocks
- receiving endorser blocks
- validating endorser blocks
- computing EB votes
- sending EB votes
- receiving EB votes
- validating EB votes
- creating ranking blocks
- storing ranking blocks
- sending ranking blocks
- receiving ranking blocks
- validating ranking blocks
- updating the ledger state upon chain head change
- storing ledger state
- removing transactions from the mempool

### Relay

Relays are typically used to shield a block producer from the internet, acting as an application layer gateway within a demilitarised network zone.
Technically, a relay is identical to a block producer that holds no stake, which means that it performs all the same activities as a block producer apart from those that create data (like blocks, votes, or transactions).

### Client

*TODO*

## Network activities

This section gathers all network-based activities from the per-role sections above and discusses their structure as well as relevant parameters.
The parameters referenced below are found under `network/` in the JSON file.

### reception of transactions

Relays and block producers receive transactions that originate from clients and are diffused across the network.
This process is initiated by a node when it has a new transaction available by announcing it to its peers, but those peers control the transfer of the transaction data by requesting it when they are ready to receive and process it (which depends among others on whether there is room in their mempools).

relevant parameters:

- `announcement_size`
- `data_request_size`
- `Txn_size`
- `Txn_reserved_bandwidth`

### sending an input block from node to node

This action is a five-step process which the sender initiates by announcing the availability by sending a hash.
The recipient may then decide to request the block header (if it doesn’t yet have it), which is subsequently transferred back.
Based on the header contents the recipient may decide to request the block data, which is subsequently transferred back.
The last request–reply pair is governed by the “freshest first” traffic shaping policy in the Leios network, with freshness (and validity) being judged based on the header contents.

relevant parameters:

- `announcement_size`
- `data_request_size`
- `IB_header_size`
- `IB_body_size`
- `Leios_reserved_bandwidth`

### sending an endorser block from node to node

This action is a five-step process which the sender initiates by announcing the availability by sending a hash.
The recipient may then decide to request the block header (if it doesn’t yet have it), which is subsequently transferred back.
Based on the header contents the recipient may decide to request the block data, which is subsequently transferred back.
The last request–reply pair is governed by the “freshest first” traffic shaping policy in the Leios network, with freshness (and validity) being judged based on the header contents.

relevant parameters:

- `announcement_size`
- `data_request_size`
- `EB_header_size`
- `EB_body_size`
- `Leios_reserved_bandwidth`

### sending an EB vote from node to node

This process is initiated by a node when it has a new vote available by announcing it to its peers, but those peers control the transfer of the vote data by requesting it when they are ready to receive and process it.

relevant parameters:

- `announcement_size`
- `data_request_size`
- `EB_vote_size`
- `Leios_reserved_bandwidth`

### sending a ranking block from node to node

This action is a three-step process where the sender announces the availability by sending a hash, the recipient asks for the block by sending a request to the sender, who will then transfer either the block or an error response back to the recipient.
Note the inversion of control here for the main data transfer, which is deliberate to implement strict flow control on the network: a node manages its own ingress traffic by asking for blocks to be sent to it.

relevant parameters:

- `announcement_size`
- `data_request_size`
- `RB_size`
- `Praos_reserved_bandwidth`

## Network properties

While the section above describes how nodes intend to use the network, this section describes how the network responds to those intents.

### Topology

The statistical model of the network has been fitted to the observed block diffusion times within the Peras investigation using as basis a random graph modified by an average local cluster coefficient.
The corresponding parameters are found under `net_model/topology/` in the JSON file.

That section also contains the network size as well as the number of block producers; these can be used to compute e.g. the stake per producer according to some chosen distribution.

### Simplified model

The simplified model used so far for initial analyses has been taken from the [Peras Technical Report 1](https://peras.cardano-scaling.org/docs/reports/tech-report-1/#certificates-in-block-header).
It classifies inter-node connections as short/medium/long range and regards data of classes small (1500B)/midsize (64kB)/large (1MB).
The respective network latencies are found under `net_model/simple/` in the JSON file.

## Computation activities

This section gathers all computations from the per-role sections above that happen locally to a node.
In this context, “intensity” refers to a CPU utilization metric that at this point still remains to be defined.
The parameters referenced below are found under `computation/` in the JSON file.

### validating a transaction

A transaction is validated both syntactically and semantically, where the latter requires a ledger state to ascertain that all inputs are still available.

relevant parameters:

- `Txn_validation_latency`
- `Txn_validation_intensity`

### executing VRF lottery

Whenever a block producer may be allowed to create something, it runs a VRF lottery to discover whether it shall actually do so.

relevant parameters:

- `VRF_lottery_latency`
- `VRF_lottery_intensity`

### creating an input block

When a node wins the VRF lottery for IB creation it will assemble transactions from its mempool and create an IB containing them.

relevant parameters:

- `IB_creation_latency`
- `IB_creation_intensity`

### validating an input block

Validating an IB validates the contained transactions for validity (but it isn’t yet clear to me against which ledger state).

relevant parameters:

- `IB_validation_latency`
- `IB_validation_intensity`

### creating an endorser block

When a node wins the VRF lottery for EB creation it will create an EB referencing all valid IBs it has received for the pipeline that is currently in the endorse phase.

relevant parameters:

- `EB_creation_latency`
- `EB_creation_intensity`

### validating an endorser block

Validating an EB validates the referenced IB and their contained transactions for validity (but it isn’t yet clear to me against which ledger state).

relevant parameters:

- `EB_validation_latency`
- `EB_validation_intensity`

### creating an EB vote

For a pipeline in the voting phase a node may create a certificate for an EB it has seen and validated.

relevant parameters:

- `EB_vote_creation_latency`
- `EB_vote_creation_intensity`

### validating an EB vote

The vote is validated syntactically and semantically by verifying the availability and correctness of its block references and signatures.

relevant parameters:

- `EB_vote_validation_latency`
- `EB_vote_validation_intensity`

### creating a ranking block

A node that has seen enough votes for an EB and has won the Praos VRF lottery may create a certificate for the EB and place it within a newly minted ranking block.

relevant parameters:

- `RB_creation_delay`
- `RB_creation_intensity`

### validating a ranking block

Praos blocks are validated syntactically and semantically against the latest ledger state as they diffuse across the network.

relevant parameters:

- `RB_validation_delay`
- `RB_validation_intensity`

### updating the ledger

Whenever a new longest chain is found, the ledger state is computed for this chain, expanding each Praos block potentially into EBs and in turn into IBs to extract transactions.

relevant parameters:

- `Ledger_update_intensity`
- `Ledger_update_delay`

## Storage activities

This section lists all parameters related to storage activities, where the mempool is considered as a storage arena.
The parameters referenced below are found under `storage/` in the JSON file.

- `Txn_store_delay` is the duration it takes to add a transaction to the mempool
- `IB_store_delay` is the duration it takes to store an input block on disk and update indexes
- `EB_store_delay` is the duration it takes to store an endorser block on disk and update indexes
- `EB_vote_store_delay` is the duration it takes to store an EB vote on disk and update indexes
- `RB_store_delay` is the duration it takes to store a Praos block on disk and update indexes
- `Ledger_store_delay` is the duration it takes to store a ledger snapshot on disk
- `Ledger_update_delay` is the duration it takes to compute and make available in memory a new ledger snapshot by applying an RB to the preceding ledger state
- `Txn_prune_delay` is the duration it takes to remove transactions referenced by a Praos block from the mempool
