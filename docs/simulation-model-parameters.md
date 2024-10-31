# Model parameters for simulating or otherwise analyzing Leios

This document attempts to provide an overview and a reference of all relevant system parameters for analyzing, simulating, or prototyping the Leios protocol on top of Ouroboros Praos.
The Leios protocol has several open design choices and free parameters that will need to be fixed before proposing its production implementation, which is the reason for performing the aforementioned analyses and tests.

## Node roles and their activities

In this section we look at the participants of the Ouroboros Leios network to enumerate the relevant activities that they are expected to perform.
We then characterise said activities in the next section.

### Block Producer

Block producers form the backbone of the Cardano network as they provide the actual functionality and thus create the value of the whole enterprise.
Their activities are:

- reception of transactions from the relays
- storing of transactions in the mempool
- validating of transactions against the latest ledger state
- executing the VRF lotteries for input blocks, endorser blocks, and ranking blocks
- creating input blocks
- storing input blocks
- sending input blocks to the relays
- receiving input blocks from the relays
- validating input blocks
- creating endorser blocks
- storing endorser blocks
- sending endorser blocks to the relays
- receiving endorser blocks from the relays
- validating endorser blocks
- computing EB votes
- sending EB votes to relays
- receiving EB votes from relays
- validating EB votes
- creating ranking blocks
- storing ranking blocks
- sending ranking blocks to the relays
- receiving ranking blocks from the relays
- validating ranking blocks
- updating the ledger state upon chain head change
- storing ledger state
- removing transactions from the mempool

### Relay

*TODO*

### Client

*TODO*

## Network activities

This section gathers all network-based activities from the per-role sections above and discusses their structure as well as relevant parameters.

### sending a ranking block to a node

This action is a two-step process where the recipient asks for the block by sending a request to the sender, who will then transfer either the block or an error response back to the recipient.
Note the inversion of control here, which is deliberate to implement strict flow control on the network: a node manages its own ingress traffic by asking for blocks to be sent to it.

relevant parameters:

- request size: XXX B
- block size: XXX kiB
- latency distribution: (depends on how we want to slice it)
- CPU usage at block sender: (some profile over time)
- memory usage at block sender: (some profile over time)

### receiving a ranking block at a node

*TODO*

## Local activities

This section gathers all activities from the per-role sections above that happen locally to a node.

### validating a ranking block

*precise description to be done*

relevant parameters:

- CPU usage: (some time profile in useful units)
- latency distribution: (some profile over time)
- memory usage: (some profile over time)
