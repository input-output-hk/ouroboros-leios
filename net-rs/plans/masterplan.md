# Leios Rust network stack

## Vision

A gold-standard implementation of the Cardano mini-protocol stack for Praos *and* Leios
protocols in Rust.

### Use cases

* Network prototyping and simulation
* Adversarial nodes
* Fast Leios on-ramp for downstream tools (e.g. Acropolis, Dolos, Ogmios...)
* Reference design for node implementors

## Context

The Praos miniprotocols are the existing network stack for the Cardano network. Leios is an
extension which adds new protocols and formats to improve performance while retaining safety.

We need to implement the existing Praos Node-to-Node (N2N) protocols and then extend them to Leios.
We do *not* need to implement the Node-to-Client (N2C) protocols and variants.

### References

Cardano network specification (Praos):

https://ouroboros-network.cardano.intersectmbo.org/pdfs/network-spec/network-spec.pdf

Cardano blueprint simplified description:

https://cardano-scaling.github.io/cardano-blueprint/network/index.html

CIP-0164 Leios specification:

https://cips.cardano.org/cip/CIP-0164#network

### Sources

Haskell networking library - only live deployment for Praos:

https://github.com/IntersectMBO/ouroboros-network

Existing Rust implementation - Pallas networking:

Version 1: https://github.com/txpipe/pallas/tree/main/pallas-network
Version 2: https://github.com/txpipe/pallas/tree/main/pallas-network2

## Requirements

### Development stack

* The network stack should be in a single crate within the Leios monorepo (net-rs)
* There should be minimal dependencies, and no C-binding dependencies.
  Any significant dependencies should be discussed and verified by a
  human,
* The code must only use fully released Rust features

### Code quality

* The code shall be high performance and high security
* The code shall be highly legible and understandable for a non-Rust
  developer.  If there is a choice between simplicity and concision,
  choose simplicity.
* The code may not panic in any circumstances - every unwrap() etc. error case must be handled

## Specific areas requiring detailed design

More detailed plans should be developed in the following areas:

### Multiplexing

The existing Praos mini-protocols are carried over a single multiplexed TCP socket for each
node pair (separately for each direction if duplexed).  In the current protocol there hasn't
been any need for a priority scheme or fair queuing, but Leios introduces large messages which
could head-of-line block time-critical Praos ones.

We therefore need to build in some QoS facilities into the multiplexer.  These should be pluggable
and configurable.  Options include:

* Strict priority based on protocol ID (DiffServ-like)
* Weighted fair queuing (WFQ) based on priority ID
* Both

### Codecs

We should investigate how the existing implementations serialise and deserialise the messages
into structures, and the most efficient way of presenting this in Rust.  We should investigate,
but not be hide-bound to, the idea of auto-generation of codecs from CDDL.

A wrinkle of the multiplexing protocol is that there are no framing bits indicating the start
and/or end of a message.  In some implementations this means successive attempts to decode the
payload to work out when a message has ended.  This is inefficient and we need to find a work
round for this.

### Timeouts

There are timeouts specified in the protocol definition but not every implementation adheres
to this.  We must, and we need to design in both detection and handling of timeouts.

### Alternate transports

The current implementations provide TCP sockets and local Unix sockets (for the N2C) protocols.
We don't need to implement the Unix sockets, but we shouldn't block future implementations from
doing so, so we still need a pluggable transport/bearer architecture.  We may also want to
experiment with alternate transports such as QUIC in the future, which would fit into the same
pattern.

## Implementation phases

### Phase 1: Basic Handshake

Implement a basic multiplexer and the Handshake protocol, and create a command line test
which can connect to an existing node.

### Phase 2: ChainSync / BlockFetch

Implement the Praos ChainSync and BlockFetch protocols and create a command line test that
can connect to an existing node, run ChainSync at the tip and fetch blocks as they are announced,
logging slot, block number and hash.

... TBC ...
