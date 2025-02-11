---
sidebar_position: 1
---

# What is Ouroboros Leios?

:::warning
This website and the Ouroboros Leios project are in the early stages of research
and development. Details may be added, removed, or changed over the coming weeks
and months.
:::

The [Ouroboros consensus protocol](https://docs.cardano.org/about-cardano/learn/ouroboros-overview) lies at the heart of Cardano, driving secure
and efficient transaction settlement while supporting the network's scalability
and robustness.

[Ouroboros Leios](https://iohk.io/en/research/library/papers/high-throughput-blockchain-consensus-under-realistic-network-assumptions/) is the protocol version designed to increase the network's
throughput by optimizing the use of available resources and enabling faster
transaction processing and confirmation.

:::info
Currently, Cardano runs the Ouroboros Praos protocol, which introduced
substantial security and scalability improvements to Ouroboros Classic. Leios
remains in its research and development phase and will extend Praos'
capabilities upon its implementation.
:::

Leios is specifically designed to solve scalability bottlenecks in existing
systems by acting as a high-throughput overlay on top of base protocols. It
tackles malicious actions like protocol bursts (sudden floods of valid messages
to congest the network) and equivocations (double-signing attacks), enabling
near-optimal transaction processing while preserving security under real-world
network constraints.

To illustrate the Leios concept, imagine a blockchain as a single-lane road
prone to bottlenecks and delays – similar to how an accident on a one-lane road
can block traffic, causing long tailbacks (pending transactions). Leios
addresses this limitation by introducing multiple lanes, allowing multiple cars
(transactions) to travel simultaneously. This approach significantly improves
both speed and efficiency.

The key idea is to separate transaction ordering (which occurs on the base
chain) from transaction diffusion, availability, and validation. Ultimately,
these multiple lanes must merge into a single, orderly flow of vehicles – just
as the blocks of the underlying main chain consolidate transactions into a
final, agreed-upon sequence.

*Read the following sections to learn more about the protocol’s properties and high-level architecture.*
