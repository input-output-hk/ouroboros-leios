---
sidebar_position: 6
---

# FAQs

## What are the benefits of Leios?

Ouroboros Leios is a blockchain protocol that improves transaction throughput and
latency by using a pipelined endorsing process. Simply put, Leios is a way to
process transactions faster.

## What are downstream effects of deploying Leios?

Ongoing internal discussions - we will publish an answer/link here to our
findings.

## Could the mempool be sized to the throughput of the system?

That's already the case. Default mempool size is a small multiple of current
block size.

## Can the system be sharded according to resources (small nodes vs. big nodes)?

Leios' current design does not involve sharding in a sense of different resource
requirements for different nodes. In short, the Leios design does not involve
sharding. These are ideas in research and require more work. As of now, each
node has to validate all blocks, hence in a traditional sense, adding more nodes
does not increase throughput. Each node must cope with the throughput of the
whole system.

## Can the system self-regulate instead of manually fine tuning?

The current system's load is imposed on each node through the protocol
parameters. Thus, it remains a democratic vote, not a choice made locally by
nodes or automatically. Given that the load is imposed on each node through the
choice of the protocol parameters, it remains a democratic vote to drive
adaptation. In a sharded approach this could be different. But in the current
system there is no local or automatic choice to be made by individual nodes.
