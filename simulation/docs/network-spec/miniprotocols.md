# Mini Protocols

## Mini Protocols

For background information on mini protocols see sections 3.1-3.4 of the *Ouroboros Network Specification*¹, and rest of that chapter for the mini protocols already in use. Here we will present the additional node-to-node mini protocols needed for Leios.

¹ https://ouroboros-network.cardano.intersectmbo.org/pdfs/network-spec/network-spec.pdf#chapter.3

## Relay mini-protocol

#### Description

The Relay protocol presented here is a generalization of the tx submission protocol used to transfer transactions between full nodes. We will use the term *datum* as a generic term for the payloads being diffused, which we expect to be generally small: transactions, input block headers, endorse block headers², vote bundles for a single pipeline and voter.

² At the network layer we split an endorse block into header and body, where the latter contains the references to other blocks.

The protocol follows a pull-based strategy where the consumer asks for new ids/datums and the producer sends them back. It is designed to be suitable for a trustless setting where both sides need to guard against resource consumption attacks from the other side.

**Options and Parameters**

A Relay instance is specified by these options and parameters:

- **BoundedWindow**: The peers manage a bounded window (i.e. FIFO queue) of datums available to be requested. Useful for datums that are otherwise unbounded in number.
- **Announcements**: Producers provide additional announcements about datums, when available.
- **id**: Identifier for a datum to be relayed, used when requesting the datum.
- **info**: Extra information provided with a new id.
- **datum**: The datum itself.
- **Ann. Condition (If Announcements)**: Condition for announcement.
- **ann (If Announcements)**: Announcement representation.

**Instances**

Relay protocol instances are listed in the table below. Tx-submission is further parameterized by the maximum window size allowed. IB-relay, EB-relay, and Vote-relay are each parametrized by the maximum age beyond which a datum is no longer relayed³. IB-relay and EB-relay rely on Announcements to let consumers know when block bodies are available as well. Consumers request IB and EB bodies through the corresponding Fetch mini protocol. For EB-relay we specify the datum to be eb-header, by which we mean the constant size part of an Endorse block, while the references (to IBs and EBs) are considered the body.

³ Older EBs and IBs referenced by the blockchain can be accessed from the CatchUp mini protocol.

> **TODO**: For IB, EB, and Vote the info could actually be unit as we do not need to apply prioritization to headers. However the slot might provide useful filtering, such as avoid downloading any more votes of a pipeline once we have a certificate for a seen EB.

| instance | BoundedWindow | Announcements | id | info | datum | Ann. Condition | ann |
|----------|---------------|---------------|----|----- |-------|----------------|-----|
| Tx-submission | Yes | No | txid | size | tx | N/A | N/A |
| IB-relay | No | Yes | hash | slot | ib-header | body available | unit |
| EB-relay | No | Yes | hash | slot | eb-header | body available | unit |
| Vote-relay | No | No | hash | slot | vote-bundle | N/A | N/A |

*Table: Relay mini-protocol instances*

### State machine

The state machine diagram shows the following states and transitions:

**States:**
- **StInit** (Producer agency) - Initial state
- **StIdle** (Consumer agency) - Idle state
- **StIdsBlocking** (Producer agency) - Blocking ids request state
- **StIdsNonBlocking** (Producer agency) - Non-blocking ids request state  
- **StData** (Producer agency) - Data transfer state
- **StDone** - Terminal state

**Transitions:**
- StInit → StIdle: MsgInit
- StIdle → StIdsBlocking: MsgRequestIdsBlocking
- StIdsBlocking → StIdle: MsgReplyIds⟨AndAnns⟩
- StIdle → StIdsNonBlocking: MsgRequestIdsNonBlocking
- StIdsNonBlocking → StIdle: MsgReplyIds⟨AndAnns⟩
- StIdle → StData: MsgRequestData
- StData → StIdle: MsgReplyData
- StIdsBlocking → StDone: MsgDone

| state | agency |
|-------|--------|
| StInit | Producer |
| StIdle | Consumer |
| StIdsBlocking | Producer |
| StIdsNonBlocking | Producer |
| StData | Producer |

*Table: Relay state agencies*

**Grammar**

```
ack ::= number     if BoundedWindow
     |  unit       otherwise
req ::= number
```

**Protocol messages**

- **MsgInit**: initial message of the protocol
- **MsgRequestIdsNonBlocking (ack, req)**: The consumer asks for new ids and acknowledges old ids. The producer replies immediately, possibly with an empty reply if nothing new is available.
- **MsgRequestIdsBlocking (ack, req)**: Same as MsgRequestIdsNonBlocking but the producer will block until the reply will be non-empty.
- **MsgReplyIds (⟨(id, info)⟩)**: The producer replies with a list of available datums. The list contains pairs of ids and corresponding information about the identified datum. In the blocking case the reply is guaranteed to contain at least one id. In the non-blocking case, the reply may contain an empty list.
- **MsgReplyIdsAndAnns (⟨(id, info)⟩, ⟨(id, ann)⟩) (Requires Announcements)**: Same as MsgReplyIds but additionally the producer might, at most once, also provide an announcement for any id it has sent, in this message or previously.
- **MsgRequestData (⟨id⟩)**: The consumer requests datums by sending a list of ids.
- **MsgReplyData (⟨datum⟩)**: The producer replies with a list of the requested datums, some may be missing if no longer available for relay.
- **MsgDone**: The producer terminates the mini protocol.

| from state | message | parameters | to state |
|------------|---------|------------|----------|
| StInit | MsgInit | | StIdle |
| StIdle | MsgRequestIdsBlocking | $ack, req$ | StIdsBlocking |
| StIdsBlocking | MsgReplyIds | $⟨(id, info)⟩$ | StIdle |
| StIdle | MsgRequestIdsNonBlocking | $ack, req$ | StIdsNonBlocking |
| StIdsNonBlocking | MsgReplyIds | $⟨(id, info)⟩$ | StIdle |
| StIdle | MsgRequestData | $⟨id⟩$ | StData |
| StData | MsgReplyData | $⟨datum⟩$ | StIdle |
| StIdsBlocking | MsgDone | | StDone |

If Announcements is set, MsgReplyIds messages are replaced with MsgReplyIdsAndAnns:

| from state | message | parameters | to state |
|------------|---------|------------|----------|
| StIdsBlocking | MsgReplyIdsAndAnns | $⟨(id, info)⟩, ⟨(id, ann)⟩$ | StIdle |
| StIdsNonBlocking | MsgReplyIdsAndAnns | $⟨(id, info)⟩, ⟨(id, ann)⟩$ | StIdle |

*Table: Relay mini-protocol messages*

### Producer and Consumer Implementation

The protocol has two design goals: It must diffuse datums with high efficiency and, at the same time, it must rule out asymmetric resource attacks from the consumer against the provider.

The protocol is based on two pull-based operations. The consumer can ask for a number of ids and it can use these ids to request a batch of datums. The consumer has flexibility in the number of ids it requests, whether to actually download the datum of a given id and flexibility in how it batches the download of datums. The consumer can also switch between requesting ids and downloading datums at any time. The protocol supports blocking and non-blocking requests for new ids. The producer must reply immediately (i.e. within a small timeout) to a non-blocking request. It replies with not more than the requested number of ids (possibly with an empty list). A blocking request on the other hand, waits until at least one datum is available.

It must however observe several constraints that are necessary for a memory efficient implementation of the provider.

**With BoundedWindow**

Conceptually, the provider maintains a limited size FIFO of outstanding transactions per consumer. (The actual implementation can of course use the data structure that works best). The maximum FIFO size is a protocol parameter. The protocol guarantees that, at any time, the consumer and producer agree on the current size of that FIFO and on the outstanding transaction ids. The consumer can use a variety of heuristics for requesting transaction ids and transactions. One possible implementation for a consumer is to maintain a FIFO which mirrors the producer's FIFO but only contains the id and info pairs and not the datum.

After the consumer requests new ids, the provider replies with a list of ids and puts these datums in its FIFO. If the FIFO is empty the consumer must use a blocking request otherwise a non-blocking request. As part of a request a consumer also acknowledges the number of old datums, which are removed from the FIFO at the same time. The provider checks that the size of the FIFO, i.e. the number of outstanding datums, never exceeds the protocol limit and aborts the connection if a request violates the limit. The consumer can request any batch of datums from the current FIFO in any order. Note however, that the reply will omit any datums that have become invalid in the meantime. (More precisely the producer will omit invalid datums from the reply but they will still be counted in the FIFO size and they still require an acknowledgement from the consumer).

**Without BoundedWindow**

A Relay mini protocol instance that does not make use of BoundedWindow will want to rely on other ways to bound the amount of datums that can be requested at a given time. The consumer shall request ids in a blocking way when it does not intend on requesting any of the available datums.

**Equivocation handling**

IB-relay, EB-relay, and Vote-relay must guard against the possibility of equivocations, i.e. the reuse of a generation opportunity for multiple different blocks. The *message identifier* of an header is the pair of its generating node id and the slot it was generated for⁴. Two headers with the same message identifier constitute a *proof of equivocation*, and the first header received with a given message identifier is the *preferred header*. For headers with the same message identifier, only the first two should be relayed, furthermore only the body of the preferred header should be fetched.

⁴ For IBs/EBs also its subslot, in case generation frequency is greater than 1/slot.

## Fetch mini-protocol

### Description

The Fetch mini protocol enables a node to download block bodies. It is a generalization of the BlockFetch mini protocol used for base blocks: IBs and EBs do not have a notion of range, so they are requested by individual identifiers.

> **TODO**: Generalizing from BlockFetch means we deliver bodies in a streaming fashion, is that appropriate for IBs and EBs?

**Parameters**

A Fetch instance is specified by these parameters:

- **request**: request format for a sequence of blocks.
- **body**: Block body itself.

**Instances**

Fetch instances are listed in the table below. The body descriptions included here are for illustration, in particular to clarify what we mean by body of an Endorse block. A point is a pair of slot and hash, the slot allows for better indexing. A range is a pair of two of point | origin. The IB-fetch and EB-fetch instances are intended for on-the-fly block diffusion, complementing the corresponding Relay mini protocols.

| instance | request | body |
|----------|---------|------|
| IB-fetch | [point] | [Tx] |
| EB-fetch | [point] | ([IBRef], [EBRef]) |
| BlockFetch | range | RB body |

*Table: Fetch mini-protocol instances*

### State machine

The state machine has the following states and transitions:

**States:**
- **StIdle** (Consumer agency) - Initial state
- **StBusy** (Producer agency) - Processing request
- **StStreaming** (Producer agency) - Streaming data
- **StDone** - Terminal state

**Transitions:**
- StIdle → StDone: MsgConsumerDone
- StIdle → StBusy: MsgRequestBodies
- StBusy → StIdle: MsgNoBlocks
- StBusy → StStreaming: MsgStartBatch
- StStreaming → StStreaming: MsgBody (loop)
- StStreaming → StIdle: MsgBatchDone

| state | agency |
|-------|--------|
| StIdle | Consumer |
| StBusy | Producer |
| StStreaming | Producer |

*Table: Fetch state agencies*

**Protocol messages**

- **MsgRequestBodies (request)**: The consumer requests a sequence of bodies from the producer.
- **MsgNoBlocks**: The producer tells the consumer that it does not have all of the blocks in the requested sequence.
- **MsgStartBatch**: The producer starts body streaming.
- **MsgBody (body)**: Stream a single block's body.
- **MsgBatchDone**: The producer ends block streaming.
- **MsgConsumerDone**: The consumer terminates the protocol.

Transition table:

| from state | message | parameters | to state |
|------------|---------|------------|----------|
| StIdle | MsgConsumerDone | | StDone |
| StIdle | MsgRequestBodies | request | StBusy |
| StBusy | MsgNoBlocks | | StIdle |
| StBusy | MsgStartBatch | | StStreaming |
| StStreaming | MsgBody | body | StStreaming |
| StStreaming | MsgBatchDone | | StIdle |

*Table: Fetch mini-protocol messages*

**Implementation**

The high-level description of the Leios protocol specifies freshest-first delivery for IB bodies, to circumvent attacks where a large amount of old IBs gets released by an adversary. The Relay mini protocol already takes a parameter that specifies which IBs are still new enough to be diffused, so older IBs are already deprioritized to only be accessible through the CatchUp protocol, and only if referenced by other blocks.

Nevertheless consumers should take care to send approximately just enough body requests to utilize the available bandwidth, so that they have more choices, and more up to date information, when deciding which blocks to request from which peers.

## CatchUp mini-protocol

### Description

The CatchUp mini protocol allows for nodes to obtain IB and EB blocks referenced by the chain. These will typically be too old to be diffused by the Relay and Fetch mini protocols, but are still relevant to reconstruct the ledger state. Additionally it covers certified EBs not yet in the chain but which are still recent enough for inclusion in a future ranking block, and any blocks they reference.

> **TODO**: Unless we specify recent certified EBs are to be offered through the Relay protocol still, in which case request "Recent certified EBs by slot range" can be dropped.

This data, together with the base chain, is what is needed for a node to participate in future pipelines.

The protocol should allow the consumer to divide the requests between different producers, and for the producer to have an efficient way to retrieve the requested blocks.

The consumer should be able to retrieve the base chain through the other mini protocols, and so the EB references within. However, the slots of those EBs are unknown, as well as any indirect references.

**Requests**

- **EBs by RB range**: given an RB range from its chain, the producer should reply with all EBs which are (i) transitively referenced by RBs in that range, (ii) not referenced by earlier RBs.
- **Recent certified EBs by slot range**: given a slot range, the producer should reply with all certified EBs which are (i) generated in the slot range, (ii) not referenced by RBs⁵. The start of the slot range should be no earlier than the oldest slot an EB could be generated in and still referenced in a future RB.
- **Certificate by EB point**: given the point of a certified EB not referenced by the chain, the producer should reply with a certificate for it. Needed for inclusion of the EB into a future RB produced by the consumer.
- **IBs by EB point, and slot range**: given a point for a certified EB, the producer should reply with all the IBs which are (i) generated in the given slot range, (ii) directly referenced by the EB. The slot range allows for partitioning request about the same EB across different peers.

⁵ Restriction (ii) is to avoid overlap with an RB range query, but could be dropped to save on complexity if not worth the saved bandwidth.

> **TODO**: The *IBs by EB point, and slot range* request could be replaced by just a list of IB points, if IB references in EB bodies are augmented with the IB slot. Maybe size of request could become a consideration: by EB point and slot range the request size is 56 bytes for possibly all the referenced IBs at once, while by IB point the size is 40 bytes each, and there could be double digits of them. If expect to always fragment requests to just a few IBs at a time the difference is perhaps not important.

> **TODO**: The *EBs by RB range* request could similarly be replaced by a list of EB points, if EB references in RBs and EBs are augmented with the EB slot. In this case, the consumer would be in charge of discovering needed referenced EBs as it fetches the ones it knows about.

**Definition**

The CatchUp protocol is defined as a new instance of the Fetch protocol. We give the parameters as a grammar:

```
request_CatchUp ::= ebs-by-rb-range(range)
                 |  ebs-by-slot-range(slot, slot)
                 |  ibs-by-eb-and-slot-range(point, (slot, slot))

body_CatchUp ::= ib-block(ib-header, ib-body)
              |  eb-block(eb-header, eb-body)
              |  eb-certificate(certificate)
```

Alternatively there could be separate mini protocols for IB, EB, and Certificate CatchUp, so that there cannot be a format mismatch between requests and replies.

**Implementation**

To fulfill the higher-level freshest-first delivery goal, we might need to stipulate that producers should prioritize serving requests for the {IB,EB,Vote}-Relay and {IB,EB}-Fetch mini protocols over requests for CatchUp. 