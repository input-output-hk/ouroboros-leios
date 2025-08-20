## Mini Protocols

The design of the Leios mini protocols is predominantly determined by which information two nodes need to exchange, when that information should be sent, and how to bound resource utilization on both sides of the mini protocol.
Notably, the FreshestFirstDelivery scheme constrains some of the timings.

A CIP ideally proposes exact mini protocols, so that nodes with different implementors will be able to interact.
There is precedent for CIPs (eg Peras) to instead let the implementors determine the details of the mini protocol separate (preferably in a separate CIP).
However, optimized diffusion times are a core concern of Leios, so a more detailed mini protocol specification is appropriate in this CIP, at least to demonstrate feasibility and highlight key factors.

### Information Exchange Requirements

It would be premature to discuss concrete mini protocols without the motivating context of what information they're required to exchange.

The primary messages will carry information that is directly required by the Leios description above: headers, blocks, txs referenced by blocks, and votes for blocks.
However, some lower-level information must also be carried by secondary messages, eg indicating when the peer is first able to send the block.

The required exchanges between two neighboring nodes is captured by the following Information Exchange Requirements (IER) table.
Each row is a datum that some mini protocol message will carry, although a single message might bundle multiple rows.
Some of the details in this table are not fully compatible with the initial concrete iterations of the mini protocol below; they instead match the later iterations.

| Sender | Name | Arguments | Semantics |
| - | - | - | - |
| Client→ | LeiosNotificationsBytes | byte count | Requests Leios notifications (announcements and delivery offers) up to some total byte size. A low-watermark scheme would suffice to ensure there's always sufficient room for more notifications. |
| ←Server | LinearLeiosAnnouncement | RankingBlockHeader that announces an LLB | The server has seen this LLB announcement. The client should disconnect if the server sends a third announcement with the same election, since two already evidence equivocation. The client should disconnect if the header is invalid in a way that any recent ledger state could notice, not only the ledger state of the header's predecessor. |
| ←Server | LinearLeiosBlockOffer | slot and hash | The server could immediately deliver this block. The client should disconnect if the server had not already sent a LinearLeiosAnnouncement for the same block. |
| ←Server | LeiosBlockTxsOffer | slot and hash | The server could immediately deliver any tx referenced by this block. The client should disconnect if the server had not already sent a LinearLeiosAnnouncement for the same block. |
| ←Server | LinearLeiosVoteOffer | slot and vote-issuer-id | The server could immediately deliver this vote. The client should disconnect if the server had not already sent a LeiosAnnouncement for the same slot (rather than block, for the other messages). |
| Client→ | LinearLeiosBlockId | slot and hash | The server must deliver this block. The server disconnects if it doesn't have it. |
| Client→ | LeiosBlockTxsId | slot, hash, and map from 16-bit index to 64-bit bitmap | The server must deliver these txs from this Leios block. The server disconnects if it doesn't have the block or is missing any of its txs. The given bitmap identifies which of 64 contiguous txs are requested, and the offset of the tx corresponding to the bitmap's first bit is 64 times the given index. |
| Client→ | LinearLeiosVoteId | slot and vote-issuer-id | The server must deliver this vote. The server disconnects if it doesn't have it. |
| ←Server | LinearLeiosBlockDelivery | Leios block | The block from an earlier LinearLeiosBlockId. |
| ←Server | LeiosBlockTxsDelivery | slot, hash, map from 16-bit index to sequences of txs | A subset of the txs from an earlier LeiosBlockTxsId. Note that this map's keys are a non-empty subset of the request's map's keys. A server is allowed to send multiple LeiosBlockTxsDelivery in reply to a single LeiosBlockTxsId. |
| ←Server | LinearLeiosVoteDelivery | Leios vote | The vote from an earlier LinearLeiosVoteId. |
| Client→ | LinearLeiosStaleBlockRangeId | two slots and two hashes | The server must deliver all LLBs that are certified within this range of the identified Ranking Blocks. The client should disconnect if the server doesn't send the block in the same order as the chain, contrary to FreshestFirstDelivery. If the requested range is not on the server's current selection, it should disconnect. If the server doesn't have all of the LLBs, it should disconnect. The client is advised to not send this message while the wall clock is still within any of the requested LLB's L_recover window; LinearLeiosBlockId is more suitable for such blocks. |

**Age bounds for lightweight servers**.
Some information (eg LinearLeiosVoteOffer) cannot be sent before other information (ie LinearLeiosAnnouncement) has been sent.
This is the only constraint preventing the server from sending an unbounded amount of nonsensical offers to the client.
Unfortunately, it also requires the server to separately maintain commensurate state for each client.
It is not uncommon for a server to have hundreds of downstream peers, so servers can only afford to maintain lightweight state separately per peer.
This per-client state of Leios server is sufficiently bounded because servers can safely forget about LLBs that are older than L_recover, and votes can be forgotten even sooner, after L_vote.
L_recover will never exceed a few minutes, so the server will never be responsible for a large number LLBs simultaneously.

**Bundling txs**.
Only LeiosBlockTxsOffer, LeiosBlockTxsId, and LeiosBlockTxsDelivery explicitly bundle requests for multiple objects (ie txs in a Leios block).
This bundling is necessary, because an adversarial Leios block could cause honest nodes to request thousands of txs simultaneously, and thousands of individual request-response pairs is an intolerable amount of overhead.
This bundling is also mostly harmless, because---without a design for streaming each LLB---a node cannot send LeiosBlockTxsOffer to its downstream peers until it has all of the Leios block's txs, so the fact that the first tx in a bundle would have arrived much sooner than the last if they weren't bundled is not particularly relevant to diffusion.
Moreover, this bundling is compact, because the Leios design inherently enables a compact scheme for referring to multiple txs: by their location within a particular Leios block.

**Bundling votes and/or blocks**.
All other rows in the table refer only to individual objects, in part because no compact addressing scheme as obvious for blocks or votes as it is for txs.
Even so, simply concatenating multiple requests and/or responses within a single mini protocol message would eliminate some overhead.
In particular, there will also be hundreds of votes in-flight at a time, so some bundling might be appropriate there too.
Too much bundling, however, would be harmful for votes, since the first vote within a bundled response might be enough to establish a quorum, and wouldn't be able to arrive sooner than the last vote in a bundle.
The ideal degree of bundling for small objects like votes or even mostly-empty Leios blocks is a trade-off to be balanced heuristically.
Thus, the mini protocol messages will accommodate it for any object without requiring it.

A bundled request does naturally create the opportunity for multiple messages to cooperatively reply to the same request, which is somewhat sophisticated.
But that possibility is already introduced by LeiosBlockTxsId, so allowing it for other objects too is merely marginal additional complexity.

**Overlapping tx requests and lightweight servers**.
Two different LeiosBlockTxsId requests might overlap, even for different blocks, since normal circumstances imply the tx references within contemporary LLBs will overlap.
A client could avoid this by excluding the overlap from its second request (even if it's pipelining requests).
However, the server could only (perfectly) force the client to do so if the server was already maintaining enough state that it could simply itself skip over the redundant parts of the second request.
If server-side reordering (discussed below) is not allowed, then the server must either maintain the state or unknowingly waste bandwidth when requests overlap.

If server-side reordering is allowed, then the client cannot necessarily avoid redundant requests, since it cannot be sure which request will be handled first.
With server-side reordering, the client could only rely on the server---as the ultimate decider of reply order---to eliminate the redundancy in its deliveries.
Thus, with or without server-side reordering, the server must maintain some state to eliminate redundancy in responses.
Requests for blocks and votes cannot overlap in any way, so this state is only needed for txs.

The necessary state can also be bounded, since the server doesn't have to track/avoid redundancy forever, merely over whatever duration server-side reordering might force the honest client to send redundant requests.
It seems sufficient to limit it by the number of LLBs, rather than a time-based duration; it's unlikely a server will make large requests from more than, say, three LLBs at once, due to the size of the corresponding receive-buffer commitment.
So the server would not be expected to eliminate redundancy from among more than three LeiosBlockTxsDelivery at once.
The size limit on a single LLB prevents one from ever referring to more than ~6250 txs, so the server would only need to track at most ~20000 txs at once per client to avoid overlap even across requests spanning three full LLBs even if they mostly do not overlap.
(TODO should the server enforce that the client never has outstanding requests for more than 20000 unique txs at once?)
Moreover, the identifiers the server uses when tracking txs can be subjective, so the server's centralized internal state can maintain an injective mapping from txs in currently-young LLBs to arbitrary 32-bit integers.
Thus, even with a relatively naive implementation, this state requires at most 20,000 * 4 = 80,000 bytes per client (there's no need for sharing/persistence, so GC overhead can be avoided), ie 8 megabytes per 100 downstream nodes.
The boundedness prevents a guarantee that the server will eliminate all redundancy among every set of pipelined requests, but the scheme almost always eliminates redundancy among requests from honest nodes under normal circumstances.

### Iteration 1

The following mini protocol is a useful starting point.
It is superficially plausible for conveying the rows of the IER table, but has some major problems.
They will be explained below in order to motivate and derive the actual mini protocol proposal.

If mini protocols are unfamiliar, see the Chapter 2 Multiplexing mini-protocols and Chapter 3 Mini Protocol of the `ouroboros-network`'s [Ouroboros Network Specification PDF](https://ouroboros-network.cardano.intersectmbo.org/pdfs/network-spec/network-spec.pdf).
A brief summary is that a mini protocol is a state machine that two nodes cooperatively navigate; each node only sends a message when it has _agency_, and at most one node has agency in any state
The agencies are indicated in this document as gold or cyan.

```mermaid
---
title: LeiosIteration1
---
graph LR
   style StIdle color:gold;
   style StNotification color:cyan;
   style StBlock color:cyan;
   style StBlockTx color:cyan;
   style StVote color:cyan;

   Note[*Legend*. Interpret the bold arrow as a right-to-left arrow. That's unfortunately the best workaround for Mermaid's limited layout.]

   StNotification ---|MsgLeiosNextNotificationRequest| StIdle
   linkStyle 0 stroke-width:8;

   StNotification -->|MsgLeiosAnnouncement| StIdle
   StNotification -->|MsgLeiosBlockOffer| StIdle
   StNotification -->|MsgLeiosBlockTxsOffer| StIdle
   StNotification -->|MsgLeiosVoteOffer| StIdle

   StIdle -->|MsgLeiosBlockRequest| StBlock -->|MsgLeiosBlock| StIdle
   StIdle -->|MsgLeiosBlockTxsRequest| StBlockTx -->|MsgLeiosBlockTxs| StIdle
   StIdle -->|MsgLeiosVoteRequest| StVote -->|MsgLeiosVote| StIdle
   StIdle -->|MsgDone| StDone
```

The above mini protocol lacks the following desired properties.

- **Decoupled requests**.
  The foremost problem is that this node cannot have an outstanding request for new notifications and an outstanding request for some specific offered thing at the same time.
  The node has to choose whether to request a new notification or a new delivery, while it should ideally be able to do both simultaneously.
- **Reordering**.
  This monolothic mini protocol forces replies to be sent in the same order as their responses, since mini protocols have a lock-step semantics.
  The FreshestFirstDelivery scheme, however, naturally implies that a server should usually instead reply to the youngest of the outstanding requests.
    - In the basic interpretation of a mini protocol, the client cannot even send multiple outstanding requests.
    - _Mini protocol pipelining_ already allows exactly that, but today's implementation does not also allow the server to react to subsequent messages before it's done responding to the oldest outstanding message.
    - It seems plausible to somehow add that capability to the `ouroboros-network` infrastructure (eg the server, when it unblocks, receives the latest accumulation of client requests instead of the merely the first of them); see a further discussion below.
- **Bundling**.
  LeiosIteration1 does not permit any bundling of blocks or votes.
- **Many replies per single request**.
  LeiosIteration1 does not allow multiple MsgLeiosBlockTxs to satisfy a single (large) MsgLeiosBlockTxsRequest.
  This "unbundling" of replies isn't inherently required by Leios---and perhaps should be the responsibility of the client instead of the server---but it might be useful for other reasons, discussed below.
- **Minimized structure**.
  Finally, the mini protocol itself is replicating messages for different object (txs, votes, blocks) for no reason.
  All of those different message types can be combined into one message that carries a tagged union of some rows of the IER table.
  This makes the structure of the mini protocol simpler and its actual responsibilities/consequences clearer, with the superficial downside of hiding some of the recognizable Leios details behind an indirection.
  (TODO is this actually somewhat counterproductive---would we instead prefer "flat" CDDL?)

### Iteration 2: Decoupled Requests and Minimized Structure (Part 1 of 2)

Decoupled requests could be achieved by simply splitting the above mini protocol into its left and right halves.
Simultaneously, the mini protocol structure can be minimized by combining the four replies into a `MsgLeiosNotification` that carries a tagged union.
The right half can't be similarly collapsed, since the requests target distinct states.

```mermaid
---
title: LeiosIteration2A
---
graph LR
   style StIdle color:gold;
   style StBusy color:cyan;

   StIdle -->|MsgLeiosNextNotificationRequest| StBusy -->|MsgLeiosNotification| StIdle

   StIdle -->|MsgDone| StDone
```

```mermaid
---
title: LeiosIteration2B
---
graph LR
   style StIdle color:gold;
   style StBlock color:cyan;
   style StBlockTx color:cyan;
   style StVote color:cyan;

   StIdle -->|MsgLeiosBlockRequest| StBlock -->|MsgLeiosBlock| StIdle
   StIdle -->|MsgLeiosBlockTxRequest| StBlockTx -->|MsgLeiosBlockTx| StIdle
   StIdle -->|MsgLeiosVoteRequest| StVote -->|MsgLeiosVote| StIdle

   StIdle -->|MsgDone| StDone
```

### Iteration 3: Many replies to one request

A server might have good reason to send multiple MsgLeiosBlockTx messages in response to a large MsgLeiosBlockTxRequest.
The following demonstrates how a mini protocol would express the possibility of many replies to a single request (eg BlockFetch already does), for both MsgLeiosNextNotificationRequest and MsgLeiosBlockTxsRequest.
If other requests could be bundled (eg votes), then this same transformation should be repeated for them.

```mermaid
---
title: LeiosIteration3A
---
graph LR
   style StIdle color:gold;
   style StBusy color:cyan;

   StIdle -->|MsgLeiosNotificationsRequest| StBusy -->|MsgLeiosNotification| StBusy -->|MsgLeiosNotificationsDone| StIdle

   StIdle -->|MsgDone| StDone
```

```mermaid
---
title: LeiosIteration3B
---
graph LR
   style StIdle color:gold;
   style StBlock color:cyan;
   style StBlockTxs color:cyan;
   style StVote color:cyan;

   StIdle -->|MsgLeiosBlockRequest| StBlock -->|MsgLeiosBlock| StIdle
   StIdle -->|MsgLeiosBlockTxsRequest| StBlockTxs -->|MsgLeiosSomeBlockTxs| StBlockTxs -->|MsgLeiosBlockTxsDone| StIdle
   StIdle -->|MsgLeiosVoteRequest| StVote -->|MsgLeiosVote| StIdle

   StIdle -->|MsgDone| StDone
```

### Iterations 4 and 5: Reordering and Minimized Structure (Part 2 of 2)

Strictly speaking, all of the above mini protocols already sometimes permit the server to send replies out of order.
For example, if the client pipelined MsgLeiosVoteRequest, MsgLeiosBlockRequest, and MsgLeiosBlockTxsRequest in that order, the server could only reply in the same order.
If it instead pipelined MsgLeiosBlockRequest, MsgLeiosVoteRequest, MsgLeiosBlockRequest messages (identifying two different blocks), then the mini protocol structure itself does not force the server to send the two MsgLeiosBlock messages in the same order as they were requested.
But it does have to send a block, a vote, and then a block.

Conventionally, the client logic adds constraints beyond the mini protocol structure in order to require that replies come in the exact same order as the requests.
If server-side reordering were desired, then the client would relax its constraints according to whatever possible prioritization the mini protocol was reorganized to allow.

To enable as much reordering as possible, LeiosIteration4B collapses the busy states into a single busy state.
The server can therefore reorder requests regardless of whether they are for blocks, txs, or votes.
Now that the states aren't distinguished, the messages can also be collapsed, just as in LeiosIteration2A.

Let LeiosIteration4A = LeiosIteration3A.

```mermaid
---
title: LeiosIteration4B
---
graph LR
   style StIdle color:gold;
   style StAtomic color:cyan;
   style StComposite color:cyan;

   StIdle -->|MsgLeiosAtomicRequest| StAtomic -->|MsgLeiosAtomicReply| StIdle
   StIdle -->|MsgLeiosCompositeRequest| StComposite -->|MsgLeiosPartialReply| StComposite -->|MsgLeiosCompositeDone| StIdle

   StIdle -->|MsgDone| StDone
```

For example, a LeiosBlockTxsId is necessarily a MsgLeiosCompositeRequest.
But a MsgLeiosCompositeRequest might carry more than one LeiosBlockTxsId, even interleaved with multiple LinearLeiosBlockId and LinearLeiosVoteId requests.

If the client is already allowing the server to reorder requests for different kinds of object, then it seems likely the server is also allowed to interleave partial replies with atomic replies.

Let LeiosIteration5A = LeiosIteration3A.

```mermaid
---
title: LeiosIteration5B
---
graph LR
   style StIdle color:gold;
   style StBusy color:cyan;

   StIdle -->|MsgLeiosRequest| StBusy -->|MsgLeiosReply| StIdle
   StBusy -->|MsgLeiosPartialReply| StBusy

   StIdle -->|MsgDone| StDone
```

Now a MsgLeiosRequest can simply carry any number of LeiosBlockTxsId, LinearLeiosBlockId, and LinearLeiosVoteId requests.
And so a MsgLeiosPartialReply could carry any number of LinearLeiosBlockDelivery, LeiosBlockTxsDelivery, and LinearLeiosVoteDelivery replies.

### Discussion

LeiosIteration5A and LeiosIteration5B address every problem identified with LeiosIteration1, assuming that the client pipelines its requests and that the server is able to reorder those requests when actual timings and the priorization rules allow.

Unfortunately, server-side reordering is not permitted by the existing `ouroboros-network` infrastructure for specifying server behavior.
Today's server is unaware of request pipelining; it's only ever aware of the first of however many messages have arrived but not yet been processed.
The existing infrastructure is completely sufficient for latency hiding, which has been the only goal of mini protocol pipelining so far.
Reordering pipelined requests (when possible) is a new desideratum, due to the FreshestFirstDelivery requirement within the Leios specification.

The missing feature for servers could be implemented in `ouroboros-network`, but the best interface is not already clear.
Once that feature is available, LeiosIteration5A and LeiosIteration5B would be sufficient for Leios with a defensibly-granular interpretation of FreshestFirstDelivery.
See section XXX for what an even more granular interpretation of FreshestFirstDelivery would require, such as message preemption.

### Iteration 6: extremely generic alternative

Especially for a first implementation, it's plausible that, instead, a coarser interpretation of FreshestFirstDelivery is acceptable.
In particular, client-side prioritization might suffice even without opportunistic server-side reordering.
The extent of the harm depends on how many requests have already been pipelined before the client learns of a fresher Leios block (which is ideally proportional to the [bandwidth-delay product](https://en.wikipedia.org/wiki/Bandwidth-delay_product) _most of the time_).
Opportunistic server-side reordering, on the other hand, is desirable specifically because it simply always respects FreshestFirstDelivery (as much as it can without preemption), regardless of how many requests have been pipelined.

If the server-side reordering is not required, then the states collapsed in Iteration 3 above could be uncollapsed.
That resulting mini protocol is not explicitly specified here, because server-side reordering is presumed to be considered worth the relatively small amount of work to enable it.
However, it's nothing more than reintroducing to LeiosIteration5B separate busy states per kind of object and restricting each state's incoming and outgoing messages to the corresponding rows of the IER table.

(TODO how does the Rust simulator relate to this question?
If I recall correctly, it's "perfectly" interleaving the reponses, isn't it?
Which is most comparable to not reordering?)

If server-side reordering is required but Leios for some reason must not be blocked on the corresponding changes to `ouroboros-network`, then there is another mini protocol design that addresses all of problems identified with LeiosIteration1 above, including reordering.
It's essentially the other possible split from Iteration 2: instead of separating notifications (LeiosIteration2A) from deliverables (LeiosIterationAB), the alternative split separates all requests from responses.
Once requests and responses are decoupled, the two server threads would simply share the state of the set of outstanding requests as sole producer and sole consumer.

```mermaid
---
title: LeiosRequest
---
graph LR
   style StIdle color:gold;

   StIdle -->|MsgLeiosDoneRequest| StDone

   StIdle -->|MsgLeiosRequest| StIdle
```

```mermaid
---
title: LeiosReply
---
graph LR
   style StInit color:gold;
   style StIdle color:cyan;

   StInit -->|MsgLeiosInit| StIdle

   StIdle -->|MsgLeiosDone| StDone

   StIdle -->|MsgLeiosReply| StIdle
```

This final mini protocol pair is extremely generic.
All of the Leios details are hidden in the tagged union of (lists of) rows from the IER table, carried by MsgLeiosRequest and MsgLeiosReply.

- There are no longer different messages for blocks, transactions, and votes; messages merely carry a sum type instead (see below).
  The mini protocol itself need not differentiate.

- This split naturally relaxes the one reply per request restriction.
    - However, it even goes beyond many-replies per request; it could allow a single reply to resolve multiple requests.
      That is not obviously harmful, but it is also not obviously beneficial.
      For the sake of simplicity, that possibility is therefore forbidden: every Leios reply must uniquely identify a single Leios request, and it must not contain any content not identified by that request.
      This restriction will be invoked below.
- Both of these protocols are particularly unusual in that only one of the peers sends messages.
  That incurs at least the following immediate disadvantages.
    - The medium for back pressure is still present, but much less explicit than it is for existing mini protocols.
        - LeiosReply must only send messages that were requested.
          Thus, whenever the client becomes overwhelmed, they should temporarily stop sending messages via LeiosRequest.
        - LeiosRequest must not send another message if it has already sent, say, 10000 bytes of requests or, say, 1000 individual requests (whichever comes first) that the peer has not yet fully replied to via LeiosReply.
          These exact limits would be a consequence of the exact negotiated version of the mini protocol.
    - The timeouts for these mini protocols cannot be managed via the existing `ouroboros-network` infrastructure.
        - Existing timeouts begin when the mini protocol enters some state, but these mini protocols spend all of their time in a single state.
        - Moreover, the duration of a timeout was determined by the specific state, but that distinction doesn't exist for these mini protocols.
        - Instead, the client's centralized decision logic that controls LeiosRequests and reacts to LeiosReply will need to explicitly manage timeouts, and do so in a way that tolerates the server reordering according to FreshestFirstDelivery, for example.

### Detailed Message Semantics

The MsgLeoisRequest and MsgLeiosReply mini protocol messages carry LeiosRequestPayload and LeiosReplyPayload, respectively.
These data types are specified in Haskell syntax but are little more than tagged unions of rows from the IER table.

```haskell
data LeiosRequestPayload
  = LeiosNotificationBytes RequestNo Word16
  | LeiosDeliverableIds RequestNo (NonEmptyList LeiosDeliverableId)

data LeiosReplyPayload
  = LeiosNotifications RequestNo CompletionFlag (NonEmptyList LeiosNotification)
  | LeiosDeliveries RequestNo CompletionFlag (List LeiosDelivery)

--

type RequestNo = Word64
type CompletionFlag = Bool

type Index16 = Word16
type Bitmap64 = Word64
type SlotNo = Word64

type LeiosPoint = (SlotNo, LeiosBlockHash)

data LeiosNotification
  = LinearLeiosAnnouncement RankingBlockHeader
  | LinearLeiosBlockOffer LeiosPoint
  | LeiosBlockTxsOffer LeiosPoint
  | LinearLeiosVoteOffer SlotNo VoteIssuer

data LeiosDeliverableId
  = LinearLeiosBlockId LeiosPoint
  | LeiosBlockTxsId LeiosPoint (NonEmptyMap Index16 NonEmptyBitmap64)
  | LinearLeiosVoteId SlotNo VoteIssuer
  | LinearLeiosStaleBlockRangeId LeiosPoint LeiosPoint

data LeiosDeliverable
  = LinearLeiosBlockDelivery LinearLeiosBlock
  | LeiosBlockTxsDelivery LeiosPoint (NonEmptyMap Index16 (List Tx))
  | LinearLeiosVoteDelivery LinearLeiosVote
```

Some names start with merely Leios instead of LinearLeios, because those names will also exist as-is for future Leios variants.
(TODO this is the only sentence we'd need to remove if we never want to mention LinearLeios within the CIP; find-and-replace would handle everything else.)

Additional message details, beyond the IER table.

- The RequestNo of the first request must be zero.
  The RequestNo of the subsequent request must be one greater, and so on.
  If it isn't, the server should disconnect.
  (If every EB incurred 10000 requests between two specific peers, their connection would have to last more than a billion years to exhaust Word64, assuming an average of one per 20 seconds.)
- Every MsgLeiosReply identifies the corresponding MsgLeiosRequest by its RequestNo.
  If there is no such outstanding request, the client should disconnect.
- The CompletionFlag indicates whether the server considers this message to completely resolve the corresponding request.
  This flag is redundant, but it will at least be useful for troubleshooting related bugs.
  If the client disagrees with a CompletionFlag, it should disconnect.
  The flag should be set on the first notification whose size includes the last byte of a LeiosNotificationBytes request.
  That same notification might include the first byte of the next LeiosNotificationsBytes request, but it should never also include the last byte of that second request.
  The flag should also be set on the delivery that includes the last of the objects identified by some LeiosDeliverableIds request.
  If it does, the client should disconnect, because the lower bound on MaxNotificationSize prevents the server from being forced to send such a message.
- If the argument of a LeiosNotificationBytes request is less than some MaxNotificationSize constant determined by the negotiated mini protocol version, the server should disconnect.
  Every MaxNotificationSize constant must accommodate at least any single LeiosNotification carrying the biggest argument it can, so MaxNotificationSize must be no less than the maximum size of a RankingBlockHeader.
- When FreshestFirstDelivery justifies the client sending two overlapping requests (eg if a younger LLB refers to the same txs as an already requested older LLB), the server might reply in-order or out-of-order, depending on how timings resolve.
  Whichever reply is sent second should exclude the content that was already included in the first reply, in order to not waste bandwidth (recall that it should be common for contemporary LLBs to share most txs).
  In an extreme case, this might require a LeiosDeliveries message to carry an empty list.
  (TODO for extra explicitness, would we also want to send a LeiosBlockTxsDelivery with an empty map?)

TODO discuss fetching "missing" LLBs, eg after L_recover, etc.
Maybe LinearLeiosStaleBlockRangeId covers it?
Would its disconnect-if-not-on-selection rule be too severe for this use case?

TODO age limits for notifications?
Maybe a generous, say 5 minutes?
Does pull-based LeiosNotificationBytes mean adversarially-old notifications would be harmless even without an explicit rule against them?

TODO copy over the OpCertIssueNumber discussion

### Timeouts

The ChainSync and TxSubmission mini protocols enforce a 10 second timeout when the peer must not be blocked.
The BlockFetch mini protocol enforces a generous 60 second timeout when the peer must not be blocked.
60 seconds would be intolerable as an average, which is why the Ouroboros Genesis design introduces additional, more aggressive, adaptive timeouts for a syncing node.
However, for caught-up nodes, mini protocols' timeouts aren't intended to ensure an average responsiveness; it's the churning of peers based on their recent performance that prevents terrible performance over longer periods, under the assumption that at least some peers are honest and healthy.
Mini protocols' timeouts are instead merely used to stop wasting resources on a clearly defunct peer.
(TODO this is my inference---I haven't found an explanation in any written document.)

A LeiosNotificationBytes request should not incur any timeout; there's no absolute limit on the duration until the next upstream Leios event (eg SPOs could choose to stop issuing LLBs alongside their RBs).
LeiosDeliverableIds are only submitted when the peer is not blocked and could be much larger than ChainSync and TxSubmission messages, and so a 60 second timeout seems comparable, copied from BlockFetch.

For a pipelined mini protocol message, the existing `ouroboros-network` infrastructure begins the timeout as soon as the request is sent.
That simple rule would be incorrect for LeiosRequest-LeiosReply due to server-side reordering and/or partial responses.
Both of those phenomena mean that the nth message sent won't necessarily be resolved by the nth message to arrive.

Instead, LeiosReply should throw a timeout exception if it ever waits more than 60 seconds for the next message it was expecting.
More concretely, a 60 second timeout should start whenever LeiosRequest sends a LeiosDeliverables message while there were no outstanding LeiosDeliverableIds requests.
That timeout is discharged when LeiosReply receives any LeiosDeliverables message.
If there are still outstanding LeiosDeliverableIds requests after LeiosReply receives a LeiosDeliverables message, LeiosReply should reset the timeout to another 60 seconds.

Remarks.

- If a request takes more than a few seconds to be resolved (perhaps as an expected consequence of server-side reordering!), the node might be well justified to also send the same request to another peer, in order to fulfill it sooner, regardless of whether or not the first peer exceeds the generous mini protocol timeout.
- For LeiosIteration5A and LeiosIteration5B instead of LeiosRequest and LeiosReply, the timeouts would be 10 seconds and 60 seconds respectively, and could be handled normally by the `ouroboros-network` infrastructure, assuming its enhancement for server-side reordering include some clever timeout handling.

TODO is this overspecified?
Is the first paragraph actually sufficient by itself?
It's OK if different clients enforce different timeouts---the honest server will always be trying its best, regardless.

### Concise Data Definition Language (CDDL)

TODO write out the full CDDL for these messages

### Head-of-Line Blocking and Sharing Bandwidth with Praos

There are two more risks that these mini protocols do not inherently address: head-of-line blocking in LeiosReply and limiting how much bandwidth the Praos mini protocols can use.

The existing `ouroboros-network` infrastructure provides some simple mitigation for head-of-line blocking, but the only way to enable it is to split the LeiosReply mini protocol into two copies of itself, so that two concurrent deliveries could be interleaved by the `ouroboros-network` mux.
If one copy of LeiosReply was reserved for messages that were both small and urgent, then the server would be able to provide an urgent notification such as LinearLeiosAnnouncement even if it were already sending a multi-megabyte LeiosBlockTxsDelivery.
That approach might suffice, at least for an initial implementation.
However, duplicating LeiosReply has two drawbacks.

- It's an artifical workaround that would explicitly manifest in the concrete interface between communicating nodes.
  Every node would need to accommodate it, and when the workaround is eventually replaced by something preferable (eg perhaps the mux could allow a single mini protocol to interleave its own messages), the mini protocol specification would need to be updated accordingly, despite the LeiosRequest-LeiosReply pair _already_ accommodating out-of-order replies.
- The existing mux logic is flat, so adding a second Leios mini protocol instance (it's not a third, since LeiosRequest only sends messages in the opposite direction) means that Leios would sometimes consume a larger share of the bandwidth that's split among all sending mini protocols.
  This is explicitly undesirable, since Praos messages should always be prioritized over Leios messages---the fundamental restriction is that Leios must not disrupt Praos.
  (A more expressive configuration for the `ouroboros-network` mux would likely also help here; for example, biased sampling of active mini protocols.)

Ideally, the Leios mini protocols would pause completely while ChainSync or BlockFetch are sending.
The `ouroboros-network` mux cannot express that today, but restricting Leios to use at most one "share" of the bandwidth at a time seems tolerable until the `ouroboros-network` mux does somehow allow intentionally-unfair sharing.

There is another way to mitigate head-of-line blocking without duplicating LeiosReply.
The client should avoid ever sending a request that incurs a large MsgLeiosReply.
Because of the aforementioned restriction that the server must not combine multiple requests into a single message, this allows the client to ensure any head-of-line blocking is insignificant.
For example, if the client tried to never send a single request that incurred more than 100,000 bytes, then---with modern bandwidths---the worst-case head-of-line blocking would be on the order of ten milliseconds.
In the proposed Linear Leios design, the only object that is atomic and potentially larger than that is LLBs, but at most by a factor of three.
(There might be other benefits to explicitly decomposing LLBs, such as being able to stream them across the network.
Remarkably, the proposed mini protocols could accommodate that by merely adding one summand to LeiosDeliverable, since the sub-blocks should have unique hashes.)

TODO this assumes the server `Peer`'s `Yield` would block instead of pushing the total enqueued past 100,000 bytes?

There is also a way to explicitly prioritize Praos without requiring any changes to `ouroboros-network`, but it seems radical enough to be not be a preferred option, at least for the first Leios deployment.
A pair of mini protocols Request and Reply could handle all communication between two peers, both Praos and Leios.
BlockFetch is simply deliveries, while ChainSync and TxSubmission are mixes of notifications and deliveries.
(KeepAlive is also merely notifications.)
The simplicity and convenience of timeouts for the existing mini protocols---which are crucial for KeepAlive and ChainSync, in particular---would be the primary loss, beyond the intuitive distinction being less present in the architecture.
Once Praos and Leios are within the same Reply mini protocol, both the client and server could arbitrarily prioritize Praos requests over Leios requests whenever arrival time permits.

### Linear Leios for Syncing Nodes

There are two kinds of syncing node, with Ouroboros Genesis and without (eg via a trusted relay or via a semi-centralized "bootstrap peer").

With Ouroboros Genesis, LLBs that are certified on chain should be fetched from the same peer that Devoted BlockFetch is fetching its blocks from.
It would be sufficient to send LinearLeiosBlockId requests to that peer via LeiosRequest when the headers it has sent via ChainSync imply those LLBs are certified on the chain it's serving.
The only time that node wouldn't be able to immediately serve the LLB is if the wall clock is still within that LLB's L_recover window.
If the node is actually a healthy caught-up upstream, that should be rare and ephemeral.
If it does happen severely enough to starve the syncing node, then LeiosRequest should rotate the Dynamo just like Devoted BlockFetch would have.
No other part of Ouroboros Genesis would need to change for the proposed Leios protocol.

When the node is syncing without Ouroboros Genesis, LeiosRequest would do the same except it does not need to monitor for and react to starvation a la Devoted BlockFetch.

For blocks older than L_recover, the syncing node could eliminate some overhead by sending LinearLeiosStaleBlockRangeId instead of LinearLeiosBlockId.
TODO should the server enforce that time limit?
TODO will the certificate density be high enough that this compactly bundled request is worthwhile?

With or without Ouroboros Genesis, the syncing node should not send LeiosNotificationBytes until it is nearly caught-up.
If sent too soon, the server might reply with headers that the syncing node's ledger state is incapable of validating at all.
Conversely, the syncing node does not need to wait until it's _completely_ caught-up before it starts sending LeiosNotificationBytes.
For example, starting to send LeiosNotificationBytes requests once the syncing node's ledger state is within a couple hours of the wall clock would suffice.
Even if the syncing node does wait until it's completely caught-up to the chain, a few minutes later it will have received all relevant Leios notifications.
