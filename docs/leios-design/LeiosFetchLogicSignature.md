I'll migrate this into the very large README.md document before merging, after review.
I'll need to elaborate the text from presentation slide to prose document before then.

# Signature of the Decision Logic Component

## Slide 1

- Incoming event stream (all annotated with non-descending timestamp T, some annotated with latest TCP_INFO)
    - GainPeer: start utilizing peer P
    - PraosRequest: some Praos mini protocol sent requests for N bytes to peer P, expecting urgent replies
    - PraosReply: some Praos mini protocol received N bytes from peer P, discharging M bytes of PraosRequest
    - LeiosNotification: either MsgOfferEbBody or MsgOfferEbClosure (includes all the bytes)
    - SocketRead: LeiosFetch received N bytes from peer P
    - LeiosReply: latest SocketRead (from peer P) finished a MsgEbBody or MsgEbTxs (includes all the bytes)
    - LosePeer: stop utilizing peer P
    - AlarmFired: the alarm fired
- Outgoing action stream
    - Send MsgRequestEbBody to peer P for given EB hash
    - Send MsgRequestEbTxs to peer P for given EB hash and some offsets
    - Send MsgTryCancels to peer P for some message identifiers, e.g. uint64s
    - Disconnect from peer P with given degree of prejudice, if any
    - Set the alarm for given deadline T_{deadline}

## Slide 2

- PraosRequest and PraosReply let the LeiosFetch logic monitor the higher-priority Praos traffic
- SocketRead and PraosReply lets the LeiosFetch logic monitor each peer's apparent latency/bandwidth/etc
    - However, TCP noise in the timestamps may make that analysis quite difficult

## Slide 3

- Simplifying assumptions
    - Assume onset of slot 0 has a universally known timestamp T_0 < now
    - Every slot’s duration is 1 s
    - Assume every MsgOfferEbBody has authentic hash and slot
    - There’s an injective function from MsgOfferEbBody hashes to valid elections
    - At most 10,000 MsgOfferEbBody messages will simultaneously have slots less than 36 hr old
    - Killing a peer always eventually incurs LosePeer and eventually a GainPeer too
    - ~25 peers (this logic is only concerned with upstream peers)
    - The socket is shared only with Praos mini protocols; they have higher priority than Leios
- Complicating realities
    - Timestamps on BlockFetchReply/SocketRead are surprisingly noisy—opaque kernel details
    - Internal state of this decision logic and the sockets’ buffers can’t occupy “too much” memory
    - Will eventually need to handle/share socket with Leios/Peras votes too, but one step at a time
