## (Classic) Leios Implementation

This implementation covers Short Leios and "Full" Leios variants.
It's used for the following values of `leios-variant`:
 - `short`
 - `full`
 - `full-with-tx-references`

## Mempool(s)

This implementation has two mempools: one for Praos, and one for Leios. The Praos mempool is used when building ranking blocks, and the Leios mempool is used when building input or endorser blocks.

When a node first receives a transaction, it will check whether that transaction conflicts with something already in the Leios and Praos mempools; it adds the transaction to whichever mempool does not conflict. When a node sees an IB or EB with a transaction, it removes that transaction from the Leios mempool. When a node sees an RB which references a transaction, it removes that transaction from both Praos and Leios mempools.

When the `leios-mempool-aggressive-pruning` option is on, nodes will take TX conflicts into account when removing TXs from their Leios mempool. When an input or endorser block contains a transaction which consumes an input, any other transactions which consume that input will be filtered from the mempool.

Mempools do not have a maximum size.

## Sampling from mempools

When building a ranking block, the node will select transactions from its Praos mempool. This can be disabled by setting `praos-fallback-enabled` to `false`.

When building an input block, the node will select transactions from its Leios mempool. Input blocks contain an "rb reference"; and the ledger state used by that IB is computed from that RB. The node will not select transactions which conflict with any transactions already in the ledger state.

## Input Blocks

Input blocks are produced on a schedule. They contain transactions sampled from the Leios mempool.

Input blocks belong to a pipeline, based on the slot they were produced for. Input blocks for a pipeline could theoretically be produced at any slot during that pipeline, but in practice we always configure them to be produced in the first slot. A single node can produce multiple input blocks in one pipeline.

Input blocks are disseminated through the network using a Freshest First strategy. Input block headers (which are small) are distributed throughout the network automatically; nodes will download IB headers as soon as they are announced, and track the header arrival times.

When a peer announces that it has an IB body, the node will add that IB to a queue of IBs to download from that peer. The queue is a priority queue, ordered by arrival timestamp. Once a node has downloaded the header to an IB, it will add that IB to a queue of IBs to fetch; that queue is a priority queue ordered by arrival time of the IB header. The node will download one IB body from each peer at a time, and will download each body from at most one peer. 

## Endorser Blocks

Endorser blocks are produced on a schedule. They contain references to input blocks, as well as (in Full Leios) older endorser blocks. Endorser blocks belong to a pipeline based on the slot they were produced for; they will always be produced in the first slot of that pipeline. A single node will only ever produce a single endorser block in one pipeline.

The contents of endorser blocks are deterministic. When a node produces an endorser block, it includes references to all input blocks produced in the same pipeline. In Full Leios, it also references endorser blocks from older pipelines (though skipping the two most recent pipelines). When choosing an endorser block from a pipeline, a node only considers EBs which
 * Have received enough votes
 * Contain only IBs which the node has already seen
If more than one EB in a single pipeline meets these requirements, we use for tiebreakers
 1. Whichever EB references the most transactions through IBs
 2. Whichever EB has the most votes

## Voting for Endorser Blocks

The Rust simulation propagates votes through "vote bundles", which are not described in the Leios spec. A vote bundle is a message containing all votes produced by a single node in a single pipeline. At the beginning of each pipeline, nodes run VRF lotteries to determine how many votes they can produce in that pipeline. Nodes are allowed to use the "same" VRF lottery win to vote for multiple EBs; if a node has 3 EBs to vote for in a given slot and the right to produce 4 votes, it will produce a vote bundle with 4 votes for each EB.

A node will only vote for an EB if it satisfies all of the following rules:
 * For every IB referenced by the EB,
   * The node has downloaded and validated that IB
   * That IB was not equivocated
   * The IB’s header was received "in time" according to equivocation rules
   * That IB was produced in the right pipeline
   * (For variants where the IB holds references to TXs instead of full TXs) the node has downloaded and validated every TX in the IB
 * If our variant is a "full" Leios,
   * For every EB referenced by the EB,
     * That referenced EB has received enough votes
     * That referenced EB belongs to a valid earlier pipeline
   * For every valid earlier pipeline with a certified EB
     * Our EB references a certified EB from that pipeline 

A node considers an EB to be "certified" as soon as that node has seen some threshold of votes for it.

## Ranking Blocks
A ranking block contains transactions, as well as an optional endorsement. The endorsement references a single EB which
 * Has enough votes to be "certified"
 * Is not older than a configurable max age
 * Is not from a pipeline already represented by the chain.
If more than one EB matches all of these criteria, we use for tiebreakers
 1. The age of the EB (older EBs take priority in Short Leios, newer EBs in Full Leios)
 2. The number of TXs in the EB
 3. The number of votes for the EB

## CPU model
|Task name in logs|Task name in code|When does it run|What happens when it completes|CPU cost
|---|---|---|---|---|
|`ValTX`|`TransactionValidated`|After a transaction has been received from a peer.|That TX is announced to other peers.|`tx-validation-cpu-time-ms`|
|`GenRB`|`RBBlockGenerated`|After a new ranking block has been generated.|That RB is announced to peers.|`rb-generation-cpu-time-ms` + `cert-generation-cpu-time-ms-constant` + `cert-generation-cpu-time-ms-per-node` for each node that voted for the endorsed EB|
|`ValRB`|`RBBlockValidated`|After a ranking block has been received.|That RB body is announced to peers and (potentially) accepted as the tip of the chain.|`rb-body-legacy-praos-payload-validation-cpu-time-ms-constant` + `rb-body-legacy-praos-payload-validation-cpu-time-ms-per-byte` for each byte of TX  + `cert-generation-cpu-time-ms-constant` + `cert-generation-cpu-time-ms-per-node` for each node that voted for the endorsed EB|
|`GenIB`|`IBBlockGenerated`|After a new IB has been generated.|That IB is announced to peers.|`ib-generation-cpu-time-ms`|
|`ValIH`|`IBHeaderValidated`|After an IB header has been received from a peer.|The IB header is announced to peers, and the body is queued for download.|`ib-head-validation-cpu-time-ms`|
|`ValIB`|`IBBlockValidated`|After an IB has been received from a peer.|The IB body is announced to peers, and the Leios mempool is updated.|`ib-body-validation-cpu-time-ms-constant` + `ib-body-validation-cpu-time-ms-per-byte` for each byte of TX|
|`GenEB`|`EBBlockGenerated`|After a new EB has been generated.|That EB is announced to peers.|`eb-generation-cpu-time-ms`|
|`ValEB`|`EBBlockValidated`|After an EB's body has been received from a peer.|That EB is announced to peers.|`eb-validation-cpu-time-ms`|
|`GenVote`|`VTBundleGenerated`|After a vote bundle has been generated.|That vote bundle is announced to peers.|`vote-generation-cpu-time-ms-constant` + `vote-generation-cpu-time-ms-per-ib` for each IB in the EB|
|`ValVote`|`VTBundleValidated`|After a vote bundle has been received from a peer.|The votes in that bundle are stored, and the bundle is propagated to peers.|`vote-validation-cpu-time-ms` for each EB voted for (in parallel)|
