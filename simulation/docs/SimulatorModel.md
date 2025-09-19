# Introduction

This work-in-progress document summarizes the structure and behaviors of the Haskell Leios simulator.
The desired level of detail is between the code itself and the various work-in-progress Leios specifications.

The Leios node is modeled as a set of threads that maintain shared state via the [stm](https://hackage.haskell.org/package/stm) library, as with the existing `ouroboros-network` and `ouroboros-consensus` implementation libraries.
This document will primarily describe those threads and the components of their shared state.

TODO also discuss the mini protocol multiplexing and TCP model

# Lifetime of an object

The objects within the simulator include Input Blocks (IBs), Endorser Blocks (EBs) (aka Endorsement Blocks, aka Endorse Blocks), Vote Bundles (VBs), and Ranking Blocks (RBs).
Certificates are not explicit; for example, a certificate's computational cost is instead associated with the containing RB.

Within a single simulated node, the lifetime of every such object follows a common sequence.

- *Generate*, the duration when the node is generating an object.
- *Receive*, the moment a node receives (the entirety of) an object from a peer.
  (It is often useful to consider a node to have received an object when it finished generating that object.)
- *Wait*, the duration when the node cannot yet validate an object (eg a known necessary input is missing).
- *Validate*, the duration when when node is computing whether the object is valid.
- *Diffuse*, the duration when the node is offering/sending the object to its peers.
- *Adopt*, the moment the node updates its state in response to the successful validation.
- *Prune*/*Forget*, the moment the node updates its state once the object is no longer necessary/relevant.

Only generation and validation consume modeled CPU, and nothing consumes any modeled RAM/disk capacity/bandwidth.

Modeled CPU consumption for a some object happens all-at-once and at most once.
For example, the IBs transitively included by an RB does not affect the cost of adopting that RB.

# Threads

The `LeiosProtocol.Short.Node.leiosNode` function constructs the node's set of threads.

## Generate threads

At the onset of each slot, the node generates whichever IBs, EBs, VBs, and RBs are required by the mocked Praos and Leios election lotteries.

### Mocked leader schedules

Different objects arise at different rates, but the simulator reuses some common infrastructure for them.
In particular, for each slot, each node is given a random number between 0 and 1 (inclusive) (ie `uniformR (0, 1 :: Double)` from the [random](https://hackage-content.haskell.org/package/random-1.3.1/docs/System-Random.html#v:uniformR) package).
For each object, that number will be mapped to a number of "wins", ie elections, via [Inverse transform sampling](https://en.wikipedia.org/wiki/Inverse_transform_sampling).

The probability distribution of wins is parameterized on the node's stake, which varies per node but not per slot, and on a corresponding protocol parameter, which only varies per kind of object.

### Generating IBs

The IB election lottery allows for a node to generate multiple IBs in a slot.
Each opportunity within a slot is called a "subslot", but the generated IB required by the subslots of some slot are all made (in subslot order) at the slot's onset.

The probability distribution of the node's IB elections in a slot is determined by the `inputBlockFrequencyPerSlot` parameter.

- If the rate is ≤1, then the distribution is `Bernoulli(stake*inputBlockFrequencyPerSlot)`.
- If the rate is >1, then the distribution is `Poisson(stake*inputBlockFrequencyPerSlot)`.

Each IB (see `LeiosProtocol.Common.InputBlock`) consists of the following fields.

- A globally unique ID, which for convenience is the ID of the issuing node and an incrementing counter.
- The slot and subslot of its (implicit) election proof.
- The hash of an RB.
- The byte size of the IB header.
- The byte size of the IB body.

More details for some fields.

- The RB hash is the youngest RB on the node's selection for which the node has already computed the ledger state.
- The header byte size is the constant `inputBlockHeader`.
- The body byte size is the constant `inputBlockBodyAvgSize`.

Each generated IB begins diffusing immediately and is adopted immediately.
If the node should validate its IB before diffusion and adoption, then that cost should be included in the generation cost.

### Generating EBs

The EB leader schedule allows for a node to generate at most one EB in a slot.
TODO the Short Leios specification requires that all EBs are all created at the beginning of Endorse, even if they're election slot is not the first slot in the stage.

The probability distribution of the node's EB elections in a slot is determined by the `endorseBlockFrequencyPerStage` parameter.

- If the rate is ≤1, then the distribution is `Bernoulli(stake*inputBlockFrequencyPerSlot)`.
- If the rate is >1, then the distribution is `Bernoulli(1 - PoissonPmf(0; stake*inputBlockFrequencyPerSlot))`.
  (Note the subtle `min 1 . f` in the definition of `endorseBlockRate`.)

*Remark*.
Those probability distributions converge as `stake` approaches 0.

Each EB (see `LeiosProtocol.Common.EndorseBlock`) consists of the following fields.

- A globally unique ID, which for convenience is the ID of the issuing node and an incrementing counter.
- The slot of its (implicit) election proof.
- The list of IB IDs.
- The list of EB IDs.
- The byte size.

More details for some fields.

- If `leios-late-ib-inclusion` is disabled, an EB from iteration `i` includes the IDs of all IBs that were already adopted, are also from iteration `i`, and arrived before the end of `i`'s Deliver2 stage.
- If `leios-late-ib-inclusion` is enabled, an EB from iteration `i` includes the IDs of all IBs that were already adopted, are from an iteration `j` in the closed interval `[max 0 (i-2), i]`, and arrived before the end of `j`'s contemporary Deliver2 stage.
- If the Leios variant is set to `short`, this EB includes no EB IDs.
- If the Leios variant is set to `full`, an EB from iteration `i` includes the ID of the best eligible EB from each iteration with any eligible EBs.
    - An eligible EB has already been adopted, has already been certified, and is from an iteration in the closed interval `[i - min i (2 + pipelinesToReferenceFromEB), i-3]`.
    - The best eligible EB from the eligible EBs within a particular iteration has more IBs and on a tie arrived earlier.
- The byte size is computed as `ebSizeBytesConstant + ebSizeBytesPerIb * (#IBs + #EBs)`.
- (TODO The field with EB IDs is `endorseBlocksEarlierPipeline`, not `endorseBlocksEarlierStage`.
  The latter is a stub related to equivocation detection; it is always empty during the simulation.)

Each generated EB begins diffusing immediately and is adopted immediately.
If the node should validate its EB before diffusion and adoption, then that cost should be included in the generation cost.

### Generating VBs

The VB election lottery schedules a node to generate a VB at the onset of exactly one slot within the first `activeVotingStageLength`-many slots of the voting stage of every iteration.
The probability distribution of the number of votes in that VB is determined by the `votingFrequencyPerStage` parameter.
The distribution is `Poisson(stake*votingFrequencyPerStage)`.

Each VB (see `LeiosProtocol.Common.VoteMsg`) consists of the following fields.

- A globally unique ID, which for convenience is the ID of the issuing node and an incrementing counter.
- The slot of its (implicit) election proof.
- The number of lottery wins in this slot.
- The list of voted EB IDs.
- The byte size.

More details for some fields.

- If all votes are considered to have the same weight, then a VB determines `#wins * #EBs`-many unweighted votes.
  Otherwise, a VB determines `#EBs`-many weighted votes.
- A VB from iteration `i` includes the IDs of all EBs that satisfy the following.
    - The EB must have already been adopted.
    - The EB must also be from iteration `i`.
    - If `leios-late-ib-inclusion` is disabled, the EB must only include IBs that have already been adopted, are from iteration `i`, and arrived before the end of `i`'s Endorse stage.
    - If `leios-late-ib-inclusion` is disabled, the EB must include all IBs that have already been adopted, are from iteration `i`, and arrived before the end of `i`'s Deliver1 stage.
    - If `leios-late-ib-inclusion` is enabled, the EB must only include IBs that have already been adopted, are from an iteration `j` in the closed interval `[max 0 (i-2), i]`, and arrived before the end of `j`'s Endorse stage.
    - If `leios-late-ib-inclusion` is enabled, the EB must include all IBs that have already been adopted, are from an iteration `j` in the closed interval `[max 0 (i-2), i]`, and arrived before the end of `j`'s Deliver1 stage.
    - If the Leios variant is set to `full`, then let X be the EB's included EBs in iteration order; let Y be the EBs this node would have considered eligible if it were to retroactively create an EB for iteration `i` right now with the only extra restriction being ignore EBs that arrived within Δ_hdr of the end of iteration `i`; then `and (zipWith elem X Y)` must be `True`.
      (TODO the `zipWith` is suspicious; whether it would misbehave in various scenarios depends on many implementation details.)
- The byte size is computed as `voteBundleSizeBytesConstant + voteBundleSizeBytesPerEb * #EBs` (which implies the weighted-vote perspective).

Each generated VB begins diffusing immediately and is adopted immediately.
If the node should validate its VB before diffusion and adoption, then that cost should be included in the generation cost.

### Generating RBs

The RB leader schedule allows for a node to generate at most one RB in a slot.

The probability distribution of the node's RB elections in a slot is determined by the `blockFrequencyPerSlot` parameter.
The distribution is `Bernoulli(stake*inputBlockFrequencyPerSlot)`.

*Remark*.
That distribution converges to Praos's `Bernoulli(ϕ_stake(inputBlockFrequencyPerSlot))` as `stake` approaches 0.

Each RB (see `LeiosProtocol.Common.RankingBlock`) consists of the following fields.

- The byte size of the RB header.
- The slot of its (implicit) election proof.
- The hash of the header content.
- The hash of the body content.
- The block number.
- The hash of its predecessor RB.
- The byte size of the RB body.
- A list (TODO which is always length 0 or 1) of EB IDs paired with the IDs and weights of a quorum of votes for that EB.
- The size of the RB's (implicit) tx payload.
- The ID of the issuing node.

More details for some fields.

- The RB extends the node's preferred chain.
- The tx payload is the constant `rankingBlockLegacyPraosPayloadAvgSize`.
- The EB is the best eligible EB, if any.
    - An eligible EB is certified, from an iteration that doesn't already have a certificate on the extended chain, only references IBs that are already adopted, and is not more than `maxEndorseBlockAgeSlots` slots older than the RB.
    - If the Leios variant is set to `short`, the best of the eligible EBs is oldest, on a tie has more IBs, and on a tie arrived earlier.
    - If the Leios variant is set to `full`, the best of the eligible EBs is youngest, on a tie has more IBs, and on a tie arrived earlier.

Each generated RB begins diffusing immediately and is adopted immediately.
If the node should validate its VB before diffusion and adoption, then that cost should be included in the generation cost.

## Leios diffusion threads

IBs, VBs, and EBs are each diffused via a corresponding instance of the Relay mini protocol and Relay buffer.
This is a generalization of the TxSubmission mini protocol and the Mempool in `ouroboros-network` and `ouroboros-consensus`.

Each Relay instance involves one thread per inbound connection (aka "peers") and one thread per outbound connection (aka "followers").
For an inbound connection, the node is (aggressively/rapidly) pulling IB headers (ie merely IDs for VBs and EBs paired with a slot) and then selectively pulling the IB body (ie VBs and EBs) it wants in a configurable order/prioritization, which is usually FreshestFirst.
It is also configurable which of the peers offering the same body the node fetches it from, which is either just the first or all---all can sometimes reduce latency.
(TODO the real node will likely request from the second peer if the first hasn't yet replied but not the third.)
For an outbound connection, the roles are switched.

*Remark*.
The reason RBs do not diffuse via Relay is because they form a chain, so one block can't be validated without its predecessors: an otherwise-valid block is invalid if it extends an invalid block.

TODO discuss the other Relay parameters, backpressure, pipelining, etc?

When an IB header arrives, its validation task is enqueued on the model CPU---for VBs and EBs it's just an ID, not a header, so there's no validation.
Once that finishes, the Relay logic will decide whether it needs to fetch the body.

- An IB body is not fetched if it exists earlier than it should, it's being offered later than it should be, or if it's already in the buffer.
- An EB is not fetched if it's older than the slot to which the buffer has already been pruned, it's too old to be included by an RB (see `maxEndorseBlockAgeSlots`), or if it's already in the buffer.
- A VB is not fetched if it's older than the slot to which the buffer has already been pruned or if it's already in the buffer.

Different objects are handled differently when the arrived.

- When an IB that extends the genesis block arrives, its validate-and-adopt task is enqueued on the model CPU.
- When an IB that extends a non-genesis RB arrives, its validate-and-adopt task is added to `waitingForLedgerStateVar`.
- When an EB arrives, its validate-and-adopt task is enqueued on the model CPU.
- When a VB arrives, its validate-and-adopt task is enqueued on the model CPU.

## Praos diffusion threads

TODO it's ChainSync and BlockFetch, but how much of `ouroboros-network` and `ouroboros-consensus` was left out?

- When an RB that extends the genesis block arrives, its validate-and-adopt task is enqueued on the model CPU.
- When an RB that extends a non-genesis RB and has no tx payload arrives, its validate-and-adopt task is added to `waitingForRBVar`.
- When an RB that extends a non-genesis RB and has some tx payload arrives, its validate-and-adopt task is added to `waitingForLedgerStateVar`.

## Wait-Validate-Adopt threads

There are three threads that reactively notice when a heretofore missing input becomes available, analogous to out-of-order execution via functional units in a superscalar processor.

- A thread triggered by the adoption of an RB; see `waitingForRBVar`.
- A thread triggered by the construction of an RB's ledger state; see `waitingForLedgerStateVar`.
  (With some Leios variants, the RB validation no longer necessarily provides a ledger state.)
- A thread triggered by the adoption of an IB, see `ibsNeededForEBVar`.

There's also a similar, more general thread that models the scheduling of outstanding tasks on a set of CPU cores, since a block cannot be validated until some modeled CPU core is available; see `taskQueue`.

Those threads enable the following tasks to happen as soon as the necessary inputs and some CPU core are available.
Because those threads use STM to read both the state of pending tasks as well as the state of available inputs, it does not matter if the task or the final input arrives first.

- The node must adopt the preceding RB before validating an RB that has no tx payload.
- The node must construct the ledger state resulting from the preceding RB before it can validate an RB that has some tx payload.
- The node must construct the ledger state resulting from the identified RB before it can validate an IB.
- The node must adopt all transitively included IBs before it can construct the ledger state resulting from an RB with a certified EB.
  (TODO this thread has some complicated and unrealistic logic, since the simulator has no way to acquire "missing" that are no longer diffusing.)

The existence of those threads enable very simple logic for the adoption tasks.

- The node adopts a validated IB by starting to diffuse it, removing the IB from the todo lists in `ibsNeededForEBVar`, and recording its ID and which stage it arrived during.
  See `iBsForEBsAndVotesVar`.
  If it arrived during the IB's iteration's Propose stage (aka "early") or after the IB's iteration's Endorse stage (aka "tardy"), then the IB is discarded.
- The node adopts a validated EB by starting to diffuse it, adding it to `relayEBState`, and adding a corresponding todo list of the not-already-available IBs to `ibsNeededForEBVar`.
- The node adopts a validated VB by starting to diffuse it and adding it to `votesForEBVar`.
- The node adopts a validated RB by starting to diffuse it and including it whenever calculating its selection; see `preferredChain`.

*Remark*.
The "starting to diffuse" element of each step is somewhat hard to see in the code because it's achieved via callbacks.
The Relay component invokes the given callback when some object arrives, and that invocation includes another callback that starts diffusing the object.

## Pruning threads

- *IBs 1*.
  At the end of the Endorse stage for iteration `i`, the node stops diffusing all IBs from `i`.
  See `relayIBState`.
- *IBs 2*.
  If `leios-late-ib-inclusion` is disabled, then at the end of the Vote(Send) stage for iteration `i`, the node forgets the arrival times of all IBs from `i`.
  If `leios-late-ib-inclusion` is enabled, the node instead does that two stages later.
  See `iBsForEBsAndVotesVar`.
- *EBs 1*.
  At the end of the Vote(Recv) stage for iteration `i`, the node stops diffusing and completely forgets all EBs from `i` that are not already certified.
  See `relayEBState`, `votesForEBVar`, and `ibsNeededForEBVar`.
- *VBs*.
  At the end of the Vote(Recv) stage for iteration `i`, the node stops diffusing and completely forgets all VBs from `i`, except that certified EBs from `i` remember the ID and multiplicity of the VBs that first met quorum.
  See `relayVoteState`.
- *EBs 2*.
  If the Leios variant is set to `short`, then `maxEndorseBlockAgeSlots` after the end of the Endorse stage for iteration `i`, the node stops diffusing and forgets all EBs from `i` that were certified but are not included by an RB on the selected chain.
  (TODO these blocks should have stopped diffusing a long time ago, assuming `maxEndorseBlockAgeSlots >> sliceLength`)
  If the Leios variant is set to `full`, the node never forgets a certified EB.
  See `relayEBState`, `votesForEBVar`, and `ibsNeededForEBVar`.
- The node never forgets an RB.

# State

The `LeiosProtocol.Short.Node.LeiosNodeState` record type declares the state shared by the threads.

These components accumulate data over time as the protocol executes.
Many of the statements in this section are redundant with the Threads section above, so those statements will be terse.
However, this section is more granular/concrete, and so has some non-redundant information and explains some design decisions.

The components are as follows.

## Diffuse state & Praos state

These variables maintain the diffusion state, and also the base protocol state.

- `praosState`.
  The state of the Praos components, including Praos diffusion.
  TODO elaborate on the Praos state
- `relayIBState`, `relayEBState`, and `relayVoteState`.
  The IB, EB, and VB Relay buffers.
- `prunedUncertifiedEBStateToVar` and `prunedVoteStateToVar`.
  Records the slot of EBs and VBs that the summarizes which objects the node has stopped diffusing due to age.
  These are used to prevent requesting EBs/VBs that should have already stopped diffusing.
  Since the relevant Relay header and the wall clock contain enough information to do determine that, these variables are just a convenience/optimization.

## Adopt state

These variables reflect the consequence of adopting an IB, EB, or VB.

- `ibsNeededForEBVar`.
  A map from an EB ID to the set of IDs of its IBs that have not yet been adopted.
  Adopting an EB inserts a new entry.
  Pruning an EB removes its entry.
  Adopting an IB removes it from all sets.
  Pruning an IB must **not** reinsert it.
    - There is no analogous state for as-of-yet missing EBs needed by EBs/RBs.
    - This is because EBs are relatively small, and so, _most of the time_ the EBs will have arrived before they're needed.
      A Leios implementation would need to deal with this case---at least for EBs required by the best RB---but it doesn't seem worthwhile to complicate the simulators so far.
    - If the simulations included an adversary who released EBs at the latest possible second, then it might be necessary.
      But so far they don't, so if some EBs are failing to diffuse in time, other aspects should already be looking quite bad.
- `iBsForEBsAndVotesVar`.
  A map from an ID of an adopted IB ID to when that IB arrived.
  Adopting an IB inserts an entry; the adoption might happen much later than the arrival.
  Pruning an IB removes its entry.
    - This variable---and the IB pruning logic in general---only enables logic for EBs and VBs.
      In particular, some IBs that are too old to be included in this variable might still be needed in order to apply some RB, which motivates another variable; see `ibsValidationActionsVar`.
- `votesForEBVar`.
  A map from an EB ID to its progress towards a quorum of votes.
  Pruning an EB removes its entry.
  Adopting a VB increments the progress of all of its EB IDs that have not already reached quorum.
  Pruning a VB does not affect this variable.

## Wait-Validate state

These variables maintain tasks blocked on some missing input.

- `ibsValidationActionsVar`.
  A map from IB ID to validate-and-adopt tasks that are blocked on a missing RB ledger state.
  It is not pruned _per se_; tasks are only removed once they're executed.
    - Usually, the tasks are executed ASAP once the necessary RB ledger state is no longer missing.
      However, when the node computes the ledger state of an RB that includes an IB that is still in this map, it executes the validation logic _even if the necessary RB ledger state is still missing_.
    - A Leios implementation would require the node to somehow urgently fetch the missing RB's chain and its prerequisites from the network, but that would add a great deal of complexity to the simulator.
      So, despite being unfaithful, the relevant bandwidth is never consumed and the relevant CPU is consumed just-in-time.
    - If an IB's RB's ledger state is never computed and no ledger state is subsequently computed for an RB that contains that IB, then that IB's entry will remain in this map indefinitely.
- `waitingForRBVar`.
  A map from RB header hash to a task.
  This is used to trigger tasks waiting on the adoption of some RB.
  Tasks are only removed when they are executed.
- `waitingForLedgerStateVar`
  A map from RB header hash to a task.
  This is used to trigger tasks waiting on the availability of some RB's ledger state.
  Tasks are only removed when they are executed.
- `ledgerStateVar`.
  All RB ledger states that have ever been computed.
  Note that ledger states are a currently isomorphic to the unit type `()`, so this is effectively a set.
  It is never pruned.
- `taskQueue`.
  A queue of tasks scheduled for the CPU, labeled according to what they model (eg "validate an RB").
  Tasks are only removed when they are executed.

# Alternative Design: Linear Leios

## Motivation

In Linear Leios, every time any party issues an RB, they also issue an EB.
In effect, the RB now consists of three parts: a header, a first body (the standard RB body), and a second body (the EB) that extends the first.
The EB includes txs (either by value or by reference)---there are no IBs.
When a (child) RB extends some (parent) RB, it will sometimes include a certificate that demonstrates a quorum of stake has already validated the parent RB's second body.
If the child RB includes that certificate, then its first body extends the parent's second body.
If the child RB excludes that certificate, then its first body instead extends the parent's first body---the parent's second body is irrevocably lost (except maybe on other chains extending that same parent RB).

This variant is _linear_ because the txs that end up on some chain are never unordered: they are ordered in the mempools and they are ordered in the roughly-alternating chain of RBs and EBs.
This is in crucial contrast to Short Leios and its extensions: there, txs included (directly or indirectly) via EBs are concurrent until an RB serializes them (at the latest possible moment).
As a result, this variant is immediately compatible with today's ledger interface, as is---possibly other than reward calculations etc.

## A Terse Interpretation of the Linear Leois Specification

- A node should fetch EBs according to a FreshestFirst policy.
- A node should validate an EB as soon as possible while both of the following are true.
    - It has validated the EB's parent RB.
      The node cannot validate the EB before validating its parent RB.
    - The EB's parent RB is the tip of the best RB header chain it has validated, excluding RB header's whose body turned out to be invalid.
      Any RB that extends the EB's parent RB either excludes the EB or else certifies its validity---in either case, the node no longer needs to validate the EB.
      Note that this conjunct is non-monotonic, due to a relevant RB header being later disqualified when its RB body is recognized as invalid.
      TODO for now, it's merely what the chain has selected, regardless of any better headers.
- A node should vote for an EB as soon as possible within the following interval.
    - The interval ends `L_vote` slots after the onset of the EB's slot (aka `linear-vote-stage-length-slots`).
    - The interval begins either when the node validates the EB or three \Delta_hdr of the onset of the EB's slot, whichever happens last (ie combined the two times via `max`).
      A node must not vote for an EB if it receives evidence of the issuer's equivocation within three \Delta_hdr of the EB's slot onset.
- A node should include an EB certificate, if any, in a new RB that extends the EB's parent if the new RB is at least `L_vote + L_diff` slots younger than the EB's parent (aka `linear-vote-stage-length-slots + linear-diffuse-stage-length-slots`).
  It is important to clarify that an RB remains valid if it excludes the certificate even when those constraints are satisfied.
- A node should diffuse an EB even before it knows whether it's invalid (ie it should enable "EB diffusion pipelining").
  TODO would it even be worth going one step further: _streaming_ the EB, ie diffusing its prefix before its suffix has been received (and therefore before the EB could have been parsed)?
- A node should diffuse RB headers (at most two per election proof) even if it they're not on the best header chain, since such a header might still evidence equivocation.
  We anticipate this happening separately (and redundantly) of ChainSync and BlockFetch.
  TODO it can also abort validation of the EB, right?
  TODO should it exclude the certificate of an equivocated EB if it issues the next RB?

A node should acquire EBs from election opportunities even if they're on competing forks.
That way, if the node switches chains, it will already have the necessary EBs.
It won't have validated them, but that's fine, since it will only need to apply them when a certificate forces them to, so they can skip the validation checks.

In order for the node to receive EBs for RB chains it doesn't necessarily have the RB headers for, RB headers will also be propogated via Relay in addition to and completely independently from their diffusion via ChainSync and BlockFetch.
This is because the RB header announces not just the RB body but also the EB (via the new `EBannounced` field in the RB header from the Linear Leios spec).

## Implementation Notes

The Linear Leios specification indicates that an RB header names the EB that occurs on the chain before the RB, if any, the EB that occurs after the RB, if any, and an EB names the RB that it follows.
However, in the absence of an attacker, the simulator can simply use the existing data types for Linear Leios even though the RB header type excludes those two fields.

- The simulator does not currently have extensible data types for Praos headers, so it would not be trivial to add these header fields.
- In the absence of an attacker within the simulation, the new RB header fields aren't _necessary_.
- Despite being unnecessary, having the RB header announce its second body EB would plausibly decrease the average latency of the EBs.
  But that decrease should be _very_ minor; with the current overly-coarse multiplexer logic (see [Issue 453](https://github.com/input-output-hk/ouroboros-leios/issues/453)), the EB's `RelayHeader` will arrive immediately after the ChainSync header (which are small), except perhaps during severe congestion.

The Linear Leios simulator adds the following new variables, some of which also require new threads.

- `relayLinearEBState`.
  As a shortcut, the first Linear Leios simulator will instantiate `Relay` with `RelayHeader InputBlockId` and `InputBlock`.
  This is because the IB specified in Short Leios has just a few small fields more than the EB specified in Linear Leios.
    - It is remarkable that the Linear EB is added to the Relay buffer immediately, before its validated.
      This is "EB Diffusion Pipelining", as indicated in the Linear Leios specification.
- `linearLedgerStateVar`, `waitingForLinearLedgerStateVar`, and `waitingForWaitingForLinearLedgerStateVar`.
  An RB that contains an EB cert canot be validated without the the certified EB's ledger state.
  However, that EB is necessarily certified, so its ledger state can be built comparatively cheaply now, but still not for free.
    - The arrival of a Linear EB populates `waitingForWaitingForLinearLedgerStateVar` (and also `waitingForTipVar`; see below).
    - The arrival of an RB populates `waitingForLinearLedgerStateVar`, which triggers the `waitingForWaitingForLinearLedgerStateVar` action to populate `linearLedgerStateVar` via the comparatively cheap `reapply` task.
- `waitingForTipVar`.
  The Linear EB should be validated the first time that both it has arrived and its parent RB is the tip of the node's selection.
- `linearEbsToVoteVar`.
  Once a Linear EB has been validated, it should be voted for.
  A new custom thread monitors this variable in addition to the clock, so that it can avoid issugin a vote too early or too late.
- `linearEbOfRb`.
  A mapping from RB to its announced Linear EB _that has been validated_, which is needed when issuing an RB.
- `pruneExpiredLinearVotes`.
  This thread prunes votes 30 seconds after the onset of their EB's slot.

TODO RB Diffusion is not pipelined

TODO RBs are so far only distributed by ChainSync and BlockFetch
