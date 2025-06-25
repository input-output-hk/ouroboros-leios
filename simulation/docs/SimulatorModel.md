# Introduction

This document summarizes the structure and behaviors of the Haskell Leios simulator.
The level of detail is between the code itself and the various work-in-progress Leios specifications.

The Leios node is modeled as a set of threads that maintain shared state via the [stm](https://hackage.haskell.org/package/stm) library, as with the existing `ouroboros-network` and `ouroboros-consensus` implementation libraries.
This document will primarily describe those threads and the components of their shared state.

TODO also discuss the mini protocol multiplexing and TCP model

# Lifetime of an object

The objects within the simulator include Input Blocks (IBs), Endorser Blocks (EBs) (aka Endorsement Blocks, aka Endorse Blocks), Vote Bundles (VBs), and Ranking Blocks (RBs).
Certificates are not explicit; for example, a certificate's computational cost is instead associated with the containing RB.

Within a single simulated node, the lifetime of every such object follows a common sequence.

- *Generate*, the duration when the node is generating an object.
- *Receive*, the moment a node receives (the entirety of) an ojbect from a peer.
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

- An EB from iteration `i` includes the IDs of all IBs that were already adopted, are also from iteration `i`, and arrived before the end of `i`'s Deliver2 stage.
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
    - The EB must only include IBs that have already been adopted, are from iteration `i`, and arrived before the end of `i`'s Endorse stage.
    - The EB must include all IBs that have already been adopted, are from iteration `i`, and arrived before the end of `i`'s Deliver1 stage.
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

IBs, VBs, and EBs are each diffused via a corresonding instance of the Relay mini protocol and Relay buffer.
This is a generalization of the TxSubmission mini protocol and the Mempool in `ouroboros-network` and `ouroboros-consensus`.

Each Relay instance involves one thread per inbound connection (aka "peers") and one thread per outbound connection (aka "followers").
For an inbound connection, the node is (aggressively/rapidly) pulling IB headers (ie merely IDs for VBs and EBs) and then selectively pulling the IB body (ie VBs and EBs) it wants in a configurable order/prioritization, which is usually FreshestFirst.
It is also configurable which of the peers offering the same body the node fetches it from, which is either just the first or all---all can sometimes reduce latency.
(TODO the real node will likely request from the second peer if the first hasn't yet replied but not the third.)
For an outbound connection, the roles are switched.

*Remark*.
The reason RBs do not diffuse via Relay is because they form a chain, so one block can't be validated without its predecessors: an otherwise-valid block is invalid if it extends an invalid block.

TODO discuss the other Relay parameters, backpressure, pipelining, etc?

TODO IB headers incur validation delays, but others don't since they're merely IDs

Different objects are handled differently when the arrived.

- When an IB that extends the genesis bock arrives, its validate-and-adopt task is enqueued on the model CPU.
- When an IB that extends a non-genesis RB arrives, its validate-and-adopt task is added to `waitingForLedgerStateVar`.
- When an EB arrives, its validate-and-adopt task is enqueued on the model CPU.
- When an VB arrives, its validate-and-adopt task is enqueued on the model CPU.

## Praos diffusion threads

TODO it's ChainSync and BlockFetch, but how much of `ouroboros-network` and `ouroboros-consensus` was left out?

- When an RB that extends the genesis bock arrives, its validate-and-adopt task is enqueued on the model CPU.
- When an RB that extends a non-genesis RB and has no tx payload arrives, its validate-and-adopt task is added to `waitingForRBVar`.
- When an RB that extends a non-genesis RB and has some tx payload arrives, its validate-and-adopt task is added to `waitingForLedgerStateVar`.

## Wait-Validate-Adopt threads

There are three threads that reactively notice when a heretofore missing input becomes available, analogous to out-of-order execution via functional units in a superscalar processor.

- One thread is triggering by the adoption of an RB; see `waitingForRBVar`.
- One by the construction of an RB's ledger state; see `waitingForLedgerStateVar`.
  (With some Leios variants, the RB validation no longer necessarily provides a ledger state.)
- One by the arrival of an IB, see `ibsNeededForEBVar`.

There's also a similar, more general thread that models the scheduling of outstanding tasks on a set of CPU cores; a block cannot be validated until some core is available; see `taskQueue`.

Those threads enable the following tasks to happen as soon as the necessary inputs and some CPU core are available.
Because those threads use STM to read both the state of pending tasks as well as the state of available inputs, it does not matter if the task or the input arrives first.

- The node must adopt the preceding RB before validating an RB that has no tx payload.
- The node must construct the ledger state resulting from the preceding RB before it can validate an RB that has some tx payload.
- The node must construct the ledger state resulting from the identified RB before it can validate an IB.
- The node must receive all transitively included IBs before it can construct the ledger state resulting from an RB with a certified EB.
  (TODO this thread has some complicated and unrealistic logic, since the simulator has no way to acquire objects that are no longer diffusing.)

The existence of those threads enable very simple logic for the adoption tasks.

- The node adopts a validated IB by starting to diffuse it and adding it to `ibDeliveryTimesVar` and removing it from the todo lists in `ibsNeededForEBVar`.
- The node adopts a validated EB by starting to diffuse it and adding it to `relayEBState` and add a corresponding todo list of the not-already-available IBs to `ibsNeededForEBVar`.
- The node adopts a validated VB by starting to diffuse it and adding it to `votesForEBVar`.
- The node adopts a validated RB by starting to diffuse it and including it whenever calculating its selection; see `preferredChain`.

*Remark*.
The "starting to diffuse" element of each step is somewhat hard to see in the code because its achieved via callbacks.

## Pruning threads

- *IBs 1*.
  At the end of the Vote(Send) stage for iteration `i`, the node stops diffusing all IBs from `i`.
  (TODO this should happen at the end of the Endorse stage, but this buffer is being abused as the adoption buffer as well.)
  It also forgets any of those IBs it had adopted, with the exception of their arrival time, which is used when generating VBs.
  See `relayIBState`.
- *EBs 1*.
  At the end of the Vote(Recv) stage for iteration `i`, the node stops diffusing and completely forgets all EBs from `i` that are not already certified.
  See `relayEBState`, `votesForEBVar`, and `ibsNeededForEBVar`.
- *VBs* and *IBs 2*.
  At the end of the Vote(Recv) stage for iteration `i`, the node stops diffusing and completely forgets all VBs from `i`, except that certified EBs from `i` remember the ID and multiplicity of the VBs that first met quorum.
  It also forgets the arrival time of IBs from `i`.
  See `relayVoteState` and `ibDeliveryTimesVar`.
- *EBs 2*.
  If the Leios variant is set to `short`, then `maxEndorseBlockAgeSlots` after the end of the Endorse stage for iteration `i`, the node stops diffusing and forgets all EBs from `i` that were certified but are not included by an RB on the selected chain.
  (TODO these blocks should have stopped diffusing a long time ago, assuming `maxEndorseBlockAgeSlots >> sliceLength`)
  If the Leios variant is set to `full`, the node never forgets a certified EB.
  See `relayEBState`, `votesForEBVar`, and `ibsNeededForEBVar`.
- The node never forgets an RB.

# State

The `LeiosProtocol.Short.Node.LeiosNodeState` record type declares the state shared by the threads.

## Leios Diffusion state

TODO `relayIBState`, `relayEBState`, `relayVoteState`

## Waiting&Validation state

TODO `ibsNeededForEBVar`, `waitingForRBVar`, `waitingForLedgerStateVar`, `ledgerStateVar`, `ibsValidationActionsVar`

TODO include `taskQueue`

## Adopted IBs state

TODO `relayIBState` abuse

TODO `ibDeliveryTimesVar`

## Adopted EBs state

TODO `relayEBState` abuse

## Adopted VBs state

TODO `votesForEBVar`

## Adopted RBs & Praos Diffusion state

TODO
