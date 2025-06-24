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
- *Adopt*, the moment the node updates it state in response to the successful validation.
- *Forget*, the moment the node updates it state once the object is no longer necessary/relevant.

Only generation and validation consume modeled CPU, and nothing consumes any modeled RAM/disk capacity/bandwidth.

Modeled CPU consumption for a some object happens all-at-once and at most once.
For example, the IBs transitively included by an RB does not affect the cost of adopting that RB.

# Threads

The `LeiosProtocol.Short.Node.leiosNode` function constructs the node's set of threads.

## Generate threads

At the onset of each slot, the node generates whichever IBs, EBs, VBs, and RBs are required by the mocked Praos and Leios election lotteries.

### Mocked leader schedules

Different objects arise at different rates, but the simulator reuses some common infrastructure for them.
In particular, for each slot, each node is given a random number between (ie `uniformR (0, 1 :: Double)` from the [random](https://hackage-content.haskell.org/package/random-1.3.1/docs/System-Random.html#v:uniformR) package (which is inclusive).
For each object, that number will be mapped to a number of "wins", ie elections, via [Inverse transform sampling](https://en.wikipedia.org/wiki/Inverse_transform_sampling).

The probability distribution of wins is parameterized on the node's stake, which varies per node but not per slot, and on a corresponding protocol parameter, which varies per kind of object.

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
That distributions converges to Praos's `Bernoulli(ϕ_stake(inputBlockFrequencyPerSlot))` as `stake` approaches 0.

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
    - An eligible EB is certified, from an iteration that doesn't already have a certificate on the extended chain, only references IBs are already adopted, and is not more than `maxEndorseBlockAgeSlots` slots older than the RB.
    - If the Leios variant is set to `short`, the best of the eligible EBs is oldest, on a tie has more IBs, and on a tie arrived earlier.
    - If the Leios variant is set to `full`, the best of the eligible EBs is youngest, on a tie has more IBs, and on a tie arrived earlier.

Each generated RB begins diffusing immediately and is adopted immediately.
If the node should validate its VB before diffusion and adoption, then that cost should be included in the generation cost.

## Leios diffusion threads

TODO

## Waiting&Validation threads

TODO

## Pruning threads

TODO

## Praos diffusion threads

TODO

# State

The `LeiosProtocol.Short.Node.LeiosNodeState` record type declares the state shared by the threads.

## Leios Diffusion state

TODO

## Waiting&Validation state

TODO

TODO include `taskQueue`

## Adopted IBs state

TODO

## Adopted EBs state

TODO

## Adopted VBs state

TODO

## Adopted RBs state

TODO

## Praos Diffusion state

TODO
