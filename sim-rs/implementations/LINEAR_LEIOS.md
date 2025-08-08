# Linear Leios Implementation

To run Linear Leios with entire transactions stored in EBs, set `leios-variant` to `linear`.
To run Linear Leios with transaction references stored in EBs, set `leios-variant` to `linear-with-tx-references`.

The log file schema is currently identical to every other variant (though `pipeline` is always 0).

## Description

Whenever a node creates an RB, it also creates an EB. The RB header contains a reference to this new EB. If the RB producer has a certificate for the parent RB’s EB, it will include that certificate in the RB body.

RB headers are diffused separately from bodies. When a node receives an RB header, it checks whether that RB should be the new head of its chain. If so, it will request the RB body and the referenced EB (from the first peer which announces them).

When a node receives an EB body, it runs lightweight validation and then propagates the body to peers. After this lightweight validation, it runs more expensive complete validation (presumably at the TX level) before voting.

To detect equivocation, a node will wait until at least `3 * Δhdr` after an EB was generated before voting for it.

When voting, a node runs a VRF lottery to decide how many times it can vote for that EB; if it has any votes, it will transmit them to all peers.

## Mempool behavior

When a node creates an RB, it will follow these steps in order:
 1. Try to produce a cert for the parent RB's EB.
   1. If this succeeds, remove all of this EB's transactions from its mempool.
 2. Fill the RB body with transactions from its mempool
 3. Create a new EB, filled with transactions from its mempool WITHOUT removing those transactions from the mempool.

When a node receives an RB body, it immediately removes all referenced/conflicting transactions from its mempool. If the RB has an EB certificate, it also removes that EB’s transactions from its mempool.

## New parameters

|Name|Description|Default value|
|---|---|---|
|`linear-vote-stage-length-slots`|How many slots the EB voting stage is allowed to last. For equivocation protection, this should be at least 3 * delta_hdr (which is currently 1 second).|5|
|`linear-diffuse-stage-length-slots`|How many slots are votes allowed to diffuse.|5|
|`eb-body-avg-size-bytes`|If `simulate-transactions` is false, this controls the size of the EBs we generate.|0|
|`eb-header-validation-cpu-time-ms`|The time taken to validate an EB _before_ we propagate it to peers|50.0|
|`eb-body-validation-cpu-time-ms-constant`|The time taken to validate the transactions in an EB _after_ we propagate it to peers.|50.0|
|`eb-body-validation-cpu-time-ms-per-byte`|The time taken to validate the transactions in an EB _after_ we propagate it to peers.|50.0|
|`vote-generation-cpu-time-ms-per-tx`|A per-transaction CPU cost to apply when generating new vote bundles.|0|

## CPU model
|Task name in logs|Task name in code|When does it run|What happens when it completes|CPU cost
|---|---|---|---|---|
|`ValTX`|`TransactionValidated`|After a transaction has been received from a peer.|That TX is announced to other peers.|`tx-validation-cpu-time-ms`|
|`GenRB`|`RBBlockGenerated`|After a new ranking block has been generated.|That RB and its EB are announced to peers.|`rb-generation-cpu-time-ms` and `eb-generation-cpu-time-ms` (in parallel)|
|`ValRH`|`RBHeaderValidated`|After a ranking block header has been received.|That RB is announced to peers.<br/>The referenced EB is queued to be downloaded when available.|`rb-head-validation-cpu-time-ms`|
|`ValRB`|`RBBlockValidated`|After a ranking block body has been received.|That RB body is announced to peers and (potentially) accepted as the tip of the chain.|`rb-body-legacy-praos-payload-validation-cpu-time-ms-constant` + `rb-body-legacy-praos-payload-validation-cpu-time-ms-per-byte` for each byte of TX|
|`ValEH`|`EBHeaderValidated`|After an EB header has been received and validated.|That EB is announced to peers, and body validation begins in the background.|`eb-header-validation-cpu-time-ms`|
|`ValEB`|`EBBlockValidated`|After an EB's body has been validated.|If eligible, the node will vote for that EB.|`eb-body-validation-cpu-time-ms-constant` + `eb-body-validation-cpu-time-ms-per-byte` for each byte of TX|
|`GenVote`|`VTBundleGenerated`|After a vote bundle has been generated.|That vote bundle is announced to peers.|`vote-generation-cpu-time-ms-constant` + `vote-generation-cpu-time-ms-per-tx` for each TX in the EB|
|`ValVote`|`VTBundleValidated`|After a vote bundle has been received from a peer.|The votes in that bundle are stored, and the bundle is propagated to peers.|`vote-validation-cpu-time-ms`|

## Not yet implemented
- Freshest first delivery is not implemented for EBs, though EBs are created infrequently enough that this likely doesn't matter.
- We are not yet simulating equivocation.
