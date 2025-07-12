# Linear Leios (rust simulation)

To run it, set `leios-variant` to `linear`.

The log file schema is currently identical to every other variant (though `pipeline` is always 0).

## Description

Whenever a node creates an RB, it also creates an EB. The RB header contains a reference to this new EB. If the RB producer has a certificate for the parent RB’s EB, it will include that certificate in the RB body.

RB headers are diffused separately from bodies. When a node receives an RB header, it checks whether that RB should be the new head of its chain. If so, it will request the RB body and the referenced EB (from the first peer which announces them).

When a node receives an RB body, it immediately removes all referenced/conflicting transactions from its mempool. If the RB has an EB certificate, it also removes that EB’s transactions from its mempool. 

When a node receives an EB body, it immediately runs a VRF lottery, and if successful, transmits votes for that EB. If the EB has been certified after L_vote + L_diff slots have passed, the node removes all of its transactions from the mempool (under the assumption that the EB will make it on-chain).

## New parameters

|Name|Description|Default value|
|---|---|---|
|`linear-vote-stage-length-slots`|How many slots the EB voting stage is allowed to last. For equivocation protection, this should be at least 3 * delta_hdr (which is currently 1 second).|5|
|`linear-diffuse-stage-length-slots`|How many slots are votes allowed to diffuse.|5|
|`eb-body-avg-size-bytes`|If `simulate-transactions` is false, this controls the size of the EBs we generate.|0|
|`vote-generation-cpu-time-ms-per-tx`|A per-transaction CPU cost to apply when generating new vote bundles.|0|

## Not yet implemented
- Freshest first delivery is not implemented for EBs, though EBs are created infrequently enough that this likely doesn't matter.
- We are not yet applying voting rules; if you’re allowed to vote, you will always vote.
- We are not yet accounting for equivocation.
- Nodes are supposed to wait until the diffuse stage to vote for an EB, they are currently voting as soon as they can.
