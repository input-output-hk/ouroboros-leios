# Stracciatella

To run Stracciatella, set `leios-variant` to `full-without-ibs`.

## Description

"Stracciatella" is the name of a simpler version of Leios, where input blocks have been eliminated and endorser blocks contain reference to transactions directly.

Transactions and ranking blocks behave the same as in the original Leios simulation, and both are quickly diffused throughout the network. Ranking blocks still contain an endorsement for a single endorser block, which still references older endorser blocks.

Endorser blocks are still produced on a schedule, at the start of every stage. Endorser blocks choose which transactions to reference by sampling from a dedicated Leios mempool (which operates identically to the Leios mempool from the the other variant). Endorser blocks are transmitted as header-only, without any concept of freshest-first delivery.

Voting for endorser blocks also behaves mostly the same as in the original Leios. A node will only vote for an endorser block if that node has validated the bodies of all transactions referenced by the block. Note that nodes never request to download “missing” transactions from a block; transactions diffuse quickly throughout the network, so that was never necessary.

## CPU model
|Task name in logs|Task name in code|When does it run|What happens when it completes|CPU cost
|---|---|---|---|---|
|`ValTX`|`TransactionValidated`|After a transaction has been received from a peer.|That TX is announced to other peers.|`tx-validation-cpu-time-ms`|
|`GenRB`|`RBBlockGenerated`|After a new ranking block has been generated.|That RB is announced to peers.|`rb-generation-cpu-time-ms` + `cert-generation-cpu-time-ms-constant` + `cert-generation-cpu-time-ms-per-node` for each node that voted for the endorsed EB|
|`ValRB`|`RBBlockValidated`|After a ranking block has been received.|That RB body is announced to peers and (potentially) accepted as the tip of the chain.|`rb-body-legacy-praos-payload-validation-cpu-time-ms-constant` + `rb-body-legacy-praos-payload-validation-cpu-time-ms-per-byte` for each byte of TX  + `cert-generation-cpu-time-ms-constant` + `cert-generation-cpu-time-ms-per-node` for each node that voted for the endorsed EB|
|`GenEB`|`EBBlockGenerated`|After a new EB has been generated.|That EB is announced to peers.|`eb-generation-cpu-time-ms`|
|`ValEB`|`EBBlockValidated`|After an EB's body has been received from a peer.|That EB is announced to peers.|`eb-validation-cpu-time-ms-constant` + `eb-validation-cpu-time-ms-per-byte` for each byte of TX|
|`GenVote`|`VTBundleGenerated`|After a vote bundle has been generated.|That vote bundle is announced to peers.|`vote-generation-cpu-time-ms-constant` + `vote-generation-cpu-time-ms-per-tx` for each TX in the EB|
|`ValVote`|`VTBundleValidated`|After a vote bundle has been received from a peer.|The votes in that bundle are stored, and the bundle is propagated to peers.|`vote-validation-cpu-time-ms` for each EB voted for (in parallel)|
