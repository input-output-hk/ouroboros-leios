## Quick TODO list

## Consensus

We need to implement true Praos consensus (longest chain).  I suspect
the co-ordinator may be doing too much in this regard and should delegate
the choice of blocks to fetch entirely to the node's consensus.

Consensus will need to build a tree of chains / forks and when a new block
is offered, attach it to the relevant fork (this requires the previous block
hash from the header).  Then it should choose which of the chains is now
the longest, and fetch blocks it does not already have.

## Cluster control

Control of the cluster from the UI - ability to set size, degree
and latency parameters and restart the cluster
