## Quick TODO list

## RTT measurement

Doesn't look like latencies are being counted - measured in the wrong place?
Or latency added in the wrong place?

## Graph display

Increase repel force to spread the graph more

## Node tip display

Show the last 2 hex digits of the node hash to ensure they are all one
the *same* block at that number.

## Consensus

We need to implement true Praos consensus (longest chain).  I suspect
the co-ordinator may be doing too much in this regard and should delegate
the choice of blocks to fetch entirely to the node's consensus.

Consensus will need to build a tree of chains / forks and when a new block
is offered, attach it to the relevant fork (this requires the previous block
hash from the header).  Then it should choose which of the chains is now
the longest, and fetch blocks it does not already have.

## Reordering of events

It looks like events are getting re-ordered in the log - for example you
see a VTVoteGenerated before EBGenerated or EBReceived.
