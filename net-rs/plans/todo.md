## Quick TODO list

## Fork sticking: remaining parent-miss

Two nodes hit `parent not in chain_tree` in the latest p=0.2 cluster
run despite the contiguity guard. The block's chain_tree and
block_cache entries appear to have different prev_hash values for the
same hash, but code inspection shows both paths store the same parsed
header value. Investigate:
- Is the block received twice with different bodies (hash collision
  impossible, but maybe the point/hash derivation differs)?
- Does `chain_tree.insert` idempotency interact with a later
  `block_cache.insert` overwrite to create a mismatch?
- Could `register_self_produced` and `on_block_received` race on
  the same hash with different header parses?

## Fork sticking: convergence speed

Nodes adopt peer blocks one at a time (replay_len=1) instead of bulk
replay. This means a lagging node catches up by one block per
select_chain cycle instead of switching to the full peer chain in one
go. Likely caused by the PeerChain walk finding the adopted tip as a
common ancestor (since the node self-produced on the adopted chain),
leaving only the single newest peer entry in the replay. Needs a way
to replay the full range from the common ancestor to the peer tip,
including blocks that are in block_cache but not in PeerChain entries.

## UI memory leak

Memory is still leaking.

## Sample models

Provide a dropdown of sample models to load to set cluster parameters
before restarting.  Samples would be:

- current one "25 nodes degree 3, realistic"
- a circle "25 nodes degree 2, loop"
- minimal "3 nodes degree 2"

## Mempool tracing

Trace mempool fullness for each node independently and min-max curves
for the whole network.
