# Roadmap

- [ ] Extend with high-level simulation of Praos  
      (Insofar as necessary for simulating ranking blocks in Simplified Leios.)
- [ ] Extend with high-level simulation of Simplified Leios

## Open Questions

- To what extent can we reuse the simulation of Leios in `leios-sim`?

## Brainstorm

* Reuse `relayNode` but use Leios-specific blocks.
* Also need Praos layer for Ranking blocks, could be high-level/abstract.
  - Could start with Shelley's ChainSync with whole-blocks: overestimates ranking blocks traffic.
* Actually implement Leios protocol, rather than just send blocks.
  - Non-block-producing nodes might skip some parts like downloading votes.
  - Some nodes produce transactions, with some distribution governing the timeslots.
     * Later: Simulation scenario might determine transactions submitted over time.
  - Needed structures for the node:
    - Mempool of valid transactions (to include in IBs).
      - Challenge: minimize inclusion of same/conflicting tx in separate IBs.
    - Set for certifiable EBs to include in RBs.
      * Actually we have to accumulate votes for EBs in general: only from specific slot ranges though.
    - Ledger state
    - Base chain (See Shelley's ChainDB ?)
    - Two sets of IBs
      * Validated, to relay.
      * Waiting to be validated, because ledger state is lagging.
        - IBs carry reference to RB whose ledger state is needed to validate (Discuss with research).
    - Blocks/Votes should be indexable by slot range, as pipelines are based on slices.
      * Old enough ones should be pruned: unless they are referenced (or could be?) by a RB though.
        - Can we throw away old non-RB-referenced but Vote2-certified EBs? Asked research in discussion.
  - Need to trigger tasks on new slot:
    * Different VRF lotteries for each of: IB, Link EB, Endorse EB, Vote1, Vote2, RB.
    * A slot lasts 1 second.
