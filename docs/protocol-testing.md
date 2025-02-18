# Protocol Testing

## Introduction

This document collects objectives & questions around the protocol and effects of
changing the configuration parameters.

### Objectives

- Find optimal parameters for the protocol
- Find correlations between parameters

### Red Flags

In all considerable cases, we want the protocol to be stable and **degrade
gracefully**. If we observe the simulations abruptly diverge from expected
behavior, it is a red flag.

## Questions

### Input Block (IB) Parameters

- Are smaller-sized, more frequent IBs better or worse than larger-sized, less frequent IBs?
- How does IB generation frequency and size relate to IB network dissemination time?
    - How does this time relate to the time described in the network functionality in the Leios paper?
    - What is the induced network capacity?
- Explore windowed versions of the freshest-first policy (recent IBs are downloaded oldest-first, older IBs are downloaded freshest first).
- How rapidly or gradually does efficiency/latency degrade as throughput increases?
- Do RBs propagate back to IB producers in time for the ledger update to be available when the IB is produced?
- Are IBs referenced by main-chain RBs available in time for legder construction?

### Endoser Block (EB) Parameters
- How does EB generation frequency relate to having zero or duplicate EBs as candidates for certification in the RB?
- How large should the EB stage be so that honest EB dissemination completes in time for voting? Similarly, how large should the voting stage be for timely vote arrival?

### Resources

- What are the peak CPU resources required as a function of throughput?
    - What operations create CPU bottlenecks?
    - How much free CPU is available?
 
### Relation to theoretical work
- What is the probability that all honest IBs of a pipeline are delivered by the end of stage deliver 1 w.r.t. deliver 1's length? Similarly, about the probabilty that a certified EB containing all honest IBs being produced.

## Test Cases

| No. | Description                  | [Parameter](../data/simulation/config.d.ts)                                      |
| --- | ---------------------------- | -------------------------------------------------------------------------------- |
| 1   | Impact of increasing IB size | `ib-body-max-size-bytes`, `ib-body-avg-size-bytes`, `tx-size-bytes-distribution` |
| 2   | Vary IB production rate      | `ib-generation-probability`                                                      |
| 3   | Vary EB production rate      | `eb-generation-probability`                                                      |
| 4   | Maximize throughput          | `ib-body-avg-size-byte` * `ib-generation-probability`                            |

## Metrics

- Duplicate EBs
- EBs not making into a RB (short Leios only)
- IBs sent or received outside of required window for the pipeline
- EBs sent or received outside of required window for the pipeline
- Votes sent or received outside of required window for the pipeline
- "Expired" EBs
- "Expired" IBs
- RBs arriving after an IB is produced in a new pipeline
- Peak CPU usage
- Average CPU usage
- I/O operations per second

## Diagnostics (i.e., faithfulness to the protocol)

- IB, EB, and vote production matches protocol parameters
- IB, EB, and vote production is proportional to a node's stake
- Propagation times are consistent with DeltaQSD estimates
