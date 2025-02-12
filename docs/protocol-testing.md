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
- How does IB generation frequency relate to IB network dissemination time?
    - How does this time relate to the time described in the network functionality in the Leios paper?
    - What is the induced network capacity?
- How rapidly or gradually does efficiency degrade as throughput increases?
- Do RBs propagate back to IB producers in time for the ledger update to be available when the IB is produced?

### Endoser Block (EB) Parameters
- How does EB generation frequency relate to having zero or duplicate EBs as candidates for certification in the RB?

### Resources

- What are the peak CPU resources required as a function of throughput?
    - What operations create CPU bottlenecks?

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
