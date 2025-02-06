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

- Are smaller-sized, more frequent IBs better or worse than larger-sized, less
  frequent IBs?
- How does IB generation frequency relate to IB network dissemination time? How does this time relate to the time described in the network functionality in the Leios paper? What is the induced network capacity ?

## Test Cases

| No. | Description                  | [Parameter](../data/simulation/config.d.ts)                                      |
| --- | ---------------------------- | -------------------------------------------------------------------------------- |
| 1   | Impact of increasing IB size | `ib-body-max-size-bytes`, `ib-body-avg-size-bytes`, `tx-size-bytes-distribution` |
| 2   | Vary IB production rate      | `ib-generation-probability`                                                      |
