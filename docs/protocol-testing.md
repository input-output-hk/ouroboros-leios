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

## Test Cases

| No. | Description                  | Parameter(s)                                                                     |
| --- | ---------------------------- | -------------------------------------------------------------------------------- |
| 1   | Impact of increasing IB size | `ib-body-max-size-bytes`, `ib-body-avg-size-bytes`, `tx-size-bytes-distribution` |
| 2   | Vary IB production rate      | `ib-generation-probability`                                                      |
