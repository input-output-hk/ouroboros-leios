---
sidebar_position: 4
---

# Cost estimator

The Linear Leios (CIP-164) [**cost estimator tool**](https://leios.cardano-scaling.org/cost-estimator/) estimates operating costs for running a Leios node. It integrates resource usage data — CPU, disk, network egress, and IOPS — to translate confirmed transaction throughput (TxkB/s) into projected monthly expenses for stake pool operators. See the [detailed cost analysis](https://github.com/input-output-hk/ouroboros-leios/tree/main/docs/cost-estimate) for methodology.

## How it works

The primary input is **confirmed throughput** in TxkB/s (transaction kilobytes per second reaching the ledger). The tool computes per-node resource requirements using the CIP-164 protocol parameters (active slot coefficient, voting window, votes per EB) and benchmark data (validation times from `db-analyser` and cryptography prototypes). Cloud cost presets let you compare hyperscale providers against discount providers.

## Example use cases

1. **Stake pool budgeting**:
   Operators can evaluate whether their fee revenue will cover a projected monthly cloud invoice at different throughput levels.

2. **Protocol parameter exploration**:
   Adjusting the voting window, vote committee size, or fetch multiplicity shows how these parameters affect CPU overhead and network egress.

3. **Provider comparison**:
   The cost presets for hyperscale and discount providers highlight where egress-heavy workloads benefit from providers with generous included transfer.
