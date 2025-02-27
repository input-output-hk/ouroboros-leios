---
sidebar_position: 4
---

# Cost Estimator

The Leios [cost estimator tool](https://leios.cardano-scaling.org/cost-estimator/) provides detailed insights into node operating costs. Integrating data on resource usage, including CPU, disk, and network bandwidth effectively connects theoretical throughput growth with the actual monthly expenses that stake pool operators incur. This estimator aligns with the same parameters used in the throughput simulator – such as transaction rates, average block sizes, and compression settings – and translates these into projected bills for cloud servers or local hardware.

## How it works

Start by specifying the number of block producers, relays, and certificates per epoch. Additionally, you can make assumptions about vCPU usage, disk input/output operations per second, and network egress. If you enable compression (for instance, at 50% or 70%), the tool recalculates monthly storage costs accordingly. This process demonstrates how overall expenses may increase or decrease based on different throughput levels.

## Example use cases

1. **Stake pool budgeting**:  
   Operators can evaluate whether their fee revenue will cover a projected monthly cloud invoice when transaction volume reaches two million transactions per epoch.

2. **Long-term planning**:  
   By assuming a 15% annual decrease in hardware costs, the estimator can indicate whether compression and block production improvements can outpace ledger growth over the next five years.

3. **Resource balancing**:  
   Some operators might opt to add more relays or upgrade to more powerful CPUs to accommodate higher throughput. The cost estimator illustrates how these decisions will affect monthly expenses, allowing for adjustments to strategy as needed.
