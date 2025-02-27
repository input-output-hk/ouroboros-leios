---
sidebar_position: 2
---

# Throughput simulation

The [throughput simulator](https://www.insightmaker.com/insight/4DU4kmFVCFDaq30ux29PCe/Cardano-Throughput-v0-3) is an interactive tool demonstrating how varying transaction volumes, ledger storage, and stake pool costs can influence Cardano’s future growth. It incorporates multiple variables and feedback loops to illustrate how transaction fees and rewards circulate among the treasury, reserve, and user wallets.

## Why it matters

- **Scalability insights.** Understanding how increasing transactions per second affects on-chain data size and fee distribution.
- **Policy testing.** Enables ‘what if’ experiments (for example, adjusting the average fee per transaction) without impacting the live network.
- **Educational exploration.** Helps users and developers build an intuitive mental model of Cardano’s economic flows.

## How to use it

1. **Adjust parameters.** Move sliders or input numeric values for transaction volumes, lovelace price, and hardware cost trends.
2. **Run the simulation.** Observe changes in ada distribution, treasury accumulation, and ledger growth.
3. **Compare scenarios.** Toggle disk compression rates (for example, ‘50% disk compression’) to see how overall storage costs shift.
4. **Interpret results.** Look for overall patterns rather than exact predictions. The model highlights trends and correlations.

## Key properties

- **Multiple feedback loops.** The model tracks about 29 interlinked loops, providing insights into how fees, stake, and rewards reinforce or reduce each other.
- **Conservation of ada.** Ada totals remain fixed at 45 billion, divided among the treasury, reserves, and user accounts.
- **Simplified assumptions.** Designed for exploration, this model excludes finer protocol details, focusing on high-level economics and throughput.