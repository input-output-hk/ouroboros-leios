---
title: Weekly Summary – August 18, 2025
authors:
- will
tags: [progress, update, weekly, attack-analysis, parameter-sweep, rust-simulation, proposed-leios, mainnet-analysis]
---

This week, the Leios team conducted comprehensive attack parameter analysis, released updated simulation tools, and performed detailed analysis of Cardano mainnet validation performance. The team successfully characterized the effectiveness of late-release attacks across different parameter ranges and established baseline performance metrics for ledger operations critical to proposed Leios implementation.

## Attack analysis and parameter optimization

### Parameter-sweep experiment for late-EB attacks

The team conducted a [comprehensive parameter-sweep experiment](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w33b/analysis.ipynb) to determine optimal adversarial strategies for late Endorser Block (EB) attacks. The experiment systematically varied EB delay timing from six to eight seconds with adversaries controlling 33% of stake, examining both diffusion parameter configurations (L_diff on/off) under the `txs-received` propagation scheme.

Critical findings from the parameter sweep analysis demonstrate that efficiency degradation begins when EBs and transactions are delayed 6.5 seconds, with minimal additional impact beyond 7-second delays. The analysis revealed that L_diff = 0s configurations perform better than L_diff = 7s under adversarial conditions. Importantly, none of the tested scenarios using `txs-received` propagation resulted in transaction loss or protocol breakdown, indicating robust behavior under these attack conditions.

## Simulation infrastructure improvements

### Rust simulation releases

The team released versions 1.1.0 and 1.2.0 of the Rust simulation infrastructure, incorporating updated transaction validation CPU models that improve accuracy of performance predictions. These releases enhance the fidelity of proposed Leios simulations and provide more reliable computational cost estimates for protocol analysis.

### Regression analysis framework

The team implemented a comprehensive [regression analysis framework](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/regression/) comparing behavior across all tagged versions of the Rust simulator `sim-cli`. This systematic approach enables rapid detection of behavioral changes in the simulator across development iterations, ensuring consistency and reliability in experimental results.

## Mainnet performance analysis

### Cardano mainnet validation timing analysis

The team extended the [analysis of ledger operations](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/timings/ReadMe.ipynb) with comprehensive linear statistical models predicting `Apply` and `Reapply` phases of ledger updates. These regressions provide crucial input for proposed Leios performance studies, particularly scenarios involving higher Plutus execution limits.

### Empty block diffusion analysis

The team completed [analysis of empty block diffusion](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/delta-header/analysis.ipynb) on Cardano mainnet using data from pooltool.io. This analysis establishes empirical estimates for the Δ_hdr parameter required by the proposed Leios protocol. The findings demonstrate that 94.0% of empty Praos blocks arrive at nodes within one second of their slot start time, providing critical timing constraints for protocol parameter selection.

## Next steps

- Continue refinement of attack resistance analysis based on parameter sweep findings
- Integrate updated CPU models into comprehensive protocol performance evaluations  
- Extend mainnet analysis to inform proposed Leios parameter optimization
- Prepare comprehensive attack analysis documentation for CIP inclusion.
