---
title: Weekly Summary – August 25, 2025
authors:
- will
tags: [progress, update, weekly, attack-experiments, bandwidth-analysis, cip-figures, proposed-leios, network-analysis]
---

This week, the Leios team refined attack analysis methodologies, conducted critical bandwidth limitation experiments, and updated simulation components for CIP documentation. The team successfully demonstrated proposed Leios behavior under constrained network conditions and validated attack experiment findings with improved simulation models.

## Attack analysis refinement

### Late-release attack validation

The team completed validation of the [late-release attack experiment](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/attack) using the latest version of the Rust simulation infrastructure. The rerun confirmed previous findings regarding adversarial impact on proposed Leios throughput, strengthening confidence in the protocol's characterized attack resistance properties under the tested scenarios.

### Enhanced CIP simulation experiments  

The [simulation experiment for CIP figures](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/cip/) received comprehensive updates with the latest Rust simulation version, incorporating several critical improvements. The enhanced experiments feature semi-optimal protocol parameter settings, improved assumptions for validation costs, and expanded exploration of increased Plutus execution step effects. These refinements provide more accurate performance predictions for CIP documentation.

## Network performance analysis

### Bandwidth limitation experiments

The team conducted comprehensive [bandwidth constraint analysis](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/bandwidth/analysis.ipynb) examining proposed Leios operation under severely constrained network conditions. The experiments systematically reduced inter-node bandwidth to values as low as 1 Mb/s to determine minimum network requirements for protocol viability.

Key findings demonstrate that proposed Leios operates successfully at 0.250 TxkB/s throughput even with constrained 2 Mb/s bandwidth between nodes. However, the protocol experiences breakdown at 1 Mb/s bandwidth limitations, establishing critical minimum network requirements for deployment scenarios. These results provide essential constraints for infrastructure planning and protocol parameter optimization.

## Simulation infrastructure enhancements

### Cross-simulation validation framework

The team expanded the regression analysis framework to systematically compare all tagged versions of the Rust simulator against consistent network topology and configuration parameters. This approach accelerates detection of behavioral changes across simulator versions and ensures consistent experimental foundations for protocol analysis.

### Updated validation models

Simulation infrastructure received updated transaction validation CPU models that improve accuracy of computational cost predictions. These enhanced models provide more reliable estimates for proposed Leios performance under various workload scenarios and support more precise parameter optimization for different deployment environments.

## Next steps

- Conduct comprehensive network topology degradation experiments  
- Extend bandwidth analysis to examine intermediate constraint levels
- Integrate improved validation models into CIP performance projections
- Finalize attack resistance documentation for formal CIP submission.
