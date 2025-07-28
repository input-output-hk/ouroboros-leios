---
title: Weekly Summary – July 14, 2025
authors:
- will
tags: [progress, update, weekly, validation-analysis, simulation-optimization, trace-processor, linear-leios, stracciatella]
---

This week, the Leios team focused on simulation analysis improvements, validation time studies, and comprehensive protocol variant experiments. The team developed new analysis tools, conducted fundamental performance studies of Cardano validation times, and completed extensive mapping of Linear Leios protocol performance under various conditions.

## Analysis tools and infrastructure

### Generic trace analysis framework

- Developed a generic analysis script for processing Leios simulator output
- Created comprehensive R-based analysis pipeline generating diagnostic plots from `leios-simulation-trace-processor` output
- Enhanced analysis capabilities for systematic evaluation of simulation results
- Documentation and usage instructions available in the [trace processor README](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/trace-processor/ReadMe.md).

## Validation performance analysis

### Cardano mainnet validation timing study

- Completed preliminary analysis of block and transaction validation times for Cardano mainnet since Epoch 350
- Key findings using `db-analyser` tool:
  - Median transaction signature verification: 0.53 ms/tx
  - Median validation time per kilobyte: 0.29 ms/kB  
  - Joint linear model estimate: 0.066 ms/tx plus 0.221 ms/kB
  - Data suitable for bulk estimates but too noisy for individual transaction predictions
- Identified missing explanatory variables (UTxO set size, input/output counts) extractable from ledger or `cardano-db-sync`
- Results provide foundation for more accurate simulator validation time modeling
- Detailed analysis available in the [validation timing notebook](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/timings/preliminary.ipynb).

## Simulation optimization studies

### Timestep resolution analysis

- Conducted comparative study of simulation timestep effects at 1000 TPS Full Leios scenarios
- Compared 0.100 ms and 0.025 ms time resolutions with no significant differences in results
- Validated use of coarser timesteps for improved parallelism and reduced simulation runtime
- Supporting analysis and evidence in the [timestep study notebook](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w27/analysis.ipynb).

## Protocol variant experiments

### Mid-throughput protocol validation

- Completed 100 TPS experiments for Stracciatella and Linear Leios variants using 1400 B/tx over 900 seconds
- Key findings:
  - 5 slot/stage insufficient for Linear Leios at 100 tx/s
  - Including transactions in EBs causes congestion compared to transaction references
  - 10 MB/EB required for 100 tx/s performance (5 MB/EB insufficient)
  - EB-sortition unluckiness in Stracciatella extends transaction lifecycle but can be mitigated
  - CPU and network peaks occur when transactions are embedded in EBs
- Analysis artifacts available in [100 TPS experiment documentation](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w29b/ReadMe.pdf) and [analysis notebook](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w29b/analysis.ipynb).

### Comprehensive Linear Leios performance mapping

- Completed extensive simulation study mapping Linear Leios performance under various loads and configurations
- Compared multiple Linear Leios variants against Stracciatella baseline
- Generated comprehensive performance characterizations across different throughput scenarios
- Results documented in [Linear Leios summary](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w29/summary.pdf) with variant-specific analysis:
  - [Linear Leios with embedded transactions](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w29/linear.ipynb)
  - [Linear Leios with transaction references](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w29/txrefs.ipynb)
  - [Linear Leios without transactions](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w29/notxs.ipynb)
  - [Stracciatella baseline comparison](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w29/stracciatella.ipynb).

## Simulation model refinements

- Revised Linear Leios model based on analysis findings, particularly regarding partial EB validation before peer propagation
- Reimplemented Stracciatella as separate simulation to identify specification deviations
- Identified and resolved multiple implementation inconsistencies during specification verification process.

## Next steps

- Continue development of analysis infrastructure for systematic protocol evaluation
- Integrate improved validation timing models into simulation configurations
- Expand protocol variant testing based on performance mapping results
- Refine simulation models for enhanced accuracy and specification compliance.
