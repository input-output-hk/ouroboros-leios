---
title: Weekly Summary – July 14, 2025
authors:
- will
tags: [progress, update, weekly, validation-analysis, simulation-optimization, trace-processor, linear-leios, stracciatella]
---

This week, the Leios team focused on improving simulation analysis, conducting validation time studies, and working on comprehensive protocol variant experiments. The team developed new analysis tools, conducted fundamental performance studies of Cardano validation times, and completed extensive mapping of Linear Leios protocol performance under various conditions.

## Analysis tools and infrastructure

### Generic trace analysis framework

- Developed a generic analysis script for processing Leios simulator output
- Created a comprehensive R-based analysis pipeline generating diagnostic plots from `leios-simulation-trace-processor` output
- Enhanced analysis capabilities for systematic evaluation of simulation results
- Documentation and usage instructions are available in the [trace processor README](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/trace-processor/ReadMe.md).

## Validation performance analysis

### Cardano mainnet validation timing study

- Completed a preliminary analysis of block and transaction validation times for Cardano mainnet since epoch 350
- Key findings using the `db-analyser` tool include:
  - Median transaction signature verification: 0.53 ms/tx
  - Median validation time per kilobyte: 0.29 ms/kB  
  - Joint linear model estimate: 0.066 ms/tx plus 0.221 ms/kB
  - Data suitable for bulk estimates but too noisy for individual transaction predictions
- Identified missing explanatory variables (UTXO set size, input/output counts) extractable from the ledger or `cardano-db-sync`
- Results provide a foundation for more accurate simulator validation time modeling
- Detailed analysis is available in the [validation timing notebook](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/timings/preliminary.ipynb).

## Simulation optimization studies

### Timestep resolution analysis

- Conducted a comparative study of simulation timestep effects at 1,000 TPS Full Leios scenarios
- Compared 0.100 ms and 0.025 ms time resolutions with no significant differences in results
- Validated the use of coarser timesteps for improved parallelism and reduced simulation runtime
- Supporting analysis and evidence are available in the [timestep study notebook](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w27/analysis.ipynb).

## Protocol variant experiments

### Mid-throughput protocol validation

- Completed 100 TPS experiments for Stracciatella and Linear Leios variants using 1,400 B/tx over 900 seconds
- Key findings include:
  - 5 slots/stages are insufficient for Linear Leios at 100 tx/s
  - Including transactions in EBs causes congestion compared to transaction references
  - 10 MB/EB is required for 100 tx/s performance (5 MB/EB is insufficient)
  - EB-sortition unluckiness in Stracciatella extends the transaction lifecycle but can be mitigated
  - CPU and network peaks occur when transactions are embedded in EBs
- Analysis artifacts are available in [100 TPS experiment documentation](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w29b/ReadMe.pdf) and the [analysis notebook](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w29b/analysis.ipynb).

### Comprehensive Linear Leios performance mapping

- Completed an extensive simulation study mapping Linear Leios performance under various loads and configurations
- Compared multiple Linear Leios variants against the Stracciatella baseline
- Generated comprehensive performance characterizations across different throughput scenarios
- Results are documented in the [Linear Leios summary](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w29/summary.pdf) with variant-specific analysis:
  - [Linear Leios with embedded transactions](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w29/linear.ipynb)
  - [Linear Leios with transaction references](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w29/txrefs.ipynb)
  - [Linear Leios without transactions](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w29/notxs.ipynb)
  - [Stracciatella baseline comparison](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w29/stracciatella.ipynb).

## Simulation model refinements

- Revised the Linear Leios model based on analysis findings, particularly regarding partial EB validation before peer propagation
- Reimplemented Stracciatella as a separate simulation to identify specification deviations
- Identified and resolved multiple implementation inconsistencies during the specification verification process.

## Next steps

- Continue developing analysis infrastructure for systematic protocol evaluation
- Integrate improved validation timing models into simulation configurations
- Expand protocol variant testing based on performance mapping results
- Refine simulation models for enhanced accuracy and specification compliance.
