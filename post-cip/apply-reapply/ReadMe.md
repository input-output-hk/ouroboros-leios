# Re-analysis of ledger apply/reapply operations on mainnet

Deepened analysis of the `db-analyser` output on the `Apply` and `Reapply` operations for the Cardano mainnet ledger.

## Measurements

The Jupyter notebook [post-cip/apply-reapply/analysis.ipynb](../post-cip/apply-reapply/analysis.ipynb) analyzes `db-analyser` measurements for Cardano `mainnet`. Linear models and quantile regressions were applied to the dataset in order to estimate how CPU resources scale with block size, transaction count, number of transaction inputs, and number of Plutus steps. These results can be used for reasoning about feasible values of Leios protocol parameters.

Regarding Plutus, nominally, one step unit corresponds to one picosecond on the benchmark machine and one memory unit corresponds to eight bytes allocated on that machine. The following plots show the relationship between execution steps and CPU on the machine where the `db-analyser` experiment was conducted.

| Plutus steps vs CPU usage                                         | CPU usage per Plutus step                                       |
| ----------------------------------------------------------------- | --------------------------------------------------------------- |
| ![CPU usage vs Plutus steps](./steps-picoseconds-scatterplot.png) | ![CPU usage per Plutus step](./steps-picoseconds-histogram.png) |

## Regression model

The db-analyser is very noisy and hard to fit. Nevertheless, here are the best fits obtained using linear models and the quantile regression. Note that the quantile regression was based on a random subset of the data because it is not computationally feasible to perform quantile regression on such a large dataset in a reasonable amount of time.

| Regression      | Dependent variable |   Block size | Number of transactions | Number of transaction inputs | Number of Plutus steps |
| --------------- | ------------------ | -----------: | ---------------------: | ---------------------------: | ---------------------: |
| Simple ratio    | `Apply - Reapply`  |              |                        |                              |          `1.5 ps/step` |
| Linear model    | `Apply - Reapply`  | `4.7e4 ps/B` |          `1.2e8 ps/tx` |              `8.0e3 ps/txin` |         `0.61 ps/step` |
|                 | `Reapply`          | `2.8e3 ps/B` |          `3.5e7 ps/tx` |              `5.2e6 ps/txin` |                        |
|                 | `Apply`            | `4.8e4 ps/B` |          `1.6e8 ps/tx` |              `1.3e7 ps/txin` |         `0.63 ps/step` |
| 75th percentile | `Apply - Reapply`  | `1.6e4 ps/B` |          `1.7e8 ps/tx` |              `1.8e7 ps/txin` |         `0.96 ps/step` |
|                 | `Reapply`          | `1.7e3 ps/B` |          `4.2e7 ps/tx` |              `5.7e6 ps/txin` |                        |
|                 | `Apply`            | `1.6e4 ps/B` |          `2.2e8 ps/tx` |              `2.3e7 ps/txin` |         `0.97 ps/step` |

Coarsely, the "one picosecond per Plutus step" is a reasonable estimate for Plutus costs; we did not assess whether "eight bytes per Plutus memory unit" was also reasonable.

## Artifacts

- [ledger-ops.sql](ledger-ops.sql): SQL script for merging measurements with ledger information.
- [analysis.ipynb](analysis.ipynb): Jupyter R notebook for analyzing data and plotting results.
