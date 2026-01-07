# Empirical distribution of block and transaction metrics

The following data describes the joint empirical distribution for several key block- and transaction-related metrics for Cardano `mainnet` since Epoch 350. The data for the metrics is binned in several dimensions, one per metrics, and the `Fraction of ...` field indicates how many observations fell in each bin. The binning process preserves both the marginal and join distribution of the observations. If any dimensions are not of interest, they can be summed over in order to create a lower-dimensional joint distribution.

Monte-carlo simulations need only sample according to the `Fraction of ...` field in order randomly select metrics. Similarly, the empirical distribution can be directly input into Delta-QSD models.


## Blocks: [block-edf.csv](./block-edf.csv)

| Field                      | Description                                                                |
|----------------------------|----------------------------------------------------------------------------|
| Tx count                   | Number of transactions in blocks in this bin.                              |
| Block size [kB]            | Mean size for blocks in this bin.                                          |
| Apply [ms]                 | Mean `apply_mux` measurement from `db-analyser` for blocks in this bin.    |
| Reapply [ms]               | Mean `reapply_muxn` measurement from `db-analyser` for blocks in this bin. |
| Fraction of blocks [%/100] | Fraction of the blocks observed since Epoch 350 that fall in this bin.     |


## Transactions: [tx-edf.csv](./tx-edf.csv)

| Field                   | Description                                                                  |
|-------------------------|------------------------------------------------------------------------------|
| Tx size [kB]            | Mean size for transactions in this bin.                                      |
| Plutus steps [ms]       | Mean Plutus execution units for transactions in this bin.                    |
| Fraction of txs [%/100] | Fraction of the transactions observed since Epoch 350 that fall in this bin. |

