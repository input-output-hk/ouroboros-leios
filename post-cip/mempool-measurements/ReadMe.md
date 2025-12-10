# Empirical, anecdotal analysis of mainnet memory pool

This experiment collects data on the memory pool and blocks from instrumented nodes in three AWS regions.


## Artifacts

- [template.tar.gz](template.tar.gz): Configuration files for setting up the nodes.
- [fetch-logs.sh](fetch-logs.sh): Shell script for retrieving logs from the remote nodes.
- [process-log.sh](process-log.sh): Shell script for processing the raw logs into `.tsv` files.
- [process-log.sql](process-log.sql): SQL script for processing the raw logs into `.tsv` files.
- [analysis.ipynb](analysis.ipynb): Jupyter R notebook for analyzing and plotting the results.
