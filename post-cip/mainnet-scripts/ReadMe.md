# Statistics for Plutus usage on Cardano mainnet


## Method

The script [redeemer-stats.sql](./redeemer-stats.sql) was executed on a `cardano-db-sync` database for Cardano `mainnet`.


## Data files

- [redeemer-stats.csv.gz](./redeemer-stats.csv.gz): full dataset
- [redeemer-stats-top100.csv](./redeemer-stats-top100.csv): 100 most-used scripts


## Data dictionary

| Field               | Description                                                         |
|---------------------|---------------------------------------------------------------------|
| `script_hash`       | The hash of the Plutus script.                                      |
| `purpose`           | The purpose of the Plutus script.                                   |
| `redeemer_count`    | The number of times the script has been executed.                   |
| `mem_avg`           | The average number of Plutus memory usits per execution.            |
| `steps_avg`         | The average number of Plutus step units per execution.              |
| `redeemer_fraction` | Fraction of executions of this script out of all Plutus executions. |
| `mem_fraction`      | Fraction of Plutus memory units out of all Plutus executions.       |
| `steps_fraction`    | Fraction of Plutus step units out of all Plutus executions.         |
