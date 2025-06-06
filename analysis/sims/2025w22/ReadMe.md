# Simulation experiments at tag `leios-2025w22`

- Rust simulator (since Haskell does not model transactions)
- 100-node topology
- 8 vCPUs / node
- 10 slot / stage
- 3 slot / shard period
- 10 shard / group
- 1.5 EB/stage
- 1, 3, 10, 30, 100, 300 tx/s
- IB generation probability varies with TPS
- Number of shards ⪅ (IB rate) x (shards per group) x (slots per slot period)
- 327,680 B/IB maximum
- No unsharded transactions


## Workflow for running experiments

1. Copy the Haskell and Rust executables to this folder.
2. Excute `parallel --jobs=2 tps.list`.
3. Execute [combine-results.sh](combine-results.sh).
4. The results are in the `results/` folder.
5. Execute `nix run ..` to launch a Jupyter server.
6. Run Jupyter notebook [analysis.ipynb](analysis.ipynb).


## Summary of results

- [1 TPS](tps3x/1/summary.txt)
- [3 TPS](tps3x/3/summary.txt)
- [10 TPS](tps3x/10/summary.txt)
- [30 TPS](tps3x/30/summary.txt)
- [100 TPS](tps3x/100/summary.txt)
- [300 TPS](tps3x/300/summary.txt)


## Archive of results

| Results                           | 100-node network                                                               |
|-----------------------------------|--------------------------------------------------------------------------------|
| Lifecycle analysis at 3x capacity | https://leios-sim-output.s3.us-east-1.amazonaws.com/2025w20/lifecycle.csv.gz | 


### Data dictionary


#### Lifecycle analysis

| Field       | Units | Type             | Description
|-------------|-------|------------------|----------------------------------------------------------------------------------------|
| simulator   | -     | scenario         | The name of the simulator used to run the experiment.                                  |
| tps         | tx/s  | scenario         | The number of transactions submitted per second.                                       |
| Kind        | -     | output           | The kind of item (TX, IB, EB, RB).                                                     |
| Item        | -     | output           | The identifier for the item.                                                           |
| Size [B]    | B     | output           | The size of the item.                                                                  |
| References  | -     | output           | The number of times the TX, IB, or EB is referenced by an IB, EB, or EB, respectively. |
| Created [s] | s     | output           | When the item was created.                                                             |
| To IB [s]   | s     | output           | When the item was first included in an IB.                                             |
| To EB [s]   | s     | output           | When the item was first referenced by an EB.                                           |
| To RB [s]   | s     | output           | When the item was first referenced by an RB.                                           |
| In RB [s]   | s     | output           | When the transaction was first included in an RB.                                      |
