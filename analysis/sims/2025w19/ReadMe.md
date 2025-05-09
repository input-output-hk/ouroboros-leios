# Simulation experiments at tag `leios-2025w19`


## Workflow for running experiments

1. Copy the Haskell and Rust executables to this folder.
2. Excute `parallel --jobs=2 tps.list`.
3. Execute [combine-results.sh](combine-results.sh).
4. The results are in the `results/` folder.
5. Execute `nix run ..` to launch a Jupyter server.
6. Run Jupyter notebook [analysis.ipynb](analysis.ipynb).


## Archive of results

| Results             | 100-node network                                                             |
|---------------------|------------------------------------------------------------------------------|
| Resource usage      | https://leios-sim-output.s3.us-east-1.amazonaws.com/2025w19/resources.csv.gz | 
| Lifecycle analysis  | https://leios-sim-output.s3.us-east-1.amazonaws.com/2025w19/lifecycle.csv.gz | 


### Data dictionary


#### Resource usage

| Field                     | Units      | Type     | Description                                                                                   |
|---------------------------|------------|----------|-----------------------------------------------------------------------------------------------|
| simulator                 | -          | scenario | The name of the simulator used to run the experiment.                                         |
| label                     | -          | scenario | A string describing the experiment, in this case `default`.                                   |
| network                   | -          | scenario | A string describing the network, in this case `100 ` since the 100-node test network is used. |
| ib-generation-probability | #/s        | scenario | The rate of IB generation.                                                                    |
| ib-body-avg-size-bytes    | B          | scenario | The size of the IBs.                                                                          |
| eb-generation-probability | #/pipeline | scenario | The rate of EB generation.                                                                    |
| leios-stage-length-slots  | s          | scenario | The length of each pipeline stage.                                                            |
| node                      | -          | output   | The unique identifier for the node that performed the task.                                   |
| egress                    | B          | output   | The number of bytes leaving the node during the simulation.                                   |
| disk                      | B          | output   | The number of bytes stored to disk during the simulation.                                     |
| total\_cpu                | s          | output   | The total CPU consumed during the simulation.                                                 |
| maximum\_cpu              | %/100      | output   | The one-second average peak CPU fraction consumed during the simulation.                      |


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
