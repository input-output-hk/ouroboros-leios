# Instructions for re-reunning simulation studies

These instructions are valid for the folders `2025w25/` and onwards.


## Recipe

### Running the simulation

1. Navigate to the folder for the study, for example `2025w31c/`.
2. Make sure to have the following tools installed: `yaml2json`, `jq` and `pigz`
    - *Nix:* use the default dev shell of the `sims/` flake `nix develop ..`
3. Copy or link the Rust simulator `sim-cli` executable to that folder.
    - If you want to reproduce the study, check out the git commit listed in the `sim-cli.hash` file.
    - Build with `cargo build --release` in the [sim-rs](../../sim-rs/) folder.
    - Link with `ln -s ../../../sim-rs/target/release/sim-cli` from the study folder.
4. Copy of link the Haskell `leios-trace-processor` executable to that folder.
    - *Cabal:* compile using `cabal build all`.
    - *Nix:* compile using `nix build ../..#leios-trace-processor && ln -s result/bin/leios-trace-processor`.
5. You can execute individual scenarios by executing the `run.sh` script in the relevant folder.
    - *Nix:* run `./run.sh`, which will automatically fetch the package dependencies.
    - *Without Nix:* run `bash run.sh`, but make sure you have the dependent tools already installled, which are listed in the first lines of `run.sh`.
6. The results folder will contain results:
    - `sim.log.gz`: the simulation log file, but with a few of the minor message types discarded.
    - `lifecycle.csv.gz`: transaction lifecycle results.
    - `resoruces.csv.gz`: resource usage results.
    - `receipts.csv.gz`: message diffusion results.
    - `cpus.csv.gz`: CPU usage results.
    - `sizes.csv.gz`: BLock size results.
7. You can also run several simulations at once using the `parallel` command-line tool.

### Combining the results

8. Execute the `combine-results.sh` script to bundle the results from multiple runs into the `results/` folder.
    - *Nix:* run `./combine-results.sh`.
    - *Without nix:* run `bash combine-results.sh` after installing the required dependencies.
  
### Plot the results in Jupyter

9. Start a Jupter notebook server using the command `nix run #../sims/`.
10. In the web browser, navigate to the relevant experiment folder and open any `.ipynb` files of interest.


## Data dictionary


### Lifecycle analysis

| Field       | Units | Type             | Description
|-------------|-------|------------------|----------------------------------------------------------------------------------------|
| /scenario/  | -     | input            | Multiple columns defining the scearion.                                                |
| Kind        | -     | output           | The kind of item: `IB`, `EB`, `RB`, or `VT`.                                           |
| Item        | -     | output           | The identifier for the item.                                                           |
| Size [B]    | B     | output           | The size of the item.                                                                  |
| References  | -     | output           | The number of times the TX, IB, or EB is referenced by an IB, EB, or EB, respectively. |
| Created [s] | s     | output           | When the item was created.                                                             |
| To IB [s]   | s     | output           | When the item was first included in an IB.                                             |
| To EB [s]   | s     | output           | When the item was first referenced by an EB.                                           |
| To RB [s]   | s     | output           | When the item was first referenced by an RB.                                           |
| In RB [s]   | s     | output           | When the transaction was first included in an RB.                                      |


### Resource usage

| Field                     | Units      | Type     | Description                                                                                   |
|---------------------------|------------|----------|-----------------------------------------------------------------------------------------------|
| /scenario/                | -          | input    | Multiple columns defining the scearion.                                                       |
| Node                      | -          | output   | The unique identifier for the node that performed the task.                                   |
| Egress [B]                | B          | output   | The number of bytes leaving the node during the simulation.                                   |
| Disk [B]                  | B          | output   | The number of bytes stored to disk during the simulation.                                     |
| Total CPU [s]             | s          | output   | The total CPU consumed during the simulation.                                                 |
| Maximum CPU [s/s]         | %/100      | output   | The one-second average peak CPU fraction consumed during the simulation.                      |


### Receipt of messages

| Field                     | Units | Type     | Description                                                                                   |
|---------------------------|-------|----------|-----------------------------------------------------------------------------------------------|
| /scenario/                | -     | input    | Multiple columns defining the scearion.                                                       |
| Kind                      | -     | output   | The kind of item: `IB`, `EB`, `RB`, or `VT`.                                                  |
| Item                      | -     | output   | The unique identifier for the item.                                                           |
| Producer                  | -     | output   | The unique identifier for the node that generated the item.                                   |
| Generated [s]             | s     | output   | When the item was generated.                                                                  |
| Size [B]                  | B     | output   | The size of the item.                                                                         |
| Recipient                 | -     | output   | The unique identifier for the node that received the item.                                    |
| Received [s]              | s     | output   | The time when the item was received.                                                          |
| Elapsed [s]               | s     | output   | The time elapsed between when the item was originally sent by the producer and then received. |


### CPU usage

| Field                     | Units | Type     | Description                                                                                   |
|---------------------------|-------|----------|-----------------------------------------------------------------------------------------------|
| /scenario/                | -     | input    | Multiple columns defining the scearion.                                                       |
| Slot                      | s     | output   | The slot number when the task *started*.                                                      |
| Node                      | -     | output   | The unique identifier for the node that performed the task.                                   |
| Task                      | -     | output   | The abbreviation for the task that was performed.                                             |
| Duration [s]              | s     | output   | The number of seconds of vCPU usage for the task.                                             |


### Block size

| Field                     | Units | Type     | Description                                                                                   |
|---------------------------|-------|----------|-----------------------------------------------------------------------------------------------|
| /scenario/                | -     | input    | Multiple columns defining the scearion.                                                       |
| Kind                      | -     | output   | The kind of block: `IB`, `EB`, or `RB`.                                                       |
| Item                      | -     | output   | The unique identifier for the block.                                                          |
| Generated [s]             | s     | output   | When the block was generated.                                                                 |
| Transactions              | -     | output   | Number of transactions directly referenced by the block.                                      |
| Endorses                  | -     | output   | The unique identifier for the item that the block endorses.                                   |
