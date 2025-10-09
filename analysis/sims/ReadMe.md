# Simulation studies

Contents

- [Building the tools](#building-the-tools)
- [Running the simulators](#running-the-simulators)
- [Running the trace processor](#running-the-trace-processor)
- [Index of simulation studies](#index-of-simulation-studies)
- [Re-reunning simulation studies](#re-reunning-simulation-studies)


## Building the tools


### Haskell simulator

Instructions for building the Haskell simulator `ols` are availabe in [/simulation/](../../simulator/README.md).


### Rust simulator

Instructions for building the Rust simulator `sim-cli` are available in [/sim-rs/](../../sim-rs/README.md).


### Building the trace processor

Instructions for building the trace process `leios-trace-processor` are available in [/analysis/sims/trace-processor/](../../analysis/sims/trace-processor/ReadMe.md).


## Running the simulators

Both the Haskell and the Rust simulators read compatible input files (the [configuration file](#configuration-file) and the [network topology file](#network-topology-file), but their command-line flags differ.

The simulators output events in JSONL or CBOR format. The output schemas of the two simulators differ somewhat but they coincide for the most useful events.

Note that the Rust simulator is multi-threaded and runs much faster than the single-threaded Haskell simulator.


### Configuration file

- Default: [/data/simulation/config.default.yaml](../../data/simulation/config.default.yaml)
- Schema: [/data/simulation/schema.schema.json](../../data/simulation/schema.schema.json)
- Typescript definition: [/data/simulation/config.d.ts](../../data/simulation/config.d.ts)


### Network topology file

- 100-node, stressful topology: [/data/simulation/topo-default-100.yaml](/data/simulation/topo-default-100.yaml)
- Mainnet variants
    - Largest, 10k nodes, "pseudo-mainnet": [/data/simulation/pseudo-mainnet/topology-v1.yaml](../../data/simulation/pseudo-mainnet/topology-v1.yaml)
    - Most useful, 750 nodes, "mini-mainnet": [/data/simulation/pseudo-mainnet/topology-v2.yaml](../../data/simulation/pseudo-mainnet/topology-v2.yaml)
    - Small, for Haskell simulator, 100 nodes, "micro-mainnet": [/data/simulation/pseudo-mainnet/topology-v3.yaml](/data/simulation/pseudo-mainnet/topology-v3.yaml)

A network generation tool is also available.


### Running a Haskell simulation

Supply the path the configuration and topology files and specify the number of slots to run.

```bash
  ols --output-seconds 1200 --leios-config-file my-config.yaml --topology-file my-network.yaml --output-file sim.log
```

```console
$ ols sim leios --help

Usage: ols sim leios [--seed NUMBER] [-l|--leios-config-file FILE] 
                     [(-t|--topology-file FILE) | 
                       (--tg|--topology-generation-strategy-file FILE) | 
                       COMMAND] [--log-verbosity NUMBER] [--analize] 
                     [--shared-log-format OUTPUT] [--conformance-events]

  Leios simulation.

Available options:
  --seed NUMBER            The seed for the random number generator.
                           (default: 0)
  -l,--leios-config-file FILE
                           File containing the configuration values for the
                           Leios simulation.
  -t,--topology-file FILE  A topology file describing the world topology.
  --tg,--topology-generation-strategy-file FILE
                           A file describing the topology generation strategy.
  --log-verbosity NUMBER   0: no log; 1: major events; 2: debug; 3: all.
                           (default: 1)
  --analize                Calculate metrics and statistics.
  --shared-log-format OUTPUT
                           Log format documented in trace.haskell.d.ts. OUTPUT
                           can be `CBOR` or `JSON`.
  --conformance-events     Emits `Slot` and `No*Generated` events in the shared
                           log format.
  -h,--help                Show this help text

Available topology generation strategies:
  close-and-random         Pick links to close and random nodes.

Global options:
  --output-seconds SECONDS Output N seconds of simulation. (default: 40)
  --output-file FILE       Output simulation data to file.
  --skip-triangle-inequality-check
                           Do not check the topology's latencies for the
                           triangle inequality.
```


### Running a Rust simulation

Supply the path the configuration and topology files and specify the number of slots to run.

```bash
sim-cli --slots 1200 --parameters my-config.yaml my-network.yaml sim.log
```

```console
$ sim-cli --help
Usage: sim-cli [OPTIONS] [TOPOLOGY] [OUTPUT]

Arguments:
  [TOPOLOGY]  
  [OUTPUT]    

Options:
  -p, --parameters <PARAMETERS>  
  -t, --timescale <TIMESCALE>    
      --trace-node <TRACE_NODE>  
  -s, --slots <SLOTS>            
  -c, --conformance-events       
  -a, --aggregate-events         
  -h, --help                     Print help
  -V, --version                  Print version
```


## Running the trace processor

The trace processor summarizes key information from the JSONL output logs into convenient CSV tables. Alternatively, tools like `jq` or `mongodb` can be used to query a simulation output file.

```bash
zcat sim.log.gz | leios-trace-processor --lifecycle-file lifecycle.csv --cpu-file cpu.csv --resource-file resource.csv --receipt-file receipt.csv
```

```console
leios-trace-processor --help
Process Leios trace logs into CSV file abstracts

Usage: leios-trace-processor [--trace-file FILE] --lifecycle-file FILE
                             --cpu-file FILE --resource-file FILE
                             --receipt-file FILE

  Leios trace processor

Available options:
  --trace-file FILE        Input Leios simulation trace log file
  --lifecycle-file FILE    Output CSV file for transaction lifecycle data
  --cpu-file FILE          Output CSV file for CPU data
  --resource-file FILE     Output CSV file for resource data
  --receipt-file FILE      Output CSV file for receipt data
  -h,--help                Show this help text
```


### Data dictionary


#### Lifecycle analysis

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


#### Resource usage

| Field                     | Units      | Type     | Description                                                                                   |
|---------------------------|------------|----------|-----------------------------------------------------------------------------------------------|
| /scenario/                | -          | input    | Multiple columns defining the scearion.                                                       |
| Node                      | -          | output   | The unique identifier for the node that performed the task.                                   |
| Egress [B]                | B          | output   | The number of bytes leaving the node during the simulation.                                   |
| Disk [B]                  | B          | output   | The number of bytes stored to disk during the simulation.                                     |
| Total CPU [s]             | s          | output   | The total CPU consumed during the simulation.                                                 |
| Maximum CPU [s/s]         | %/100      | output   | The one-second average peak CPU fraction consumed during the simulation.                      |


#### Receipt of messages

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


#### CPU usage

| Field                     | Units | Type     | Description                                                                                   |
|---------------------------|-------|----------|-----------------------------------------------------------------------------------------------|
| /scenario/                | -     | input    | Multiple columns defining the scearion.                                                       |
| Slot                      | s     | output   | The slot number when the task *started*.                                                      |
| Node                      | -     | output   | The unique identifier for the node that performed the task.                                   |
| Task                      | -     | output   | The abbreviation for the task that was performed.                                             |
| Duration [s]              | s     | output   | The number of seconds of vCPU usage for the task.                                             |


#### Block size

| Field                     | Units | Type     | Description                                                                                   |
|---------------------------|-------|----------|-----------------------------------------------------------------------------------------------|
| /scenario/                | -     | input    | Multiple columns defining the scearion.                                                       |
| Kind                      | -     | output   | The kind of block: `IB`, `EB`, or `RB`.                                                       |
| Item                      | -     | output   | The unique identifier for the block.                                                          |
| Generated [s]             | s     | output   | When the block was generated.                                                                 |
| Transactions              | -     | output   | Number of transactions directly referenced by the block.                                      |
| Endorses                  | -     | output   | The unique identifier for the item that the block endorses.                                   |


## Index of simulation studies

The [Simulation Experiments section of the second technical report](../../docs/technical-report-2.md#simulation-experiments) lists each simulation experiment, provides a link to its folder of artifacts, and summarizes its findings.


## Re-reunning simulation studies

These instructions are valid for the folders `2025w25/` and onwards. Earlier folders are not as automated.

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
