# Ouroboros Leios

This repository is home of the _Leios R&D project_ whose purpose is to define a specification of the Ouroboros Leios protocol.

This project aims to address the challenges outlined in [CPS-0018](https://github.com/cardano-foundation/CIPs/blob/master/CPS-0018/README.md), which focuses on improving transaction throughput in the Cardano network.

> [!CAUTION]
> This project is in its very early stage and is mostly
> experimental and exploratory. All contributions and feedbacks are
> welcome. No warranties of any kind about the current or future
> features of Cardano are to be expected, implicitly and explicitly.

## Getting started

Checkout [CONTRIBUTING.md](CONTRIBUTING.md) document for possible contributions and communication channels

More documentation about Leios can be found in the [web site](https://leios.cardano-scaling.org).

## Repository Structure

- [Logbook](Logbook.md) contains a detailed account of
  problems,successes, failures, ideas, references and is intended as a
  tool to help the team members stay in sync. It's updated frequently
  with notes about the day-to-day work, meetings, ideas, etc.
- [data](data) contains common input files, schemas, and default configurations used by both simulations
- [deltaQ](deltaQ) contains network quality analysis tools and measurements
- [simulation](simulation) contains experimental Haskell code to simulate the Leios protocol, including built-in visualization capabilities
- [sim-rs](sim-rs) contains experimental Rust code to simulate the Leios protocol
- [ui](ui) contains the web-based visualization tool for the Rust simulation traces
- [site](site) contains the sources of the aforementioned web site


## Simulations

Both the Haskell and Rust simulations read in a network topology file that defines the nodes and their connections, along with a configuration file that controls various protocol parameters. The simulations then produce trace outputs that can be visualized to analyze the protocol's behavior. The Haskell simulation includes built-in visualization capabilities, while the Rust simulation generates JSONL traces that can be visualized using the web UI in the `ui` directory.

### Configuration Parameters

The Leios simulations (both Rust and Haskell) can be configured using YAML configuration files. The configuration schema is defined in [data/simulation/config.d.ts](data/simulation/config.d.ts) and the default configuration is available in [data/simulation/config.default.yaml](data/simulation/config.default.yaml).

Each parameter controls a specific aspect of the simulation, and some parameters are only supported by either the Rust or Haskell implementation:

### Simulation Configuration

| Parameter | Description | Haskell | Rust |
|-----------|-------------|:-------:|:----:|
| `relay-strategy` | Strategy for relaying blocks | ✅ | ✅ |
| `tcp-congestion-control` | Enable TCP congestion control | ✅ | ❌ |
| `multiplex-mini-protocols` | Enable multiplexing of mini-protocols | ✅ | ❌ |
| `simulate-transactions` | Enable transaction simulation | ❌ | ✅ |
| `treat-blocks-as-full` | Calculate delays and message sizes as if blocks were full | ✅ | ❌ |
| `cleanup-policies` | Policies for cleaning up expired data | ✅ | ❌ |

### Leios Protocol Configuration

| Parameter | Description | Haskell | Rust |
|-----------|-------------|:-------:|:----:|
| `leios-stage-length-slots` | Number of slots in a Leios stage | ✅ | ✅ |
| `leios-stage-active-voting-slots` | Number of slots for active voting | ✅ | ✅ |
| `leios-vote-send-recv-stages` | Whether to separate Vote Send and Vote Receive stages | ✅ | ❌ |

### Transaction Configuration

| Parameter | Description | Haskell | Rust |
|-----------|-------------|:-------:|:----:|
| `tx-generation-distribution` | Distribution for transaction generation | ❌ | ✅ |
| `tx-size-bytes-distribution` | Distribution for transaction sizes | ❌ | ✅ |
| `tx-validation-cpu-time-ms` | CPU time for transaction validation | ❌ | ✅ |
| `tx-max-size-bytes` | Maximum transaction size | ❌ | ✅ |

### Ranking Block Configuration

| Parameter | Description | Haskell | Rust |
|-----------|-------------|:-------:|:----:|
| `rb-generation-probability` | Probability of generating a ranking block | ✅ | ✅ |
| `rb-generation-cpu-time-ms` | CPU time for generating a ranking block | ✅ | ✅ |
| `rb-head-validation-cpu-time-ms` | CPU time for validating a ranking block header | ✅ | ✅ |
| `rb-head-size-bytes` | Size of a ranking block header | ✅ | ✅ |
| `rb-body-max-size-bytes` | Maximum size of a ranking block body | ✅ | ✅ |
| `rb-body-legacy-praos-payload-validation-cpu-time-ms-constant` | Constant CPU time for validating legacy Praos payload | ✅ | ✅ |
| `rb-body-legacy-praos-payload-validation-cpu-time-ms-per-byte` | Per-byte CPU time for validating legacy Praos payload | ✅ | ✅ |
| `rb-body-legacy-praos-payload-avg-size-bytes` | Average size of legacy Praos payload | ✅ | ❌ |

### Input Block Configuration

| Parameter | Description | Haskell | Rust |
|-----------|-------------|:-------:|:----:|
| `ib-generation-probability` | Probability of generating an input block | ✅ | ✅ |
| `ib-generation-cpu-time-ms` | CPU time for generating an input block | ✅ | ✅ |
| `ib-shards` | Number of shards for input blocks | ❌ | ✅ |
| `ib-head-size-bytes` | Size of an input block header | ✅ | ✅ |
| `ib-head-validation-cpu-time-ms` | CPU time for validating an input block header | ✅ | ✅ |
| `ib-body-validation-cpu-time-ms-constant` | Constant CPU time for validating an input block body | ✅ | ✅ |
| `ib-body-validation-cpu-time-ms-per-byte` | Per-byte CPU time for validating an input block body | ✅ | ✅ |
| `ib-body-avg-size-bytes` | Average size of an input block body | ✅ | ❌ |
| `ib-body-max-size-bytes` | Maximum size of an input block body | ❌ | ✅ |
| `ib-diffusion-strategy` | Strategy for diffusing input blocks | ✅ | ✅ |
| `ib-diffusion-max-window-size` | Maximum window size for input block diffusion | ✅ | ❌ |
| `ib-diffusion-max-headers-to-request` | Maximum number of headers to request for input blocks | ✅ | ❌ |
| `ib-diffusion-max-bodies-to-request` | Maximum number of bodies to request for input blocks | ✅ | ❌ |

### Endorsement Block Configuration

| Parameter | Description | Haskell | Rust |
|-----------|-------------|:-------:|:----:|
| `eb-generation-probability` | Probability of generating an endorsement block | ✅ | ✅ |
| `eb-generation-cpu-time-ms` | CPU time for generating an endorsement block | ✅ | ✅ |
| `eb-validation-cpu-time-ms` | CPU time for validating an endorsement block | ✅ | ✅ |
| `eb-size-bytes-constant` | Constant size of an endorsement block | ✅ | ✅ |
| `eb-size-bytes-per-ib` | Per-input-block size of an endorsement block | ✅ | ✅ |
| `eb-diffusion-strategy` | Strategy for diffusing endorsement blocks | ✅ | ❌ |
| `eb-diffusion-max-window-size` | Maximum window size for endorsement block diffusion | ✅ | ❌ |
| `eb-diffusion-max-headers-to-request` | Maximum number of headers to request for endorsement blocks | ✅ | ❌ |
| `eb-diffusion-max-bodies-to-request` | Maximum number of bodies to request for endorsement blocks | ✅ | ❌ |

### Vote Configuration

| Parameter | Description | Haskell | Rust |
|-----------|-------------|:-------:|:----:|
| `vote-generation-probability` | Probability of generating a vote | ✅ | ✅ |
| `vote-generation-cpu-time-ms-constant` | Constant CPU time for generating a vote | ✅ | ✅ |
| `vote-generation-cpu-time-ms-per-ib` | Per-input-block CPU time for generating a vote | ✅ | ✅ |
| `vote-validation-cpu-time-ms` | CPU time for validating a vote | ✅ | ✅ |
| `vote-threshold` | Threshold for vote acceptance | ✅ | ✅ |
| `vote-bundle-size-bytes-constant` | Constant size of a vote bundle | ✅ | ✅ |
| `vote-bundle-size-bytes-per-eb` | Per-endorsement-block size of a vote bundle | ✅ | ✅ |
| `vote-diffusion-strategy` | Strategy for diffusing votes | ✅ | ❌ |
| `vote-diffusion-max-window-size` | Maximum window size for vote diffusion | ✅ | ❌ |
| `vote-diffusion-max-headers-to-request` | Maximum number of headers to request for votes | ✅ | ❌ |
| `vote-diffusion-max-bodies-to-request` | Maximum number of bodies to request for votes | ✅ | ❌ |

### Certificate Configuration

| Parameter | Description | Haskell | Rust |
|-----------|-------------|:-------:|:----:|
| `cert-generation-cpu-time-ms-constant` | Constant CPU time for generating a certificate | ✅ | ✅ |
| `cert-generation-cpu-time-ms-per-node` | Per-node CPU time for generating a certificate | ✅ | ✅ |
| `cert-validation-cpu-time-ms-constant` | Constant CPU time for validating a certificate | ✅ | ✅ |
| `cert-validation-cpu-time-ms-per-node` | Per-node CPU time for validating a certificate | ✅ | ✅ |
| `cert-size-bytes-constant` | Constant size of a certificate | ✅ | ✅ |
| `cert-size-bytes-per-node` | Per-node size of a certificate | ✅ | ✅ |

For more details on each parameter, refer to the comments in the [config.d.ts](data/simulation/config.d.ts) file and the default values in [config.default.yaml](data/simulation/config.default.yaml).

## Specification

The formal specification of the Leios protocol in Agda is referenced from the repository: https://github.com/input-output-hk/ouroboros-leios-formal-spec

## Docker Simulation

You can run both the Rust and Haskell simulations using Docker to generate simulation trace logs.

### Building the Docker Images

```bash
# Build the Rust simulation image
docker build --target rs -t ouroboros-leios/sim-rs:latest -f Dockerfile .

# Build the Haskell simulation image
docker build --target hs -t ouroboros-leios/sim-hs:latest -f Dockerfile .
```

### Running the Rust Simulation

The Rust simulation generates JSONL trace files that can be visualized using the web-based UI:

#### Basic Usage (Default Settings)
```bash
# Run with default settings
docker run -v $(pwd)/output:/output ouroboros-leios/sim-rs:latest
```

#### Specifying Output File
```bash
# Run with custom output file location
docker run -v $(pwd)/output:/output ouroboros-leios/sim-rs:latest /output/simulation.jsonl
```

#### Using Custom Topology and Config Files
```bash
# Mount your config directory and use custom files
docker run \
  -v $(pwd)/output:/output \
  -v $(pwd)/data/simulation:/config \
  ouroboros-leios/sim-rs:latest /config/topology-dense-52.yaml /output/simulation.jsonl -s 20 -p /config/config.default.yaml
```

Common arguments for Rust simulation:
- `-s NUMBER`: Number of slots to simulate
- `-p PATH`: Path to custom parameters file
- `--trace-node NODE_ID`: Enable tracing for specific node
- `--timescale SCALE`: Adjust simulation speed (e.g., 16 for 16x faster)

### Running the Haskell Simulation

The Haskell simulation generates log files with simulation data:

#### Basic Usage (Default Settings)
```bash
# Run with default settings (40 seconds)
docker run -v $(pwd)/output:/output ouroboros-leios/sim-hs:latest
```

#### Custom Duration and Output File
```bash
# Run for 120 seconds with specific output file
docker run -v $(pwd)/output:/output ouroboros-leios/sim-hs:latest \
    --output-seconds 120 \
    --output-file /output/my-simulation.log
```

#### Using Custom Configuration
```bash
# Run with custom topology and config files
docker run \
    -v $(pwd)/output:/output \
    -v $(pwd)/data/simulation:/config \
    ouroboros-leios/sim-hs:latest \
    --topology /config/topology-dense-52.yaml \
    --config /config/config.default.yaml \
    --output-seconds 60 \
    --seed 12345
```

Common arguments for Haskell simulation:
- `--output-seconds NUMBER`: Duration of simulation in seconds (default: 40)
- `--seed NUMBER`: Random seed for reproducible runs
- `--topology PATH`: Custom topology file
- `--config PATH`: Custom configuration file
- `--output-file PATH`: Custom output file location

> [!NOTE]
> The Rust simulation generates JSONL trace files that can be visualized using the web-based UI in the `ui` directory.
> The Haskell simulation generates log files in its own format.
> 
> To visualize Rust simulation traces:
> 1. Generate a trace file using the Rust simulation
> 2. Use the web UI in the `ui` directory to load and visualize the trace
>
> For Haskell simulation visualization, use the `viz` command option directly in the Haskell simulation binary (not available in Docker).

## Archive

The [Leios CIP](https://github.com/cardano-foundation/CIPs/pull/379)
initially proposed in November 2022, yielded the following
content. While the material there is still relevant and useful, it
won't be updated in the future.

- `report`: the LaTeX source for the design report
- `CIP`: the initial version of the Leios CIP
- `simulation`: simulation and visualisation code for investigating Leios-like network traffic patterns.
