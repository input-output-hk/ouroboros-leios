This repository is home of the _Leios R&D project_ whose purpose is to define a specification of the Ouroboros Leios protocol.

> [!CAUTION]
> This project is in its very early stage and is mostly
> experimental and exploratory. All contributions and feedbacks are
> welcome. No warranties of any kind about the current or future
> features of Cardano are to be expected, implicitly and explicitly.

# Getting started

Checkout [CONTRIBUTING.md](CONTRIBUTING.md) document for possible contributions and communication channels

More documentation about Leios can be found in the [web site](https://leios.cardano-scaling.org).

# Content

## Current

- [Logbook](Logbook.md) contains a detailed account of
  problems,successes, failures, ideas, references and is intended as a
  tool to help the team members stay in sync. It's updated frequently
  with notes about the day-to-day work, meetings, ideas, etc.
- [simulation](simulation) contains experimental Haskell code to simulate the Leios protocol
- [sim-rs](sim-rs) contains experimental Rust code to simulate the Leios protocol
- [site](site) contains the sources of the aforementioned web site

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

## Specification

Build the Agda specification for Leios using either

```console
$ nix build --no-link --accept-flake-config .#leiosSpec
```

or

```console
$ nix develop

$ cd formal-spec

$ agda Leios/SimpleSpec.agda
```

## Archive

The [Leios CIP](https://github.com/cardano-foundation/CIPs/pull/379)
initially proposed in November 2022, yielded the following
content. While the material there is still relevant and useful, it
won't be updated in the future.

- `report`: the LaTeX source for the design report
- `CIP`: the initial version of the Leios CIP
- `simulation`: simulation and visualisation code for investigating Leios-like network traffic patterns.
