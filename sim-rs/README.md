# Leios Simulation

This directory contains a (very heavily WIP) simulation of the Leios protocol. It produces a stream of events which can be used to visualize or analyze the behavior of Simplified Leios.

## Running the project

```sh
cargo run --release input_path [output_path] [-s slots] [-t timescale] [--trace-node <node id>]

# for example...
cargo run --release ./test_data/realistic.yaml output/out.jsonl
```

The `input_path` is a YAML file which describes the network topology. Input files for predefined scenarios are in the `test_data` directory.

The default parameters for the simulation are defined in `data/simulation.yaml` in the root of this repository. To override parameters, pass `-p <path-to-parameters-file>` (you can pass this flag as many times as you'd like). Some predefined overrides are in the `parameters` directory.

While the simulation is running, it will log what's going on to the console. You can stop it at any time with ctrl+c, and when you do it will save the stream of events to `output_path`. To only simulate e.g. 50 slots, pass `-s 50`.

The simulation runs in realtime (1 slot every second), but you can speed it up by passing e.g. `-t 16` to run 16 times faster.

> [!NOTE]
> For instructions on running the simulation using Docker, please refer to the Docker Simulation section in the root README.md.

## Using traces in model comparisons

### Transaction diffusion

Assuming an output file `simplified.json`:

```sh
./txn_diffusion.sh simplified.json
```

This will output a ΔQ expression for use with the `delta_q` web tool corresponding to the probabilistic choice between all diffusion traces contained in the JSON file.
