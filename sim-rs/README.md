# Leios Simulation

This directory contains a (very heavily WIP) simulation of the Leios protocol. It produces a stream of events which can be used to visualize or analyze the behavior of Simplified Leios.

## Running the project

```sh
cargo run --release input_path [output_path]

# for example...
cargo run --release ./test_data/realistic.toml output/out.jsonl
```

The `input_path` is a TOML file which describes protocol parameters, the network topology, and other necessary configuration. Input files for predefined scenarios are in the `test_data` directory.

While the simulation is running, it will log what's going on to the console. You can stop it at any time with ctrl+c, and when you do it will save the stream of events to `output_path`.

The simulation runs in realtime (1 slot every second), but you can speed it up by passing e.g. `-t 16` to run 16 times faster.
