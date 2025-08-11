# Conformance testing

The goal of conformance testing is to check that an implementation of a protocol behaves as described in the formal specification of the protocol, i.e. conformance testing verifies that a given trace from an execution of the protocol is one of the possible paths defined by a relation in the formal specification.

## Formal specification

The formal specification is implemented in Agda as a relation specification. Different variants of the Leios protocol have been explored in the formal specification, with a focus on Short-Leios.
A common code base for the variants is used in order to share data types, like the block types for example. In addition the functionalities (FFD, VRF, Base ledger, etc.) are abstract data types with defining properties.

### Categorical crypto framework

Motivated by the need for better runtime performance of the trace verifier, the Categorical Crypto Framework developed by André Knispel has been introduced in the project. The framework facilitates the composition of the different components and we no longer have to manage the state for the functionalities explicitly (previously state of the functionalities was also put into the `LeiosState`).

### Single node view

The formal spec describes the evolution of a single, honest node running the Leios protocol, i.e., it describes all the possible changes of the `LeiosState` for some given pre-conditions.
This is different to the formal specification of [Ouroboros Peras](https://github.com/input-output-hk/peras-design/blob/main/src/Peras/SmallStep.lagda.md) or [Ouroboros Praos](https://github.com/input-output-hk/ouroboros-praos-formal-spec/blob/main/src/Protocol/Semantics.agda), where in both cases all nodes of the distributed system (including adversary nodes) are modelled, and the relation in the formal specification describes the possible evolution of the "world".

### State transitions in Leios

The Short-Leios relation does state transition steps upon

* Creating an InputBlock
* Creating an EndorserBlock
* Voting
* Can not create an InputBlock
* Can not create an EndorserBlock
* Can not vote
* Transitioning to the next slot
* Interaction with Base Ledger

Upkeep

## Trace verification

Trace verification checks, if an execution trace of the Leios protocol is correct by checking it against the formal specification. The idea has been developed in the [formal-streamlet](https://github.com/input-output-hk/formal-streamlet) protocol and been adapted in the [Fast-BFT](https://github.com/input-output-hk/innovation-fastbft) and Leios projects.

Trace verification in the Leios project is currently implemented for Short-Leios.

Events from the trace log are mapped to actions. 
Actions

### Formal spec repo

The formal specification of the Leios protocol is implemented in the repository [ouroboros-leios-formal-spec](https://github.com/input-output-hk/ouroboros-leios-formal-spec).

### Leios repo

In the `leios-trace-verifier` module in the Leios repo the executable for the trace verifier is built.

Stake distribution
Configuration
Parameters

### Conformance events

### Error handling

### Log file parser

The parser for the trace log files is in the module `leios-trace-hs`. The Haskell module is a shared module that both the Haskell simulation code and the trace verifier use. In addition there is a common trace log file format specified in JSON, that both the Haskell and Rust simulation use when externalizing events into the trace log file.

JSON log file

```bash
{"message":{"id":"0-0","pipeline":0,"producer":"node-0","rb_ref":"genesis","size_bytes":98608,"slot":0,"tx_payload_bytes":98304,"type":"IBGenerated"},"time_s":0.13}
{"message":{"id":"1-0","pipeline":0,"producer":"node-1","rb_ref":"genesis","size_bytes":98608,"slot":0,"tx_payload_bytes":98304,"type":"IBGenerated"},"time_s":0.13}
{"message":{"id":"2-0","pipeline":0,"producer":"node-2","rb_ref":"genesis","size_bytes":98608,"slot":0,"tx_payload_bytes":98304,"type":"IBGenerated"},"time_s":0.13}
```

### Running the trace verifier

Example execution

#### Generate a trace file

Currently both simulations, Rust and Haskell, support generating the additional events needed for conformance testing by adding the flag `--conformance-testing` when running the simulation from the command line.

```bash
$ cargo run --release -- --slots 86400 --conformance-events ../leios-trace-verifier/examples/topology.yaml ../sim-rs.out
```

### Run trace verifier

It is recommended to run trace verifier using Nix and with the Haskell runtime system parameters setting the minimal heap size.

#### flags

```bash
$ nix run .#leios-trace-verifier -- +RTS -H1G -s -RTS --help
parser - a Leios trace verifier

Usage: leios-trace-verifier --trace-file ARG --config-file ARG
                            --topology-file ARG --idSut ARG

  Leios trace verifier

Available options:
  --trace-file ARG         Short Leios simulation trace log file
  --config-file ARG        Short Leios configuration file
  --topology-file ARG      Short Leios topology file
  --idSut ARG              Id of system under test (SUT)
  -h,--help                Show this help text
```

```bash
$ nix run .#leios-trace-verifier -- +RTS -H1G -s -RTS --trace-file trace.log --config-file data/simulation/config.default.yaml --topology-file leios-trace-verifier/examples/topology.yaml --idSut 0
```

#### Performance

GC degrades for long traces
