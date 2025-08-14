# Conformance testing

The goal of conformance testing is to check that an implementation of a protocol behaves as described in the formal specification of the protocol.
In Leios this is achieved by doing trace verification. The trace verifier checks, whether a trace log corresponds to a possible execution path of the relation in the formal specification.

## Formal specification

The formal specification of [Ouroboros Leios](https://github.com/input-output-hk/ouroboros-leios-formal-spec) is implemented in Agda as a relational specification. Different variants of the Leios protocol have been explored in the formal specification, with a focus on Short-Leios.
A common code base for the variants is used in order to share data types, for example the block types.
The functionalities (FFD, VRF, Base ledger, etc.) are abstract data types with defining properties.

### Categorical crypto framework

Motivated by the need for better runtime performance of the trace verifier, the Categorical Crypto Framework has been introduced in the project. The framework facilitates the composition of the different components and we no longer have to manage the state of the functionalities explicitly (previously state of the functionalities was also put into the `LeiosState` for convenience).

In this setup the Leios protocol is specified from the view of a single, honest party, describing all the possible changes of the `LeiosState` for given pre-conditions.

This is different to the formal specifications of [Ouroboros Peras](https://github.com/input-output-hk/peras-design/blob/main/src/Peras/SmallStep.lagda.md) or [Ouroboros Praos](https://github.com/input-output-hk/ouroboros-praos-formal-spec/blob/main/src/Protocol/Semantics.agda), where in both cases all nodes of the distributed system, including adversarial nodes, are modelled and the relation in the formal specification describes the possible evolution of the distributed system as a whole.

### State transitions in Leios

The relation specifying the Short-Leios protocol carries out state transition steps upon block creation, transitioning to next slot and interacting with the base ledger. Those steps usually have pre-conditions that need to be fulfilled. For details, see [(Full-)Short Leios transitions](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Short.lagda.md#full-short-leios-transitions) in the formal specification.

## Trace verification

Trace verification checks, whether an execution trace of the Leios protocol is a possible realization of the formal specification. This idea has been developed in the [formal-streamlet](https://github.com/input-output-hk/formal-streamlet) protocol and been adapted in the [Fast-BFT](https://github.com/input-output-hk/innovation-fastbft) and Leios projects. Trace verification in the Leios project is currently implemented for Short-Leios.

When parsing a trace log file, events are mapped to actions that trigger a step in the relational specification of the protocol. As long as for an action the pre-conditions for the next transition step can be fulfilled and the step can be done, the transition is considered correct with respect to the formal specification. Steps are done sequentially until a transition fails with a proof providing the reason of failure that gets included in the error.

### Error handling

Error handling is the interpretation of the failure proofs, mapping the failure proofs to informative error messages that can be displayed in the output of the trace verifier.

### Conformance events

For conformance testing additional events had to be added to the Haskell and Rust simulation. First, an explicit event for the slot transition of a node has been added (the event could also be inferred from the other log entries), second the non-election for block creation or voting events have been added as well. Those "negative" events are needed as the formal specification enforces a node to always check, whether a block or vote can be created.

### Formal spec repo

The formal specification of the Leios protocol is implemented in the repository [ouroboros-leios-formal-spec](https://github.com/input-output-hk/ouroboros-leios-formal-spec).
In that repository there are [examples](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Short/Trace/Verifier/Test.lagda.md) that illustrate how the trace verifier works. Here the trace is part of the example in the Agda file. In addition in order to setup the trace verifier we need the following configuration values:

* Stake distribution
* Configuration
* Parameters

### Leios repo

In the `leios-trace-verifier` module in the Leios repo the executable for the trace verifier is built. This is done by extracting the Agda code as MAlonzo to Haskell. Having the Haskell code for the trace verifier also to use it together with log file parser from the module `leios-trace-hs`. The Haskell module is a shared module that both the Haskell simulation code and the trace verifier use.

In addition there is a common trace log file format specified in JSON, that both the Haskell and Rust simulation use when externalizing events into the trace log file.

```bash
{"message":{"id":"0-0","pipeline":0,"producer":"node-0","rb_ref":"genesis","size_bytes":98608,"slot":0,"tx_payload_bytes":98304,"type":"IBGenerated"},"time_s":0.13}
{"message":{"id":"1-0","pipeline":0,"producer":"node-1","rb_ref":"genesis","size_bytes":98608,"slot":0,"tx_payload_bytes":98304,"type":"IBGenerated"},"time_s":0.13}
{"message":{"id":"2-0","pipeline":0,"producer":"node-2","rb_ref":"genesis","size_bytes":98608,"slot":0,"tx_payload_bytes":98304,"type":"IBGenerated"},"time_s":0.13}
```

* buildup stake distr
* read topo file, etc.

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
