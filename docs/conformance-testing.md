# Conformance testing

The goal of conformance testing is to check that an implementation of a protocol behaves as described in the formal specification of the protocol.
In Leios this is achieved by doing trace verification. The trace verifier checks, whether a trace log corresponds to a possible execution path of the relation in the formal specification.

## Formal specification

The formal specification of [Ouroboros Leios](https://github.com/input-output-hk/ouroboros-leios-formal-spec) is implemented in Agda as a relational specification. Different variants of the Leios protocol have been explored in the formal specification, with a focus on Linear Leios.
A common code base for the variants is used in order to share data types, for example the block types.
The functionalities (FFD, VRF, Base ledger, etc.) are abstract data types with defining properties.

### Categorical crypto framework

Motivated by the need for better runtime performance of the trace verifier, the Categorical Crypto Framework has been introduced in the project. The framework facilitates the composition of the different components and we no longer have to manage the state of the functionalities explicitly (previously state of the functionalities was also put into the `LeiosState` for convenience).

The Leios protocol is specified from the view of a single, honest party, describing all the possible changes of the `LeiosState` with pre-conditions.

This is different to the formal specifications of [Ouroboros Peras](https://github.com/input-output-hk/peras-design/blob/main/src/Peras/SmallStep.lagda.md) or [Ouroboros Praos](https://github.com/input-output-hk/ouroboros-praos-formal-spec/blob/main/src/Protocol/Semantics.agda), where in both cases all nodes of the distributed system, including adversarial nodes, are modelled and the relation in the formal specification describes the possible evolution of the distributed system as a whole.

### State transitions in Leios

The relation specifying the Linear-Leios protocol carries out state transition steps upon block creation, transitioning to next slot and interacting with the base ledger. Those steps usually have pre-conditions that need to be fulfilled. For details, see [Linear Leios transitions](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Linear.lagda.md#linear-leios-transitions) in the formal specification.

## Trace verification

Trace verification checks, whether an execution trace of the Leios protocol is a possible realization of the formal specification. This idea has been developed in the [formal-streamlet](https://github.com/input-output-hk/formal-streamlet) protocol and been adapted in the [Fast-BFT](https://github.com/input-output-hk/innovation-fastbft) and Leios projects. Trace verification in the Leios project is currently implemented for Short and Linear-Leios.

When parsing a trace log file, events are mapped to actions that trigger a step in the relational specification of the protocol. As long as for an action the pre-conditions for the next transition step can be fulfilled and the step can be done, the transition is considered correct with respect to the formal specification. Steps are done sequentially until a transition fails with a proof providing the reason of failure that gets included in the error.

### Error handling

Error handling is the interpretation of the failure proofs, mapping the failure proofs to informative error messages that can be displayed in the output of the trace verifier.

### Conformance events

For conformance testing additional events had to be added to the Haskell and Rust simulation. For Short and Linear Leios, an explicit event for the slot transition of a node has been added (the event could also be inferred from the other log entries), for Short-Leios the non-election for block creation or voting events have been added as well (those "negative" events are needed as the formal specification enforces a node to always check, whether a block or vote can be created).

### Formal spec repository

The formal specification of the Leios protocol is implemented in the repository [ouroboros-leios-formal-spec](https://github.com/input-output-hk/ouroboros-leios-formal-spec).
In that repository there are [examples](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Linear/Trace/Verifier/Test.lagda.md) that illustrate how the trace verifier works. Here the trace is part of the example in the Agda file. In addition in order to setup the trace verifier for Linear Leios we need the following configuration values:

* Network parameters
  * numberOfParties: Number of parties (nodes) in the distributed system
  * stakeDistribution: The stake distribution, i.e. stake per node

* Other parameters
  * sutId: The id of the system under test (SUT)
  * winning-slots: The lotteries for EB and Votes

### Leios repository

In the `leios-trace-verifier` module in the Leios repository the executables for the trace verifier is built. This is done by extracting the Agda code as MAlonzo to Haskell. Having the Haskell code for the trace verifier allows to use it together with log file parser from the module `leios-trace-hs`. The Haskell module is a shared module that both the Haskell simulation code and the trace verifier use.

In addition there is a common trace log file format specified in JSON, that both the Haskell and Rust simulation use when externalizing events into the trace log file.
```bash
{"message":{"node":"node-0","slot":25,"type":"Slot"},"time_s":25}
{"message":{"node":"node-0","slot":25,"type":"NoIBGenerated"},"time_s":25}
{"message":{"id":"54-2","recipient":"node-0","type":"IBReceived"},"time_s":25.028918}
{"message":{"id":"20-3","node":"node-0","slot":24,"type":"IBEnteredState"},"time_s":25.065875}
{"message":{"id":"54-2","node":"node-0","slot":23,"type":"IBEnteredState"},"time_s":25.12807}
{"message":{"id":"21-0","recipient":"node-0","type":"IBReceived"},"time_s":25.23862}
{"message":{"id":"21-0","node":"node-0","slot":24,"type":"IBEnteredState"},"time_s":25.337772}
{"message":{"id":"51-1","recipient":"node-0","type":"IBReceived"},"time_s":25.680406}
{"message":{"id":"83-0","recipient":"node-0","type":"IBReceived"},"time_s":25.743445}
{"message":{"id":"51-1","node":"node-0","slot":24,"type":"IBEnteredState"},"time_s":25.779558}
{"message":{"id":"83-0","node":"node-0","slot":25,"type":"IBEnteredState"},"time_s":25.842597}
{"message":{"node":"node-0","slot":26,"type":"Slot"},"time_s":26}
{"message":{"node":"node-0","slot":26,"type":"NoIBGenerated"},"time_s":26}
{"message":{"id":"24-2","recipient":"node-0","type":"IBReceived"},"time_s":26.299945}
{"message":{"id":"24-2","node":"node-0","slot":24,"type":"IBEnteredState"},"time_s":26.399097}
{"message":{"id":"17-2","recipient":"node-0","type":"IBReceived"},"time_s":26.840607}
{"message":{"id":"90-1","recipient":"node-0","type":"IBReceived"},"time_s":26.920078}
{"message":{"id":"57-2","recipient":"node-0","type":"IBReceived"},"time_s":26.921749}
{"message":{"id":"17-2","node":"node-0","slot":26,"type":"IBEnteredState"},"time_s":26.939759}
{"message":{"node":"node-0","slot":27,"type":"Slot"},"time_s":27}
{"message":{"node":"node-0","slot":27,"type":"NoIBGenerated"},"time_s":27}
{"message":{"id":"45-4","recipient":"node-0","type":"IBReceived"},"time_s":27.005877}
{"message":{"id":"90-1","node":"node-0","slot":25,"type":"IBEnteredState"},"time_s":27.01923}
{"message":{"id":"57-2","node":"node-0","slot":24,"type":"IBEnteredState"},"time_s":27.020901}
{"message":{"id":"45-4","node":"node-0","slot":26,"type":"IBEnteredState"},"time_s":27.105029}
{"message":{"id":"40-1","recipient":"node-0","type":"IBReceived"},"time_s":27.393871}
{"message":{"id":"40-1","node":"node-0","slot":27,"type":"IBEnteredState"},"time_s":27.493023}
{"message":{"id":"35-2","recipient":"node-0","type":"IBReceived"},"time_s":27.502044}
{"message":{"id":"35-2","node":"node-0","slot":26,"type":"IBEnteredState"},"time_s":27.601196}
```

The stake distribution, that has to be passed to the trace verifier as argument is deduced from the trace log file. This is possible as in the log file there are also the negative events, i.e. for every slot there is a message, if block was created or not.

Other parameters are read from the configuration files that were used to run the simulations as well. Those are:
* topology file
* configuration file
* trace log file

### Running the trace verifier

The Leios trace verifier needs a simulation output.

#### Generate a trace file

Currently both simulations, Rust and Haskell, support generating the additional events needed for conformance testing by adding the flag `--conformance-testing` when running the simulation from the command line. A Rust simulation output for a whole day can be produced as follows:

```bash
$ cargo run --release -- --slots 86400 --conformance-events ../leios-trace-verifier/examples/topology.yaml ../sim-rs.out
```

### Run trace verifier

It is recommended to run trace verifier using Nix and with the Haskell runtime system parameters setting the minimal heap size.

The trace verifier can be invoked as follows:

```bash
$ nix run .#linear-leios-trace-verifier -- --help
Leios trace verifier

Usage: linear-leios-trace-verifier --trace-file ARG --config-file ARG
                                   --topology-file ARG --idSut ARG

  Linear Leios trace verifier

Available options:
  --trace-file ARG         Leios simulation trace log file
  --config-file ARG        Leios configuration file
  --topology-file ARG      Leios topology file
  --idSut ARG              Id of system under test (SUT)
  -h,--help                Show this help text
```

Make sure, to specify the same topology and configuration files as used to generate the log trace.

```bash
$ nix run .#linear-leios-trace-verifier -- +RTS -H1G -s -RTS --trace-file trace.log --config-file data/simulation/config.default.yaml --topology-file leios-trace-verifier/examples/topology.yaml --idSut 0
```

#### Performance

The performance of the trace verifier is still an open issue. When running log traces, the performance degrades significantly as the Haskell garbage collector takes a lot of resources.
