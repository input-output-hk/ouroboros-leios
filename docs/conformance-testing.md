# Conformance testing

The goal of conformance testing is to check that an implementation of a protocol behaves as described in the formal specification of the protocol.
In Leios this is achieved by doing trace verification. The *trace verifier* checks, whether a trace log corresponds to a possible execution path of the relation in the formal specification. If it accepts a trace, the trace verifier produces a correctness proof, otherwise a proof for a specific failure is provided.

A formal specification for a consenus protocol usually has safety and liveness properties proved. The trace verifier serves as the connection for testing conformance of the implementation against this verified model.

## Formal specification

The formal specification of [Ouroboros Leios](https://github.com/input-output-hk/ouroboros-leios-formal-spec) is implemented in Agda as a relational specification. The relation describes the evolution of the local state of a single node, together with inputs and outputs from and to other functionalities (for example the FFD functionality) or the base ledger (which for Linear Leios is Ouroboros Praos) - see the section [Categorical Crypto framework](#categorical-crypto-framework) for more details on the composition of these channels.

Different variants of the Leios protocol have been explored in the formal specification, with a focus on *Linear Leios*. A common code base for the variants is used in order to share data types, for example the block types. The functionalities (FFD, VRF, Base ledger, etc.) are abstract data types with defining properties. The protocol carries out state transition steps upon block creation, transitioning to next slot and interacting with the base ledger. Those steps usually have pre-conditions that need to be fulfilled. For details, see [Linear Leios transitions](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Linear.lagda.md#linear-leios-transitions) in the formal specification.

## Trace verification

Trace verification checks, whether an *execution trace* of the Leios protocol is a possible realization of the formal specification. This idea has been developed in the [formal-streamlet](https://github.com/input-output-hk/formal-streamlet) protocol and been adapted in the [Fast-BFT](https://github.com/input-output-hk/innovation-fastbft) and Leios projects. Trace verification in the Leios project is currently implemented for Short and Linear Leios.

An execution trace is defined as a list of actions, where an *action* provides the necessary input for the rule selection. As long as for an action the pre-conditions for a transition step can be fulfilled, the step can be executed and is therefore correct with respect to the formal specification. Steps are done sequentially and for every step there is a correctness proof until a transition fails with a proof for a specific failure. Error handling is the interpretation of the failure proofs, mapping the failure proofs to informative error messages that can be displayed in the output of the trace verifier.

In order to be able to build explicit traces, the generic entities of the trace verifier and the formal specification need to be instantiated by specifying the parameters for the parameterized modules. An exmaple trace and it's verification can be found in [trace verifier example](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Linear/Trace/Verifier/Test.lagda.md).

## Running in Haskell

In the [leios-trace-verifier](../leios-trace-verifier) module the executables for the trace verifier are built. This is done by extracting the Agda code as MAlonzo to Haskell. Having the Haskell code for the trace verifier allows to use it together with log file parser from the module [leios-trace-hs](../leios-trace-hs) - the Haskell module is a shared module that both the Haskell simulation code and the trace verifier use.

There is a common trace log file format specified in JSON, that both the Haskell and Rust simulation use when externalizing events into the trace log file. An example log file looks as follows:
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
In order that the trace log includes all the required events, we need to specify the `--conformance-events` flag when running the simulations.

The stake distribution, that has to be passed to the trace verifier as argument is deduced from the trace log file. This is possible as in the log file there are also the negative events, i.e. for every slot there is a message, if block was created or not.

Other parameters are read from the configuration files that were used to run the simulations as well. Those are:
* topology file
* configuration file
* trace log file

### Running the trace verifier
#### Generate a trace file
Currently both simulations, Rust and Haskell, support generating the additional events needed for conformance testing by adding the flag `--conformance-testing` when running the simulation from the command line. A Rust simulation output for a whole day can be produced as follows:

```bash
$ cargo run --release -- --slots 86400 --conformance-events ../leios-trace-verifier/examples/topology.yaml ../sim-rs.out
```
#### Verify the trace file
It is recommended to run trace verifier using Nix and with the Haskell runtime system parameters setting the minimal heap size. The trace verifier can be invoked as follows:

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
### Unit tests
Along with the Haskell module for the trace verifier, there is a [small DSL](../leios-trace-verifier/hs-src/test/Spec.hs) that allows building test-traces for property based tests in Haskell. The library allows to build specific positive and negative scenarios that are tested using quick-check. A test run looks as follows:

```bash
$ cabal test
Build profile: -w ghc-9.10.1 -O1
In order, the following will be built (use -v for more details):
 - trace-parser-0.1.0.0 (test:test-trace-verifier) (first run)
Preprocessing test suite 'test-trace-verifier' for trace-parser-0.1.0.0...
Building test suite 'test-trace-verifier' for trace-parser-0.1.0.0...
Running 1 test suites...
Test suite test-trace-verifier: RUNNING...

Generated traces
  Positive cases
    Genesis slot [✔]
      +++ OK, passed 1 test.
    Generate RB [✔]
      +++ OK, passed 1 test.
    Generate IB [✔]
      +++ OK, passed 1 test.
    Generate no IB [✔]
      +++ OK, passed 1 test.
    Generate EB [✔]
      +++ OK, passed 1 test.
    Generate no EB [✔]
      +++ OK, passed 1 test.
    Generate VT [✔]
      +++ OK, passed 1 test.
    Generate no VT [✔]
      +++ OK, passed 1 test.
    Skip block production [✔]
      +++ OK, passed 100 tests.
    Sporadic block production [✔]
      +++ OK, passed 100 tests.
    Noisy block production [✔]
      +++ OK, passed 100 tests.
  Negative cases
    No actions [✔]
      +++ OK, passed 1 test.
    Start after genesis [✔]
      +++ OK, passed 1 test.
    Failure to generate IB [✔]
      +++ OK, passed 1 test.
    Failure to generate EB [✔]
      +++ OK, passed 1 test.
    Failure to generate VT [✔]
      +++ OK, passed 1 test.
Golden traces
  Verify valid traces
    agda-1.jsonl [✔]
  Reject invalid traces
    agda-2.jsonl [✔]
    case-1.jsonl [✔]

Finished in 0.4433 seconds
19 examples, 0 failures
Test suite test-trace-verifier: PASS
Test suite logged to:
/home/yves/code/ouroboros-leios/leios-trace-verifier/dist-newstyle/build/x86_64-linux/ghc-9.10.1/trace-parser-0.1.0.0/t/test-trace-verifier/test/trace-parser-0.1.0.0-test-trace-verifier.log
1 of 1 test suites (1 of 1 test cases) passed.
```
## Appendix
### Categorical crypto framework

Motivated by the need for better runtime performance of the trace verifier, the Categorical Crypto Framework has been introduced in the project. The framework facilitates the composition of the different components and we no longer have to manage the state of the functionalities explicitly (previously state of the functionalities was also put into the `LeiosState` for convenience).

The Leios protocol is specified from the view of a single, honest party, describing all the possible changes of the `LeiosState` with pre-conditions.

This is different to the formal specifications of [Ouroboros Peras](https://github.com/input-output-hk/peras-design/blob/main/src/Peras/SmallStep.lagda.md) or [Ouroboros Praos](https://github.com/input-output-hk/ouroboros-praos-formal-spec/blob/main/src/Protocol/Semantics.agda), where in both cases all nodes of the distributed system, including adversarial nodes, are modelled and the relation in the formal specification describes the possible evolution of the distributed system as a whole.

### TODOs

* Move Linear Leios, specification and trace verifier code into a separate module or repo. The other Leios variants are more complex than Linear Leios and therefore the general model in the formal specification might be confusing with Linear Leios
* Currently the leader selection is inferred from the log file. The formal specification needs to run the leader selection algorithm with the same seed as the node. This is a requirement for the trace verifier to be used for *live monitoring* in a production system
* [PR-605](https://github.com/input-output-hk/ouroboros-leios/pull/605) introduced the feature, that allows the trace verifier to start at an arbitrary slot. This needs to be more generalized, in order for the trace verifier to start with an arbitrary state
* The performance of the trace verifier needs to be improved: When running long traces, the performance degrades significantly (the Haskell garbage collector taking a lot of resources)
