# Leios Trace Verifier

The Leios trace verifier checks a trace file from the Rust or Haskell simulator of Leios for conformance to the Leios specification.


## Building


### Nix

```bash
nix build .#leios-trace-verifier
```


### Development environment

```bash
make
```


## Example usage

First create a trace using the Haskell simulator.

```bash
nix run .#ols -- \
  sim leios \
  --leios-config-file data/simulation/config.default.yaml \
  --topology-file data/simulation/topo-default-100.yaml \
  --conformance-events \
  --shared-log-format JSON \
  --output-seconds 30 \
  --output-file sim.log
```

Now check the `sim.log` file produced by the simulator.

```bash
nix run .#leios-trace-verifier -- \
  --config-file data/simulation/config.default.yaml \
  --topology-file data/simulation/topo-default-100.yaml \
  --trace-file sim.log \
  --idSut 0
```

The output lists the number of successful trace entries checked, or `0` if the checking failed.


### Test cases for trace verify and conformance tests

The test suite for the trace verify contains property-based tests that check whether the conformance testing matches expectations. The suite has both manually curated golden tests and automatically generated property-based tests. Both positive and negative cases are tested.

```console
$ nix run .#test-trace-verifier

Generated trace
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
    Generate equivocated IBs [✔]
      +++ OK, passed 1 test.
    Generate equivocated EBs [✔]
      +++ OK, passed 1 test.
    Generate equivocated VTs [✔]
      +++ OK, passed 1 test.
    Sporadic gaps in production [✔]     
      +++ OK, passed 100 tests.
Golden traces
  Verify valid traces
    agda-1.jsonl [✔]
    agda-2.jsonl [✔]
  Reject invalid traces
    case-1.jsonl [✔]

Finished in 0.3541 seconds
20 examples, 0 failures
Test suite test-trace-verifier: PASS
```
