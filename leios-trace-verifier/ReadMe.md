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
