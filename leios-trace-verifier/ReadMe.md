# Leios Trace Verifier

The Leios trace verifier checks a trace — from the Rust or Haskell simulator, or
from a running node — for conformance to the Leios specification.

There are two executables:

- **`linear-leios-trace-verifier`** — reads the topology, configuration and
  trace from files. Verifies a whole trace at once (batch) or incrementally
  (`--streaming`). Has no `cardano-api` dependency.
- **`linear-leios-trace-verifier-chain`** — streams the trace from stdin and
  sources the system-under-test's leadership schedule and the stake
  distribution from a running node via the `cardano-api`. The stage lengths are
  fixed (`lvote = 4`, `ldiff = 7`); no topology or configuration file is needed.


## Building

```bash
nix build '.#trace-parser:exe:linear-leios-trace-verifier'
nix build '.#trace-parser:exe:linear-leios-trace-verifier-chain'
```

Or, in the development environment:

```bash
make
```


## File-based verifier

First create a trace using the Haskell simulator.

```bash
nix run '.#ouroboros-leios-sim:exe:ols' -- \
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
nix run '.#trace-parser:exe:linear-leios-trace-verifier' -- \
  --config-file data/simulation/config.default.yaml \
  --topology-file data/simulation/topo-default-100.yaml \
  --trace-file sim.log \
  --idSut 0
```

The output lists the number of successful trace entries checked, or `0` if the
checking failed.

To verify incrementally instead, pass `--streaming` and feed the trace on
stdin; the verifier re-checks at each slot boundary and fails fast on the first
violation:

```bash
cat sim.log | nix run '.#trace-parser:exe:linear-leios-trace-verifier' -- \
  --config-file data/simulation/config.default.yaml \
  --topology-file data/simulation/topo-default-100.yaml \
  --idSut 0 \
  --streaming
```

| Option | Description |
| --- | --- |
| `--trace-file FILE` | Trace log file, batch mode (default `/dev/stdin`). |
| `--config-file FILE` | Leios configuration file. |
| `--topology-file FILE` | Leios topology file (party count and stakes). |
| `--idSut N` | Index of the system under test (`node-N`). |
| `--starting-slot N` | Starting slot of the trace (default `0`). |
| `--streaming` | Read JSONL events from stdin and verify incrementally. |


## Chain verifier

The chain verifier connects to a running node, queries the system-under-test's
leadership schedule and the on-chain stake distribution for the current (or
`--next`) epoch, and stream-verifies a JSONL trace read from stdin. The system
under test is identified by its stake pool id (`--stake-pool-id`); the parties
are the chain's stake pools and trace producers (pool ids) are matched against
them, so no topology or configuration file is needed.

```bash
<node emitting a JSONL conformance trace> | \
nix run '.#trace-parser:exe:linear-leios-trace-verifier-chain' -- \
  --socket-path /path/to/node.socket \
  --mainnet \
  --shelley-genesis /path/to/shelley-genesis.json \
  --stake-pool-id pool1abc... \
  --vrf-signing-key-file /path/to/vrf.skey
```

| Option | Description |
| --- | --- |
| `--socket-path FILE` | Node socket for the cardano-api queries. |
| `--mainnet` / `--testnet-magic N` | Network identifier. |
| `--shelley-genesis FILE` | Shelley genesis file. |
| `--stake-pool-id POOLID` | System-under-test's stake pool id (bech32 or hex). |
| `--vrf-signing-key-file FILE` | VRF signing key file. |
| `--next` | Query the next epoch's schedule (default: current). |
| `--starting-slot N` | Starting slot of the trace (default `0`). |

The verifier reports `ok` at each slot boundary and fails fast on the first
violation.


## Test cases for trace verify and conformance tests

The test suite for the trace verify contains property-based tests that check whether the conformance testing matches expectations. The suite has both manually curated golden tests and automatically generated property-based tests. Both positive and negative cases are tested.

```console
$ nix run '.#trace-parser:test:test-trace-verifier'

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
