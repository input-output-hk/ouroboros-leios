# CIP Experiment Scripts

These scripts run the Linear Leios simulation experiments for the CIP analysis,
sweeping throughput levels (0.150–0.350 TxMB/s) and voting committee modes
(wfa-ls, everyone, top-stake-fraction) on the 750-node pseudo-mainnet topology.

## Quick Start

```sh
# Run all throughputs × all voting modes (default: turbo engine, seed 0)
bash run-all-voting-modes.sh

# Run with a different seed
bash run-all-voting-modes.sh -s 1

# Run a single voting mode across all experiments
bash run-sweep.sh -m wfa-ls

# Run a single experiment (from within an experiment directory, e.g. experiments/NA,0.200/)
cd experiments/NA,0.200
bash ../../run-deterministic.sh -m everyone -s 0

# Monitor a running sweep
bash check-progress.sh
```

## Scripts

### run-deterministic.sh

Per-experiment runner. Must be run from an experiment directory (e.g. `NA,0.200/`).
Generates config from `../config.yaml`, runs the simulation, processes traces,
and saves all outputs into a `{voting-mode}/seed-{N}/` subdirectory.

**Options:**
| Flag | Default | Description |
|------|---------|-------------|
| `-m, --voting-mode MODE` | `wfa-ls` | `wfa-ls`, `everyone`, or `top-stake-fraction` |
| `-s, --seed N` | `0` | RNG seed for deterministic runs |
| `--turbo` | *(default)* | Sequential DES, 6-shard zero-latency-clusters |
| `--actor` | | Async actor engine (non-deterministic) |
| `--sequential` | | Sequential DES, single shard |
| `--memory-limit` | off | Apply backlog caps (generated=10, peer=10000, max-age=24) |
| `--quorum-fraction F` | `0.75` | Quorum fraction for vote threshold |
| `--stake-fraction F` | `0.99` | Stake fraction for top-stake-fraction mode |

**Output directory structure:**
```
NA,0.200/
├── case.csv              # original CIP results (git-tracked)
├── config.yaml           # original CIP config (git-tracked)
├── summary.txt           # original CIP summary (git-tracked)
├── wfa-ls/
│   ├── seed-0/
│   │   ├── config.yaml   # generated per-run config
│   │   ├── case.csv
│   │   ├── summary.txt
│   │   ├── stdout / stderr
│   │   ├── sim.log.gz
│   │   ├── lifecycle.csv.gz
│   │   ├── cpus.csv.gz
│   │   ├── receipts.csv.gz
│   │   ├── resources.csv.gz
│   │   └── sizes.csv.gz
│   └── seed-1/
│       └── ...
├── everyone/
│   └── seed-0/
│       └── ...
└── top-stake-fraction/
    └── seed-0/
        └── ...
```

### run-sweep.sh

Runs `run-deterministic.sh` for all sweep experiments — both NA throughputs
(0.150, 0.200, 0.250, 0.300, 0.350 TxMB/s, no Plutus) and Plutus levels
(1000, 2000, 5000, 10000, 20000, 50000 Gstep/EB at fixed 0.250 TxMB/s).
Other arguments are passed through to `run-deterministic.sh`.

| Flag | Effect |
|------|--------|
| `--na-only` | Run only the NA throughput experiments |
| `--plutus-only` | Run only the Plutus experiments |
| *(none)* | Run both groups (11 experiments per voting mode) |

```sh
bash run-sweep.sh -m wfa-ls -s 0                    # both groups, single mode/seed
bash run-sweep.sh --plutus-only -m wfa-ls -s 0      # Plutus only
bash run-sweep.sh --na-only -m everyone -s 1 --actor
```

### run-all-voting-modes.sh

Runs `run-sweep.sh` for each of the three voting modes (wfa-ls, everyone,
top-stake-fraction). Passes all arguments through.

```sh
bash run-all-voting-modes.sh                # all modes, turbo, seed 0
bash run-all-voting-modes.sh -s 1           # all modes, turbo, seed 1
bash run-all-voting-modes.sh --actor        # all modes, actor engine
```

**Typical run times** (turbo mode, 750-node topology, 1500 slots):
- Per experiment: ~30–70 min (higher throughput = longer)
- Full 15-experiment sweep: ~6–13 hours

### check-progress.sh

Monitoring script. Shows running sim-cli processes, current slot progress,
and sweep log status.

### combine-results-multi-vote.sh

Collects results from a specific voting mode and seed into the `results/`
directory format expected by `analysis.ipynb`.

```sh
bash combine-results-multi-vote.sh -m wfa-ls -s 0
# then open analysis.ipynb
```

## Configuration

### config.yaml

Shared scenario config for all experiments. Contains both Haskell sim field
names (original) and sim-rs split field names (persistent/non-persistent).
Both simulators read the same file, each ignoring fields it doesn't recognise.

Key parameters:
- TX generation: slots 60–960, 1500 total slots
- Topology: `topology-v2` (750 nodes), bandwidth scaled to 10 Mb/s, 4 vCPU
- EB size: 12 MB max
- Vote probability: 480 persistent + 120 non-persistent (wfa-ls), threshold 450
- Stage lengths: diffuse=7 slots, vote=4 slots

### Voting mode thresholds

Each mode computes its vote threshold from the topology:
- **wfa-ls**: Fixed threshold 450, probability split 480:120 persistent:non-persistent
- **everyone**: All 750 nodes vote, threshold = ceil(750 × 0.75) = 563
- **top-stake-fraction**: Top 99% stake nodes (~213), threshold = ceil(213 × 0.75) = 160

## Engine modes

- **turbo** (default): Sequential DES with 6 shards and zero-latency-clusters
  strategy. Deterministic, ~5× faster than actor. Uses `turbo.yaml` overlay
  (timestamp-resolution-ms: 1.0, tx-batch-window-ms: 10.0).
- **actor**: Async tokio actor system. Non-deterministic (async scheduling).
  Most faithful to real network behaviour but slow (~90 min per experiment).
- **sequential**: Sequential DES, single shard. Deterministic but slower than
  turbo due to finer timestamp resolution (0.1ms vs 1.0ms).

## Reproducibility

With turbo or sequential engine and a fixed seed, results are bit-identical
across runs (verified by md5sum of output files, modulo gzip header timestamps).
Different seeds produce different RB lottery outcomes but the same protocol
behaviour (100% TX finalization at all throughputs tested).
