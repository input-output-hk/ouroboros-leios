# CIP Experiment Scripts

These scripts run the Linear Leios simulation experiments for the CIP analysis,
sweeping throughput levels (0.150–0.350 TxMB/s) and voting committee modes
(wfa-ls, everyone, top-stake-fraction) across the 750-node and 1500-node
pseudo-mainnet topologies.

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
| `--memory-limit` | off | Apply backlog caps from `sim-rs/parameters/memory-limit.yaml` (generated=10, peer=10000, max-age=24). Note: these caps **alter behaviour** at high throughput — generated=10 drops ~17% of TXs at 0.350 TxMB/s. Avoid for production runs. |
| `--memory-limit-file PATH` | | Use a custom memory-limit YAML instead of the default; PATH is relative to `sim-rs/parameters/`. |
| `--quorum-fraction F` | `0.75` | Quorum fraction for vote threshold |
| `--stake-fraction F` | `0.99` | Stake fraction for top-stake-fraction mode |
| `--topology NAME` | `topology-v2` | Basename of topology file under `data/simulation/pseudo-mainnet/` (e.g. `topology-v2-1500` for 1500 nodes) |

**Output directory structure:**
```
NA,0.200/
├── wfa-ls/
│   ├── topology-v2/
│   │   ├── seed-0/
│   │   │   ├── config.yaml      # generated per-run config (incl. throughput, vote params)
│   │   │   ├── case.csv         # 1-row scenario summary used by analysis.ipynb
│   │   │   ├── summary.txt      # ansifilter'd `INFO leios|praos|network` lines
│   │   │   ├── stdout / stderr  # full sim-cli output
│   │   │   ├── time.txt         # `/usr/bin/time -v` (peak RSS, etc.)
│   │   │   ├── done             # marker: written ONLY when full pipeline completes
│   │   │   ├── sim.log.gz       # raw conformance event stream
│   │   │   ├── lifecycle.csv.gz
│   │   │   ├── cpus.csv.gz
│   │   │   ├── receipts.csv.gz
│   │   │   ├── resources.csv.gz
│   │   │   └── sizes.csv.gz
│   │   └── seed-1/
│   │       └── ...
│   └── topology-v2-1500/
│       └── seed-0/
│           └── ...
├── everyone/
│   └── topology-v2/
│       └── seed-0/
│           └── ...
└── top-stake-fraction/
    └── topology-v2/
        └── seed-0/
            └── ...
```

The `done` marker is the authoritative signal that a run completed. `combine-results-multi-vote.sh` checks for it (instead of inferring completion from empty stderr) so OOM-killed or partial runs naturally drop out of analysis.

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

If any individual experiment fails (OOM, abort), the sweep logs `=== <exp> FAILED (exit N) — continuing ===` and proceeds with the next experiment. At the end it prints the failed list and exits 1.

### run-all-voting-modes.sh

Runs `run-sweep.sh` for each of the three voting modes (wfa-ls, everyone,
top-stake-fraction). Passes all arguments through.

```sh
bash run-all-voting-modes.sh                # all modes, turbo, seed 0
bash run-all-voting-modes.sh -s 1           # all modes, turbo, seed 1
bash run-all-voting-modes.sh --actor        # all modes, actor engine
bash run-all-voting-modes.sh --na-only --topology topology-v2-1500 -s 0
```

If `run-sweep.sh` reports any failed experiments for a mode, the wrapper logs and continues to the next mode (rather than aborting the whole sweep on first OOM).

**Typical run times** (turbo mode, 1500 slots simulated, sim+trace+pigz post-processing):

| Topology | Per experiment | Full 11-exp sweep × 3 modes |
|---|---|---|
| `topology-v2` (750 nodes) | ~30–90 min | ~12–18 h |
| `topology-v2-1500` (1500 nodes) | ~50–185 min | ~28–32 h |

The `everyone` mode runs ~25% slower than `wfa-ls` due to higher vote message volume; `top-stake-fraction` runs ~5% slower than `wfa-ls`. Plutus 50000 Gstep/EB is the fastest (collapse case — the EB flow halts so post-processing is small).

### check-progress.sh

Monitoring script. Reports any running `sim-cli`, `leios-trace-processor`, or `pigz -p 3 -9f` processes (so post-processing isn't mistaken for "no sim running"), plus tails of the sweep logs at `/tmp/{seed*-sweep,overnight-*}.log`.

### combine-results-multi-vote.sh

Collects results from a specific voting mode, topology, and seed into
`results/<MODE>/<TOPOLOGY>/` for `analysis.ipynb`.

```sh
bash combine-results-multi-vote.sh -m wfa-ls -s 0                          # default topology-v2
bash combine-results-multi-vote.sh -m wfa-ls -s 0 --topology topology-v2-1500
# then open analysis.ipynb (set MODE and TOPOLOGY in cell 5)
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
- **wfa-ls**: fixed threshold 450, probability split 480:120 persistent:non-persistent (sampled from staking nodes only; relays never win the lottery)
- **everyone**: every node in the topology votes (including zero-stake relays), threshold = ⌈total_nodes × 0.75⌉
- **top-stake-fraction**: top-stake nodes covering `committee-stake-fraction-threshold` (default 0.99) of total stake, threshold = ⌈top_n × 0.75⌉

Concrete values:

| Topology | Total | Stakers | Relays | wfa-ls thresh | everyone thresh | TSF thresh |
|---|---|---|---|---|---|---|
| `topology-v2` (750 nodes) | 750 | 458 | 292 | 450 | 563 | 160 (top-213) |
| `topology-v2-1500` | 1500 | 458 | 1042 | 450 | 1125 | 336 (top-448) |

Note that `everyone` and `top-stake-fraction` use *persistent* vote sizes/CPU costs (no VRF eligibility proof needed since selection is deterministic), so each individual vote is smaller and cheaper than a `wfa-ls` non-persistent vote. See `vote_weighted_average` in `sim-rs/sim-core/src/config.rs`.

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
behaviour (100% TX finalization at all NA throughputs and Plutus levels < 50000 tested).

## Memory and disk requirements

The dominant memory consumer during the sim phase is the per-node `txs` cache (~20 MB/node at high throughput); end-of-sim, the EventMonitor's 1-second sort window can spike RSS by 5–8 GB as buffered events flush.

| Topology / Throughput | Sim-phase peak RSS | Total commit (incl. event-monitor flush) |
|---|---|---|
| 750n / NA,0.150–0.250 | 20–30 GB | 30–35 GB |
| 750n / NA,0.300–0.350 + Plutus 1000–20000 | 30–35 GB | 35–40 GB |
| 1500n / NA,0.150–0.250 | 22–58 GB | 30–58 GB |
| 1500n / NA,0.300–0.350 + Plutus 1000–20000 | 50–60 GB | **60–65 GB → exceeds 60 GB physical, requires swap** |

The sequential engine sets `ulimit -S -v 256000000` (256 GB virtual address-space; needed because Rust+tokio reserves more virtual than it commits — a 96 GB cap broke 1500n runs at slot ~310 with `memory allocation failed` despite RSS only ~58 GB).

**Disk:** each completed run produces ~10 GB on `topology-v2`, ~25 GB on `topology-v2-1500` (the receipts.csv.gz dominates; everyone mode adds another ~5 GB of vote-receipt rows). A full 33-run 1500n sweep needs ~700 GB free disk. The `--memory-limit` flag's `linear-tx-max-age-slots` knob does little here: at our throughputs most TXs are too young to evict, so the savings are <2 GB. The peer-backlog cap clips real traffic and inflates retransmissions — net memory is not improved. **Use swap rather than memory limits for 1500n high-throughput.**
