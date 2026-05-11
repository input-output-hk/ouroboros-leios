# Linear Leios CIP simulation sweep (2026w18)

This directory holds the simulation study supporting the Linear Leios CIP, run
with `sim-rs` against the pseudo-mainnet topologies. It sweeps two axes:

- **Network load** — 5 throughput levels (0.150, 0.200, 0.250, 0.300, 0.350
  TxMB/s) with no Plutus, plus 6 Plutus levels (1000–50000 Gstep/EB at a fixed
  0.250 TxMB/s).
- **Voting committee** — three selection algorithms: `wfa-ls` (the CIP
  default), `everyone`, and `top-stake-fraction`.

Each combination is run on both the 750-node (`topology-v2`) and 1500-node
(`topology-v2-1500`) pseudo-mainnet networks, with a fixed RNG seed for
bit-identical reproducibility.

## Layout

```
2026w18/
├── experiments/             # one directory per (Plutus,throughput) case
│   ├── config.yaml          # shared scenario config (Praos/Leios params)
│   ├── NA,0.150/ … NA,0.350/
│   └── 1000,0.250/ … 50000,0.250/
├── results/                 # combined CSVs + R data, one tree per voting mode
│   └── <mode>/<topology>/   # cpus, lifecycle, receipts, resources, sizes
├── plots/                   # PNG/SVG figures rendered by analysis.ipynb
├── analysis.ipynb           # R-kernel notebook producing the plots
├── run-deterministic.sh     # per-experiment runner
├── run-sweep.sh             # sweep all 11 experiments for one voting mode
├── run-all-voting-modes.sh  # outer loop over all 3 voting modes
├── combine-results-multi-vote.sh   # collect outputs for analysis.ipynb
└── check-progress.sh        # status of any running sim / trace processor
```

## Prerequisites

- A built `sim-cli` (the symlink `sim-cli` in this directory should resolve to
  `sim-rs/target/release/sim-cli`).
- A built `leios-trace-processor` (the symlink in this directory points at the
  cabal build output).
- `pigz`, `jq`, `ansifilter`, `bc`, `python3` with `pyyaml`, and `R` with
  `data.table`, `ggplot2`, `magrittr`. The combine and run scripts shebang
  through `nix-shell` if you have nix; otherwise just have the binaries on
  `PATH`.
- About 700 GB of free disk for a full 1500-node sweep; ~150 GB for 750-node.
  See CLAUDE.md for the RAM table — 1500n high-throughput peaks at 60–65 GB
  and assumes swap is available.

## Running a sweep

```sh
# Full matrix: 3 voting modes × 11 experiments, default 750-node topology
bash run-all-voting-modes.sh

# Just the 1500-node NA throughput sweep
bash run-all-voting-modes.sh --na-only --topology topology-v2-1500

# A single mode + topology + seed
bash run-sweep.sh -m wfa-ls -s 0 --topology topology-v2-1500

# One experiment (must `cd` into its directory first)
cd experiments/NA,0.250
bash ../../run-deterministic.sh -m top-stake-fraction -s 0
```

While a sweep runs, `bash check-progress.sh` reports any live `sim-cli`,
`leios-trace-processor`, or `pigz` processes and tails the standard sweep log
locations under `/tmp/`.

Each run writes its output to a `{voting-mode}/{topology}/seed-{N}/`
subdirectory of the experiment, and drops a `done` marker only after the full
trace-processing pipeline completes. The combine script uses `done` (not an
empty `stderr`) to decide which runs to include, so partial/OOM-killed runs
naturally drop out.

## Producing analysis

After (or alongside) a sweep, collect outputs for one mode/topology:

```sh
bash combine-results-multi-vote.sh -m wfa-ls -s 0                          # 750-node
bash combine-results-multi-vote.sh -m wfa-ls -s 0 --topology topology-v2-1500
```

This populates `results/<mode>/<topology>/` with combined `.csv.gz` and
`.Rdata` files. Then open `analysis.ipynb` in Jupyter (an R kernel — the
notebook uses `data.table`/`ggplot2`) and set the `MODE` and `TOPOLOGY`
variables in the third code cell. Re-running the notebook regenerates the
figures under `plots/`.

## Voting modes

| Mode | Committee | Threshold | Notes |
|------|-----------|-----------|-------|
| `wfa-ls` | weighted Fait-accompli with local sortition; sampled from staking nodes | fixed 450 | CIP default. 480 persistent + 120 non-persistent votes per EB. |
| `everyone` | every node in the topology (including zero-stake relays) | ⌈total × 0.75⌉ | Useful as an upper-bound on vote-message volume. |
| `top-stake-fraction` | top-stake nodes covering 99% of total stake | ⌈top_n × 0.75⌉ | Smaller, deterministic committee; same votes are persistent-style. |

Concrete committee sizes for the two production topologies are in CLAUDE.md.

## Engines

`run-deterministic.sh` accepts three engine modes:

- `--turbo` (default) — sequential DES with 6 shards and the
  zero-latency-clusters strategy. Deterministic, ~5× faster than the actor
  engine. This is what the CIP sweep uses.
- `--sequential` — single-shard sequential DES. Deterministic but slower.
- `--actor` — async tokio actor system. Most faithful to real network timing
  but non-deterministic and slow (~90 min/experiment).

## Reproducibility

With turbo or sequential engine plus a fixed seed, every output file (modulo
gzip header timestamps) is bit-identical across re-runs. Different seeds
produce different RB lottery outcomes but the same protocol behaviour.

## More detail

`CLAUDE.md` in this directory has the in-depth reference: option-by-option
flag tables, the full output directory tree, the RAM/disk requirements per
topology and throughput, and notes on why specific limits and ulimits are
set the way they are.
