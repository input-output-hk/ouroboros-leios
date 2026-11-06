# Leios technical-feasibility report

Report for ouroboros-leios issue 1127 (milestone LS.01): the Leios pipeline
measured stage by stage against its timing constraints on the public testnet
and on the benchmarking cluster, with the ledger benchmark and the DeltaQ /
CIP models alongside, and the parameter set the measurements confirm.

This folder holds the sources of `docs/feasibility-report.md`, the report
one level up, and everything needed to reproduce its tables. The report is
rebuilt from here with:

    python3 docs/feasibility-report/scripts/build.py --out docs/feasibility-report.md

**Per-node outputs.** The per-node outputs of the testnet windows
(`diffusion.csv`, `diffusion-body.csv`, `validation_nodes.csv`,
`tally_quorum_nodes.csv` and `voters.csv` under each window) are
published with every node and pool numbered (n1, n2, … and p1, p2, …,
one number per node across the windows) in place of the agent names,
hostnames and pool ids, and the operators' ticker column emptied, by
`scripts/publish_outputs.py`; the IOG and PIR hosts keep their labels
(IOG1 to IOG3, PIR1 to PIR10, the pool tickers the report uses) next to
their number, in `data/hosts.csv` as well. The printers read the files
unchanged, so every table regenerates from here. The mapping from numbers
to agent names, hostnames and pool ids is held by the author and
available to reviewers on request. The Markdown views of the diffusion
files are not published.

Layout:

- `report/`: the report in Markdown, one file per section as they are
  drafted, assembled by `scripts/build.py`. The open points the text
  leaves for the team and the reviewers sit in the section files between
  `<!-- note -->` and `<!-- /note -->` and the build renders them in place
  as block quotes headed "Note to resolve".
- `scripts/`: the printers, one per family of tables, which read the saved
  outputs and print the report's tables; and `scripts/build.py`.
- `scripts/instruments/`: the instruments, which read a data set (DATA.md)
  and write the saved outputs of one window or run; two drivers run them
  all for a testnet window (`testnet_window.sh`) or a cluster run
  (`cluster_run.sh`).
- `outputs/<window>/`: the saved outputs per testnet window (`f1-high`,
  `f2-high`, `1kb`, with `archive-only/` for the SPO-archive-only check) and
  per cluster run (`cluster-40k260k`, `cluster-100k1m`, `cluster-100k1m-374`),
  small text files committed with the scripts so that every table is
  reproducible from the repository alone: run the printer; to regenerate
  the outputs from the data sets, run the driver first.
- `data/windows/`: the loaded hours of each testnet window, the files the
  instruments and printers restrict to.
- `DATA.md`: the data sets the instruments read (origin, period, size,
  hash). They are not in this repository, and neither are the scripts that
  acquire or build them: anything that reaches the explorer, the telemetry
  archive, the IOG monitoring or the db-sync instance, or holds a credential,
  stays in the analysis folder and is described, not shipped (Appendix A.4).

Printers (section, what they print, what they read under `outputs/`):

| printer | section | reads |
|---|---|---|
| `scripts/build.py` | the whole report, `report/REPORT.md`, with the notes to resolve as block quotes; `--html` also writes the self-contained preview page next to it | the section files `report/*.md` and the repository's commit |
| `scripts/mainnet_blocks.py` | 1, the fetch of the mainnet data set; the one fetcher kept in the repository, because its source (Koios) is public and keyless and a reviewer can repeat it | Koios: block headers and epoch parameters per epoch into the mainnet data set (DATA.md) |
| `scripts/mainnet_praos.py`, `scripts/mainnet_windows.sh` | 1, the congestion-windows table (Praos under load) | the mainnet data set, `$LEIOS_MAINNET` (instrument and printer in one) |
| `scripts/ladder_table.py` | 4, table (a), the ladder per parameter set | `<window>/ladder.jsonl` |
| `scripts/stage_table.py` | 4, table (b) and the 4.3 closure-tail sub-table; `--archive-only` for the check column | `<window>/diffusion.csv`, `diffusion-body.csv`, `validation_nodes.csv`, `tally_quorum_nodes.csv`, `tally_quorum_ebs.csv`, `closure_fleet_per_eb.csv`, `voters.csv` |
| `scripts/eb_composition.py` | 4.3.1, the EB classes of the 1 kB window | the chain cache (`--data`) and `1kb/eb_composition_dbsync.csv`, the certified closures' composition written outside the repository by the db-sync query |
| `scripts/praos_table.py` | 5, Tables 5.1 to 5.5 (`kinds`, `adoption`, `pairs`, `density`, `control`), the `path` table behind 5.3's timings, `--trickle` for the density rows of 5.5's note | `<window>/adoption.md`, `pairs.md`, `adoption_path.md`, `forge_path.md`; the chain caches (`--data`) for `kinds` and `density` |
| `scripts/cost_table.py` | 6, Table 6.1 (`bins`), 6.2 (`unseen`), 6.5 (`resources`); `fit` for section 7 and `speed` for section 8 | `<window>/validation_bins.md`, `host_speed.md`, `resources.md`, `validation_fit.md` |
| `scripts/diffusion_table.py` | 6, Tables 6.3 (`bins`) and 6.4 (`upstream`) | `<window>/diffusion_bins.csv`, `upstream.csv` |

Instruments (what they write under `outputs/<window>/`, from which data set):

| instrument | writes | reads |
|---|---|---|
| `instruments/ladder.py ceiling`, `sizes` | `ladder.jsonl`, `ladder.md`, `sizes.md` | the chain cache (and the committee file for the caps) |
| `instruments/diffusion_nodes.py` | `diffusion.csv`/`.md` (closure stage), `diffusion-body.csv`/`.md` (body stage) | a period database or a cluster run's trace table, the chain cache |
| `instruments/validation_pairs.sql`, `cluster_validation_pairs.sql` | `validation_nodes.csv` (per node); the per-pair `validation_pairs.csv`, tens of MB, stays outside | a period database or a cluster run |
| `instruments/tally_quorum.sql`, `cluster_tally_quorum.sql` | `tally_quorum_nodes.csv`, `tally_quorum_ebs.csv`, `tally.md` | a period database or a cluster run, the chain cache |
| `instruments/closure_fleet.sql` | `closure_fleet_per_eb.csv`, `closure_fleet.md` | a period database, the chain cache |
| `instruments/closure_never.sql` | `closure_never.md` | a period database, the chain cache |
| `instruments/coverage.sql` | `voters.csv`, `coverage.md` (the reporting weight) | a period database, the chain cache and the committee file |
| `instruments/adoption_delay.sql`, `cluster_adoption.sql` | `adoption.md` (adoption delay by RB kind; the leader slots of the observed hosts) | a period database or a cluster run, the chain cache |
| `instruments/consecutive_pairs.sql`, `cluster_forks.sql` | `pairs.md` | a period database or a cluster run, the chain cache |
| `instruments/adoption_path.sql`, `cluster_adoption_path.sql` | `adoption_path.md` | a period database or a cluster run, the chain cache |
| `instruments/forge_path.py` | `f2-high/forge_path.md` | the archived IOG monitoring pulls of the 2 MB period, the chain cache |
| `instruments/validation_bins.py` | `validation_bins.md` (validation time per EB by applied-share bin on the window's most common EB size class, host classes from `data/hosts.csv` and the operators' quartiles) | the per-pair `validation_pairs.csv` of the window or run (outside) |
| `instruments/validation_fit.py` | `validation_fit.md` (the least-squares fit: fixed cost per EB, rate per applied and per reapplied transaction; section 7) | the same |
| `instruments/host_speed.py` | `host_speed.md` (certification and throughput on faster hosts; failures by applied share; cluster runs) | the same, `ladder.jsonl` |
| `instruments/resources.py` | `resources.md` (memory and CPU distributions; the IOG and PIR hosts by instance class) | the period database's metric scrapes and the archived monitoring series (testnet), `raw/Resources.db` (cluster) |
| `instruments/diffusion_bins.py` | `diffusion_bins.csv`, `upstream.csv` (nodes per p90 bin; nodes by upstream peers with committee weight) | `diffusion.csv`, `diffusion-body.csv`, `voters.csv`, `upstream_hosts.csv` in the window's folder |
| `instruments/peers_upstream.py` | `upstream_hosts.csv` (the IOG and PIR hosts' upstream peers) | the archived per-peer announcement pulls (DATA.md) |
| `instruments/testnet_window.sh`, `cluster_run.sh` | everything above for one window or run | the data sets, by path |

The SQL instruments take their inputs as DuckDB variables (`t0`, `t1`,
`win`, `chain`, `committee`, `gap`) and write their CSVs into the working
directory; the drivers set all of that. Every printer accepts `--outputs`
(default `outputs/`) and, where it reads a chain cache, `--data` (default
the parent of this repository, the analysis folder where DATA.md's sets
live).
