# Leios technical-feasibility report

Report for ouroboros-leios issue 1127 (milestone LS.01): the Leios pipeline
measured stage by stage against its timing constraints on the public testnet
and on the benchmarking cluster, with the ledger benchmark and the DeltaQ /
CIP models alongside, and the parameter set the measurements confirm.

This folder holds the sources of `docs/feasibility-report.md`, the report
one level up, and everything needed to reproduce its tables. The report is
rebuilt from here with:

    python3 docs/feasibility-report/scripts/build.py --out docs/feasibility-report.md

**Held back for now.** The per-node outputs of the testnet windows and the
cluster runs (`diffusion.csv` and `.md`, `diffusion-body.csv` and `.md`,
`validation_nodes.csv`, `tally_quorum_nodes.csv` and `voters.csv` under
each window) carry the operators' agent names, pool ids and tickers, one
row per node. Whether they are published as they are or pseudonymised is
not decided, so they are not in this copy; until they are, the stage
table's rows that read them (the body, closure, applied-share, validation,
tally, vote-rate rows and the reporting-weight captions) print as n/a
when regenerated from here, and the instruments regenerate them from the
data sets of DATA.md.

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
| `instruments/testnet_window.sh`, `cluster_run.sh` | everything above for one window or run | the data sets, by path |

The SQL instruments take their inputs as DuckDB variables (`t0`, `t1`,
`win`, `chain`, `committee`, `gap`) and write their CSVs into the working
directory; the drivers set all of that. Every printer accepts `--outputs`
(default `outputs/`) and, where it reads a chain cache, `--data` (default
the parent of this repository, the analysis folder where DATA.md's sets
live).
