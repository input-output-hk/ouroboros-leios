

# Demo Scripts for Leios Crypto Benchmarks

This folder contains scripts that orchestrate end-to-end demonstrations of BLS-based vote aggregation and certificate generation/verification for the Leios project.

## Prerequisites

- Build the CLI once from the repository root:

  ```bash
  cargo build --release -p crypto-benchmarks
  ```

  The resulting binary will be at:
  ```
  target/release/leios_crypto_benchmarks
  ```

- Ensure Python 3 is available with `cbor2` and `matplotlib` installed.  
  For example:

  ```bash
  python3 -m venv .venv
  source .venv/bin/activate
  pip install cbor2 matplotlib
  ```

- Make sure all scripts are executable:

  ```bash
  chmod +x scripts/*.sh
  ```

## Workflow

The scripts are designed to be run from the `demo/` directory.

### Run Step by Step (Manual Mode)

You can run each script individually to understand and control each step of the process for a given number of voters (e.g., 32). Use the `-d` option to specify the output directory (e.g., `run32`).

#### 10_init_inputs.sh

Initialize inputs for N voters:

```bash
scripts/10_init_inputs.sh -d run64 --pools 200 --stake 100000 --alpha 8 --beta 1
```

#### 20_make_registry.sh

Build the registry from initialized inputs:

```bash
scripts/20_make_registry.sh -d run64 -n 64
```

#### 30_cast_votes.sh

Cast votes with a specified fraction of voters voting (e.g., 1.0 means all vote):

```bash
scripts/30_cast_votes.sh -d run64 -f 0.75
```

#### 40_make_certificate.sh

Generate the aggregated certificate:

```bash
scripts/40_make_certificate.sh -d run64
```

#### 50_verify_certificate.sh

Verify the generated certificate:

```bash
scripts/50_verify_certificate.sh -d run64
```

#### 60_pretty_print_cert.sh

Pretty-print key metrics and statistics of the certificate:

```bash
scripts/60_pretty_print_cert.sh -d run64
```

### Run a Single End-to-End Demo

```bash
scripts/70_run_one.sh -d run64 -n 64 -f 0.75
```

This will:

1. Initialize inputs (`10_init_inputs.sh`)
2. Build a registry (`20_make_registry.sh`)
3. Cast votes (`30_cast_votes.sh`)
4. Make a certificate (`40_make_certificate.sh`)
5. Verify the certificate (`50_verify_certificate.sh`)
6. Pretty-print key metrics (`60_pretty_print_cert.sh`)

All files are placed in `demo/run64/`.

### Sweep Across Multiple N

```bash
scripts/80_sweep.sh -d sweep1 -f 1.0 --ns "32 64 128 256 512 1024 2056 3000"
```

This will run the full pipeline for multiple voter sizes (`N`) and write a CSV of results:

```
demo/sweep1/sweep_results.csv
```

### Plot Sweep Results

```bash
scripts/85_plot_sweep.sh -d sweep1 --open
```

This will generate a plot `gain_vs_N.png` showing compression ratio vs. number of voters.  
Use `--open` to automatically open the PNG.

## Notes

- All scripts must be run from within the `demo/` directory.
- Directories passed via `-d` will be created automatically under `demo/`.
- Compression ratio is defined as:

  ```
  votes_bytes / certificate_bytes
  ```

which illustrates the storage/bandwidth savings achieved by BLS aggregation.