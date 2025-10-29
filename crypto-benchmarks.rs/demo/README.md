

# Demo Scripts for Leios Crypto Benchmarks

This folder contains scripts that orchestrate end-to-end demonstrations of BLS-based vote aggregation and certificate generation/verification for the Leios project.

## Prerequisites

- Ensure the CLI built from the repository root is available; see `crypto-benchmarks.rs/ReadMe.md` for build instructions and usage details.
- Ensure Python 3 is available with `cbor2` installed.  
  For example:

  ```bash
  python3 -m venv .venv
  source .venv/bin/activate
  pip install cbor2
  ```

## Workflow

The scripts are designed to be run from the `demo/` directory.

### Run Step by Step (Manual Mode)

You can run each script individually to understand and control each step of the process for a given number of voters (e.g., 100). Use the `-d` option to specify the output directory (e.g., `run100`).

#### 10_init_inputs.sh

Initialize inputs for N voters:

```bash
scripts/10_init_inputs.sh -d run100 --pools 500 --stake 100000 --alpha 9 --beta 1
```

#### 20_make_registry.sh

Build the registry from initialized inputs:

```bash
./scripts/20_make_registry.sh -d run100 -n 100
```

#### 30_cast_votes.sh

Cast votes with a specified fraction of voters voting (e.g., 1.0 means all vote):

```bash
scripts/30_cast_votes.sh -d run100 -f 0.75
```

#### 40_make_certificate.sh

Generate the aggregated certificate:

```bash
scripts/40_make_certificate.sh -d run100
```

#### 50_verify_certificate.sh

Verify the generated certificate:

```bash
scripts/50_verify_certificate.sh -d run100
```

### Run a Single End-to-End Demo

```bash
scripts/70_run_one.sh -d run100 -p 500 -n 100 -f 0.75
```

This will:

1. Initialize inputs (`10_init_inputs.sh`)
2. Build a registry (`20_make_registry.sh`)
3. Cast votes (`30_cast_votes.sh`)
4. Make a certificate (`40_make_certificate.sh`)
5. Verify the certificate (`50_verify_certificate.sh`)
6. Export data for the UI (`60_export_demo_json.sh`)

All files are placed in `demo/run100/`.

### Launch the Demo UI

After generating a demo run (for example via `scripts/70_run_one.sh`), start the UI server from this directory:

```bash
python3 ui/server.py
```

Then open your browser at [http://127.0.0.1:5050/ui](http://127.0.0.1:5050/ui) to explore the results.

## Notes

- All scripts must be run from within the `demo/` directory.
- Directories passed via `-d` will be created automatically under `demo/`.
- Compression ratio is defined as:

  ```
  votes_bytes / certificate_bytes
  ```

which illustrates the storage/bandwidth savings achieved by BLS aggregation.
