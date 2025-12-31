# Leios demo

This is a collection of Leios demonstrations created using specially patched versions of `cardano-node` and other components not originating from this repository:

This folder contains the latest demo.

Previous demos:

- [2025-10](2025-10/): Minimum viable demo of Leios network traffic interfering with Praos
- [2025-11](2025-11/): Improvement of MVD using tc and better observability

There are other, component-specific demos you might be looking for:

- [Visualizer](../ui) contains a few stored scenarios that are standalone demos
- [Cryptography](../crypto-benchmarks.rs/demo) demo of signing/verifying votes and certificates
- [Trace translator](../scripts/trace-translator/demo) has an example/demo

## Prototypes

Leios prototyping is visibile in the following PRs:

1. [cardano-node](https://github.com/IntersectMBO/cardano-node/pull/6386)
2. [ouroboros-consensus](https://github.com/IntersectMBO/ouroboros-consensus/pull/1793)
3. [ouroboros-network](https://github.com/IntersectMBO/ouroboros-network/tree/nfrisby/leios-202511-demo)

All prototyping artifacts are in their `leios-prototype` branch.
For each demo a special tag `leios-prototype-demo-YYYYMM` will be attached to denote the components used in the demo for a particular month.

## Running the Leios demo

### Running the demo

The latest demo can be run directly from GitHub using Nix:

```shell
nix run github:input-output-hk/ouroboros-leios#leios-demo
```

Or from a local checkout:

```shell
nix run .#leios-demo
```

For previous demos:

```shell
# November 2025 demo
nix run .#demo-2025-11

# October 2025 demo
nix run .#demo-2025-10
```

**Note:** The demo requires sudo privileges to create network namespaces and configure traffic control. When the process-compose UI starts, navigate to the `InitNamespaces` process and provide your password when prompted. This is needed to simulate isolated network environments with realistic bandwidth and latency constraints between the nodes.

## Background Concepts

Before diving into configuration and customization, it's helpful to understand the key components and concepts used in the demo.

### Demo Architecture

The demo simulates a three-node Cardano network to test how Leios traffic interacts with Praos block diffusion:

- **Upstream Node**: A mock peer that serves pre-generated Praos blockchain data and injects Leios traffic
  - Runs `immdb-server`: Serves blocks from the immutable database and sends scheduled Leios notifications
  - The immutable blocks are served from the directory specified by the `CLUSTER_RUN` configuration variable (see [Configuring the experiment](#configuring-the-experiment))
  - Controlled by an EB schedule (see [EB schedules](#eb-schedules)) that specifies when to send each Endorsement Block
  - The schedule is generated from a [manifest file](#manifest-files) using the [`leiosdemo202510` tool](#generating-eb-schedules-and-databases)

- **Node 0**: A real `cardano-node` that receives both Praos and Leios traffic
  - This is the node under test - we measure its performance under Leios load

- **Downstream Node**: Another `cardano-node` that receives blocks from Node 0
  - Used to measure block propagation delays from the upstream node

Network conditions (bandwidth, latency) between nodes can be configured using [tc](https://man7.org/linux/man-pages/man8/tc.8.html).

### Timing Concepts

The demo uses several timing-related concepts to control when blocks and EBs are sent:

- **REF_SLOT** and **ONSET_OF_REF_SLOT**: Define the transition from fast replay to real-time. The `immdb-server` sends all Praos blocks before `REF_SLOT` immediately (rapid catch-up), then waits until `ONSET_OF_REF_SLOT` and begins real-time transmission for blocks at `REF_SLOT` and onwards.
- **EB_RELEASE_OFFSET**: Slot number offset that positions EBs at specific points in the blockchain timeline. The offset is added to base schedule slot numbers at runtime (see [EB schedules](#eb-schedules) for examples).

## Configuring the experiment

The demo can be configured by setting environment variables before running:

```shell
# Core executables
CARDANO_NODE=cardano-node
IMMDB_SERVER=immdb-server

# Data and configuration
DATA_DIR=data
CLUSTER_RUN=data/2025-10-10-13-29-24641-1050-50-blocks-50-coay-sup
REF_SLOT=41
SECONDS_UNTIL_REF_SLOT=5
LEIOS_MANIFEST=manifest.json

# Analysis tools
ANALYZE=analyse.py
PYTHON3=python

# Network parameters (for 2025-11 demo onwards, using tc)
RATE_UP_TO_N0="100Mbps"
DELAY_UP_TO_N0="20ms"
RATE_N0_TO_UP="100Mbps"
DELAY_N0_TO_UP="20ms"
RATE_N0_TO_DOWN="100Mbps"
DELAY_N0_TO_DOWN="20ms"
RATE_DOWN_TO_N0="100Mbps"

# Leios timing
EB_RELEASE_OFFSET=128.9
```

**Key configuration variables:**

- **CLUSTER_RUN**: Path to pre-generated Praos blockchain data (immutable database and genesis files)
- **REF_SLOT**, **SECONDS_UNTIL_REF_SLOT**: Timing anchor for real-time execution (see [Timing Concepts](#timing-concepts))
- **LEIOS_MANIFEST**: Manifest file defining EB contents and timing (see [Manifest files](#manifest-files))
- **EB_RELEASE_OFFSET**: Slot offset for positioning EBs in the timeline (see [Timing Concepts](#timing-concepts))
- **RATE_***, **DELAY_***: Network bandwidth and latency parameters for tc (traffic control)

Example of running with custom configuration:

```shell
SECONDS_UNTIL_REF_SLOT=10 REF_SLOT=200 nix run .#leios-demo
```

### Using locally built binaries

To use locally built `cardano-node` and `immdb-server` executables instead of the Nix-provided ones:

```shell
# Set paths to your locally built binaries
export CARDANO_NODE=$(cd ~/code/iog/cardano-node; cabal list-bin cardano-node)
export IMMDB_SERVER=$(cd ~/code/iog/ouroboros-consensus; cabal list-bin immdb-server)

# Run the demo with your local binaries
nix run .#leios-demo
```

This is useful for testing changes to the Leios prototype before they are merged.

### Cleanup

To clean up temporary files created by the demo:

```shell
# For latest demo
rm -fr .tmp-leios-demo

# For 2025-11 demo
rm -fr .tmp-leios-202511-demo
rm -fr .tmp-x-ray

# For 2025-10 demo
rm -fr ./leios-run-tmp-dir
```

## Understanding the Data Pipeline

This section explains the data flow from manifest definition to demo execution: Manifest → Database + Base Schedule → Runtime Offset → Final Schedule → Demo Execution.

### Manifest files

EB schedules and their associated databases are generated using a manifest file which defines the timing of the EBs and their contents.

The basic structure of a manifest is as follows:

```json
[
  {
    "slotNo": <number>,
    "nickname": "<optional-name>",
    "comment": "<optional-description>",
    "txRecipes": [<recipe>, <recipe>, ...]
  }
]
```

Where the fields are:

- **`slotNo`**: The slot number where this EB will be created (required)
- **`nickname`**: An optional friendly name that can be referenced by other EBs to share transactions
- **`comment`**: Optional documentation describing the purpose or characteristics of this EB
- **`txRecipes`**: An array defining the transactions in this EB. Each recipe can be:
  - A simple integer representing the transaction size in bytes (e.g., `16384` for a 16KB transaction)
  - An object referencing transactions from another EB: `{"share": "<nickname>", "startIncl": <index>, "stopExcl": <index>}`
    - `share`: References the `nickname` of a previously defined EB
    - `startIncl`: Starting index (inclusive) of transactions to copy
    - `stopExcl`: Ending index (exclusive) of transactions to copy (optional, if omitted, copies all transactions from `startIncl` onwards)

Below is an example of a simple manifest with direct transaction sizes:

```json
[
  {
    "slotNo": 0,
    "nickname": "SmallEB",
    "comment": "Small EB with 4 transactions totaling ~18KB",
    "txRecipes": [500, 600, 700, 16584]
  },
  {
    "slotNo": 1,
    "nickname": "LargeEB",
    "comment": "Large 12.5 MB EB",
    "txRecipes": [15390, 16384, 16384, 16384]
  }
]
```

The following example shows a manifest with shared transactions:

```json
[
  {
    "slotNo": 0,
    "nickname": "BaseEB",
    "txRecipes": [500, 600, 700, 800, 900]
  },
  {
    "slotNo": 1,
    "nickname": "DerivedEB",
    "comment": "Reuses transactions 1-3 from BaseEB",
    "txRecipes": [
      {"share": "BaseEB", "startIncl": 1, "stopExcl": 4},
      1000,
      2000
    ]
  },
  {
    "slotNo": 2,
    "nickname": "MixedEB",
    "comment": "Mix of shared and new transactions",
    "txRecipes": [
      {"share": "BaseEB", "startIncl": 0},
      {"share": "DerivedEB", "startIncl": 0, "stopExcl": 2},
      5000
    ]
  }
]
```

### Generating EB schedules and databases

To generate an EB schedule and its associated database, use the `leiosdemo202510` tool:

```bash
# Generate the Leios database and base schedule
leiosdemo202510 generate output.db myManifest.json base-schedule.json
```

This produces:

- `output.db`: SQLite database with EB and transaction data
- `base-schedule.json`: Initial schedule with timing information

The schedule and database can be passed to `immdb-server` as follows:

```bash
# Run immdb-server with the generated database and schedule
immdb-server \
  --db /path/to/immutable/ \
  --config config.json \
  --initial-slot 41 \
  --initial-time $ONSET_OF_REF_SLOT \
  --leios-schedule schedule.json \
  --leios-db output.db \
  --port 3001
```

### EB schedules

EB schedules are JSON files that specify when Endorsement Blocks (EBs) should be sent over the network during a Leios demo.

**Schedule entry format:**

Each entry contains a **slot number** (fractional) and EB metadata:

```json
[schedule_slot, [eb_id, eb_hash, optional_size]]
```

- `schedule_slot` (Double): Fractional slot number when the message should be sent
- `eb_id` (Word64): EB identifier (0-9 in default manifest)
- `eb_hash` (Text): Hex-encoded EB block hash
- `optional_size` (Maybe Word32): EB body size if present, `null` otherwise

**Example schedule** (with default `EB_RELEASE_OFFSET=128.9`):

```json
[
  [129.0, [0, "adfe0e24083d8dc2fc6192fcd9b01c0a2ad75d7dac5c3745de408ea69eaf62d8", 28234]],
  [129.1, [0, "adfe0e24083d8dc2fc6192fcd9b01c0a2ad75d7dac5c3745de408ea69eaf62d8", null]],
  [130.0, [1, "bd384ce8792d89da9ab6d11d10fc70a36a2899e6c3b10d12345...", 28234]],
  [130.1, [1, "bd384ce8792d89da9ab6d11d10fc70a36a2899e6c3b10d12345...", null]]
]
```

**Understanding the entries:**

Each EB generates **two messages**:
1. **Block offer** (with size): Slot 129.0 for EB 0, slot 130.0 for EB 1
2. **Transactions offer** (without size): Slot 129.1 for EB 0, slot 130.1 for EB 1

**How `immdb-server` uses the schedule:**

The slot numbers are converted to wall-clock times using:
```
send_time = ONSET_OF_REF_SLOT + (schedule_slot - REF_SLOT)
```

With `REF_SLOT=41` and `ONSET_OF_REF_SLOT=1735561000`:
- Slot 129.0 → sends at `1735561000 + (129.0 - 41) = 1735561088` (unix timestamp)
- Slot 129.1 → sends at `1735561000 + (129.1 - 41) = 1735561088.1`
- Slot 130.0 → sends at `1735561000 + (130.0 - 41) = 1735561089`

The EBs corresponding to the hashes in the schedule can be found in the associated SQLite database (specified with `--leios-db`), in the `ebPoints` and `ebTxs` tables. The hash in the schedule matches the `ebHashBytes` field in the `ebPoints` table, which links to the EB's transactions in the `ebTxs` table.

Schedules allow precise timing of Leios traffic to overlap with Praos block diffusion, testing scenarios like the [ATK-LeiosProtocolBurst](../docs/leios-design/README.md#protocol-bursts) attack.

### EB and transactions database

The SQLite database associated to an EB schedule contains:

 - txCache table: Transaction storage
    - txHashBytes: Transaction hash (primary key)
    - txBytes: CBOR-encoded transaction data
    - txBytesSize: Size in bytes
    - expiryUnixEpoch: Expiration timestamp
  - ebPoints table: EB metadata
    - ebSlot: Slot number
    - ebHashBytes: EB hash
    - ebId: Internal identifier
  - ebTxs table: EB-transaction mappings
    - ebId: References ebPoints.ebId
    - txOffset: Transaction position within EB
    - txHashBytes: References txCache.txHashBytes
    - txBytesSize: Transaction size
    - txBytes: Transaction data (nullable)

## Pre-generating Leios databases and schedules

You can pre-generate Leios databases and EB schedules independently from running the demo.

#### Basic generation

```shell
# Generate with default settings
nix run .#generate-leios-db

# Outputs to ./leios-data/ by default:
#   - leios.db           # SQLite database with EB and transaction data
#   - base-schedule.json # Base schedule with relative timing (before offset is applied)
```

**Note:** The final `schedule.json` (with `EB_RELEASE_OFFSET` applied) is generated at runtime by the demo, allowing you to test different release timings without regenerating the database.

#### Custom output location and manifest

```shell
# Specify output directory
nix run .#generate-leios-db ./my-leios-data

# Specify both output directory and custom manifest
nix run .#generate-leios-db ./my-leios-data ./my-manifest.json
```

**Note:** For details on how EB_RELEASE_OFFSET and timing work, see [Timing Concepts](#timing-concepts) in the Background Concepts section.

#### Using pre-generated data with the demo

Once you've generated the database and base schedule, use them with the demo:

```shell
# Run demo with pre-generated files (EB_RELEASE_OFFSET applied at runtime)
LEIOS_DB=./leios-data/leios.db \
  LEIOS_BASE_SCHEDULE=./leios-data/base-schedule.json \
  nix run .#leios-demo

# Or with custom EB release offset
LEIOS_DB=./leios-data/leios.db \
  LEIOS_BASE_SCHEDULE=./leios-data/base-schedule.json \
  EB_RELEASE_OFFSET=150.0 \
  nix run .#leios-demo
```

#### Workflow examples

**Testing different network conditions with same data:**

```shell
# Generate once
nix run .#generate-leios-db ./test-data

# Run multiple tests with different network parameters
LEIOS_DB=./test-data/leios.db LEIOS_BASE_SCHEDULE=./test-data/base-schedule.json \
  RATE_UP_TO_N0="50Mbps" nix run .#leios-demo

LEIOS_DB=./test-data/leios.db LEIOS_BASE_SCHEDULE=./test-data/base-schedule.json \
  RATE_UP_TO_N0="200Mbps" nix run .#leios-demo
```

**Testing different release timings (without regenerating database):**

```shell
# Generate base data once
nix run .#generate-leios-db ./timing-test

LEIOS_DB=./timing-test/leios.db \
  LEIOS_BASE_SCHEDULE=./timing-test/base-schedule.json \
  EB_RELEASE_OFFSET=100.0 nix run .#leios-demo

```

**Advanced: Using a fully custom schedule (bypasses EB_RELEASE_OFFSET):**

If you need complete control over timing, you can provide a final schedule that bypasses runtime `EB_RELEASE_OFFSET` application:

```shell
# Pre-generate with specific timing
nix run .#generate-leios-db ./custom-data

# Manually create custom schedule with your own timing logic
jq "map(.[0] = custom_timing_function)" ./custom-data/base-schedule.json > ./custom-data/my-schedule.json

# Use the custom schedule (EB_RELEASE_OFFSET will be ignored)
LEIOS_DB=./custom-data/leios.db \
  LEIOS_SCHEDULE=./custom-data/my-schedule.json \
  nix run .#leios-demo
```

**Note:** If `LEIOS_DB` is not provided, the demo will automatically generate it along with the base schedule.

## Flake inputs

The repository pulls in patched cardano-node and ouroboros-consensus as visible
in [flake.nix](../flake.nix):

```nix
    cardano-node.url = "github:intersectmbo/cardano-node?ref=...";

    ouroboros-consensus.url = "github:intersectmbo/ouroboros-consensus?ref=...";
```

To point to newer/different versions you want to set the appropriate
[ref](https://git-scm.com/book/en/v2/Git-Internals-Git-References).

> The refs in these two URLs need to identify commits that have up-to-date
> source-repository-packages for the custom commits used in ouroboros-network,
> ouroboros-consensus, cardano-node.

```shell
nix flake lock --update-input cardano-node --update-input ouroboros-consensus
```

## build.nix convention

Every `build.nix` files is a [flake-parts module](https://flake.parts/) and is
automatically loaded when found.

## Using the repository

Enter the shell either by

```shell
nix develop .#dev-demo
```

or if you're using Direnv the shell will automatically load once you

```shell
direnv allow
```

To invoke code formatting and checks on the entire repo use

```shell
$ nix fmt
black................................................(no files to check)Skipped
deadnix..................................................................Passed
markdownlint.............................................................Passed
nixfmt-rfc-style.........................................................Passed
shellcheck...............................................................Passed
```

or alternatively in the shell

```shell
$ pre-commit run --all
black................................................(no files to check)Skipped
deadnix..................................................................Passed
markdownlint.............................................................Passed
nixfmt-rfc-style.........................................................Passed
shellcheck...............................................................Passed
```

This repository is using
[git-hooks.nix](https://github.com/cachix/git-hooks.nix) and you can manage them in:

1. [top level configuration](../pre-commit-hooks.nix).
1. [demo configuration](./pre-commit-hooks.nix).
