# net-cli

Command-line tool for testing and demonstrating the Cardano N2N network stack. Connects to live Cardano nodes or runs local simulations using the `net-core` library.

## Commands

| Command | Description |
|---------|-------------|
| `handshake` | Connect to a node and perform version negotiation |
| `capture` | Record raw handshake bytes for test vectors |
| `chain-sync` | Follow chain tip via ChainSync (limited count, for debugging) |
| `block-fetch` | Fetch blocks via BlockFetch (finds tip via ChainSync first) |
| `follow` | Persistent single-peer chain follower with reconnection |
| `multi-follow` | Multi-peer chain follower via coordinator (supports `--listen`, `--duplex`, `--leios`) |
| `serve` | Run a fake Cardano node with Poisson block generation (supports `--leios`) |
| `submit` | Submit synthetic transactions via TxSubmission |
| `peer-share` | Request peers from a node via PeerSharing |

## Structure

```
src/
├── main.rs         # CLI definition (clap) and subcommand dispatch
├── connect.rs      # Re-exports net_core::peer::connect helpers
├── handshake.rs    # handshake command
├── capture.rs      # capture command (raw byte recording)
├── chainsync.rs    # chain-sync command
├── blockfetch.rs   # block-fetch command
├── follow.rs       # follow command (single-peer, reconnecting)
├── multi_follow.rs # multi-follow command (coordinator-based)
├── serve.rs        # serve command (fake node with Poisson generation)
├── submit.rs       # submit command (tx submission)
└── peershare.rs    # peer-share command
```

## Usage

All commands accept `--magic <N>` for network magic (defaults to mainnet 764824073).

### Live network testing

```sh
# Version handshake
cargo run -p net-cli -- handshake backbone.cardano.iog.io:3001

# Follow chain tip from multiple peers
cargo run -p net-cli -- multi-follow \
  --host backbone.cardano.iog.io:3001 \
  --host backbone.cardano.iog.io:3001

# Peer discovery
cargo run -p net-cli -- peer-share cardano-main2.everstake.one:3001

# Capture raw bytes for test vectors
cargo run -p net-cli -- capture backbone.cardano.iog.io:3001
```

### Local simulation

```sh
# Fake node with Poisson block generation
cargo run -p net-cli -- serve --port 9999 --block-rate 0.05

# Follow it
cargo run -p net-cli -- follow 127.0.0.1:9999

# Submit synthetic transactions
cargo run -p net-cli -- submit 127.0.0.1:9999 --tx-rate 2.0

# Relay mode: upstream mainnet, downstream local
cargo run -p net-cli -- multi-follow \
  --host backbone.cardano.iog.io:3001 \
  --listen 0.0.0.0:8888
```

### Leios simulation

```sh
# Fake node with Leios EB/vote generation
cargo run -p net-cli -- serve --port 9999 --block-rate 0.5 --leios

# Follow with Leios notifications
cargo run -p net-cli -- multi-follow --host 127.0.0.1:9999 --leios

# Multi-peer dedup (observe dedup/routing in logs)
RUST_LOG=debug cargo run -p net-cli -- multi-follow \
  --host 127.0.0.1:9999 \
  --host 127.0.0.1:9999 \
  --leios
```

## Dependencies

Beyond `net-core`, the CLI adds:

| Crate | Purpose |
|-------|---------|
| `clap` | Argument parsing with derive macros |
| `tracing-subscriber` | Log output formatting |
| `rand` | Poisson timing and synthetic data generation |
