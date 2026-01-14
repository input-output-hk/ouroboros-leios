# Demo: Proto-Devnet

A small network of patched cardano nodes that is loaded with synthetically created transactions. The same observability as with [the November demo](../2025-11) is available.

![Demo diagram](./demo-proto-devnet.excalidraw.svg)

> [!TIP]
> This is an excalidraw SVG with embedded scene so it can be loaded and edited in [https://excalidraw.com/].

## Getting started

### Using Nix (recommended)

Run the demo with all dependencies automatically provided:

``` shell
nix run github:input-output-hk/ouroboros-leios#demo-proto-devnet
```

Or enter the development shell and run manually:

``` shell
nix develop .#dev-demo-proto-devnet
./run.sh
```

The `nix develop` shell is also available via `direnv allow`.

### Without Nix

Install these prerequisites:

- `process-compose` - for orchestrating the demo processes
- `cardano-node` (patched with Leios support)
- `cardano-cli` - compatible with the cardano-node version
- `sqlite3` - for creating Leios databases
- `tx-generator` (optional) - for generating transaction workload

Set environment variables if the commands are not in your PATH:

``` shell
export CARDANO_NODE=/path/to/cardano-node
export CARDANO_CLI=/path/to/cardano-cli
```

Then run:

``` shell
./run.sh
```

## Using the demo

The demo will:

1. Initialize a 3-node cardano testnet in the `devnet/` directory
2. Create Leios databases for all nodes
3. Start all three nodes using process-compose

Once running, you can launch the transaction workload using `tx-generator`:

``` shell
tx-generator -- json_highlevel gen.json
```

Observe tip advancing and mempool size:

``` shell
export CARDANO_NODE_NETWORK_ID=164
export CARDANO_NODE_SOCKET_PATH=devnet/node1/node.socket
watch -n1 "cardano-cli query tip && cardano-cli query tx-mempool info"
```

## Configuration

You can customize the demo by setting environment variables before running. See `run.sh` for available options and their defaults:

``` shell
export WORKING_DIR=my-devnet
export CONFIG_DIR=/path/to/my/config
./run.sh
```

## Clean up

To reset the demo, simply remove the working directory:

``` shell
rm -rf devnet
```

## About the configuration

The `config/` directory contains pre-prepared configuration files for the 3-node devnet:

- Genesis files (shelley, alonzo, conway, dijkstra)
- Node configuration (`config.json`)
- Topology template (`topology.template.json`)
- Pool keys for 3 block-producing nodes (pool1, pool2, pool3)
- Stake delegators and UTxO keys

The configuration was originally created using `cardano-testnet`:

``` shell
cardano-testnet create-env --output config --num-pool-nodes 3 --slot-length 1 --testnet-magic 164 --params-mainnet
```

Then tuned to remove unnecessary components (Byron-era and governance-related files).
