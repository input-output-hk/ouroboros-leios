# Demo: Proto-Devnet

A small network of patched cardano nodes that is loaded with synthetically created transactions. The same observability as with [the November demo](../2025-11) is available.

![Demo diagram](./demo-proto-devnet.excalidraw.svg)

> [!TIP]
> This is an excalidraw SVG with embedded scene so it can be loaded and edited in [https://excalidraw.com/].

## Getting started

Run the demo with all dependencies automatically provided using nix:

``` shell
nix run github:input-output-hk/ouroboros-leios#demo-proto-devnet
```

Or enter the `nix develop` shell (also available via `direnv allow`) and follow [without nix instructions](#without-nix).

### Without Nix

Install these prerequisites:

- `process-compose` for orchestrating the demo processes
- `cardano-node` patched with Leios support
- `cardano-cli` compatible with the cardano-node version
- `sqlite3` for creating Leios databases
- `jq` and `envsubst` for config modifications
- `tx-generator` (optional) for generating transaction workload

Ensure they are on your PATH, override if needed with something like:

``` shell
export PATH=/path/to/cardano-node:/path/to/cardano-cli:$PATH
```

Then run:

``` shell
./run.sh
```

## What's included

This `process-compose` orchestrated demo will:

1. Initialize a three node cardano devnet
2. Start all three nodes
3. Generate and submit a transaction workload using `tx-generator`
4. Observes tip advancing and mempool size (more observability come later):

``` shell
export CARDANO_NODE_NETWORK_ID=164
export CARDANO_NODE_SOCKET_PATH=devnet/node1/node.socket
watch -n1 "cardano-cli query tip && cardano-cli query tx-mempool info"
```

## Configuration

You can customize the demo by setting environment variables before running. See `run.sh` for available options and their defaults:

``` shell
export WORKING_DIR=my-devnet
./run.sh
```

## Observability with X-ray

Proto-devnet generates an Alloy configuration for use with the X-ray observability stack.

To use it:

1. Start proto-devnet (using one of the methods above)

2. In another terminal, start x-ray with the generated config:

    **Using nix:**

    ``` shell
    ALLOY_CONFIG="$(realpath tmp-devnet/alloy)" nix run github:input-output-hk/ouroboros-leios#x-ray
    ```

    **Without nix:**

    ``` shell
    cd ../extras/x-ray
    ALLOY_CONFIG="$(realpath ../../proto-devnet/tmp-devnet/alloy)" ./run.sh
    ```

3. Access Grafana at <http://localhost:3000>

The generated alloy config is customized for proto-devnet with correct node IPs and Prometheus ports.

### Debugging Alloy log collection

If logs aren't appearing in Grafana, check:

1. View the generated alloy config to see the LOG_PATH (should be absolute):
   ```shell
   cat tmp-devnet/alloy | grep -A2 "local.file_match"
   ```

2. Check Alloy's UI at http://localhost:12345 to see:
   - What files it's discovering
   - Any errors in log collection

3. Verify the log files exist and match the pattern:
   ```shell
   ls -la tmp-devnet/node*/node.log
   ```

## Clean up

To reset the demo, simply remove the working directory, for example:

``` shell
rm -rf tmp-devnet
```

## About the configuration

The `config/` directory contains pre-prepared configuration files for the 3-node devnet:

- Genesis files (shelley, alonzo, conway, dijkstra)
- Node configuration (`config.json`)
- Topology template (`topology.template.json`)
- Pool keys for 3 block-producing nodes (pool1, pool2, pool3)
- Stake delegators and UTxO keys

This serves as a starting configuration when intializing the testnet (see `init.sh`), which requires the typical modifications like file permissions, topology wiring and updating the start times.

The template configuration was originally created using `cardano-cli`:

``` shell
cardano-cli conway genesis create-testnet-data --out-dir config --testnet-magic 164 --pools 3 --total-supply 2000000000000 --delegated-supply 240000000002 --stake-delegators 3 --utxo-keys 3
```

Then tuned and removed unnecessary components (Byron-era and governance-related files).
