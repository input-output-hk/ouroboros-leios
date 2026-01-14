# Demo: Proto-Devnet

A small network of patched cardano nodes that is loaded with synthetically created transactions. The same observability as with [the November demo](../2025-11) is available.

![Demo diagram](./demo-proto-devnet.excalidraw.svg)

> [!TIP]
> This is an excalidraw SVG with embedded scene so it can be loaded and edited in [https://excalidraw.com/].

## Getting started

``` shell
nix run github:input-output-hk/ouroboros-leios#demo-proto-devnet
```

Or install these prerequisites:

- `cardano-testnet` and `tx-generator` (recent)
- Path to patched `cardano-node` set on `CARDANO_NODE`
- A compatible `cardano-cli` set on `CARDANO_CLI`
- `jq`

and run:

``` shell
./start.bash
```

The `nix develop` shell, also available via `direnv allow`, provides all these.

Then, we can launch the transaction workload using `tx-generator`:

``` shell
tx-generator -- json_highlevel gen.json
```

Observe tip advancing and mempool size:

``` shell
export CARDANO_NODE_NETWORK_ID=164
export CARDANO_NODE_SOCKET_PATH=devnet/socket/node1/sock
watch -n1 "cardano-cli query tip && cardano-cli query tx-mempool info"
```
