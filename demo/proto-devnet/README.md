# Demo: Proto-Devnet

A small network of patched cardano nodes that is loaded with synthetically created transactions. The same observability as with [the November demo](../2025-11) is available.

![Demo diagram](./demo-proto-devnet.excalidraw.svg)

> [!TIP]
> This is an excalidraw SVG with embedded scene so it can be loaded and edited in [https://excalidraw.com/].

## Prerequisites

- `cardano-testnet` (recent)
- Path to patched `cardano-node` set on `CARDANO_NODE`
- A compatible `cardano-cli` set on `CARDANO_CLI`

The `nix develop` shell, also available via `direnv allow`, provides all these.

## Start the devnet

``` shell
cardano-testnet cardano --testnet-magic 164 --output-dir devnet
```


