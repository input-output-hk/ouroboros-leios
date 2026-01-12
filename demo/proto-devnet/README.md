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

We require a prepared devnet setup in `devnet/` so starting it is:

``` shell
cardano-testnet cardano --node-env devnet --update-time
```

## Restart and cleanup

Once `cardano-testnet` is stopped, restarting is not robustly possible because of dynamically allocated ports by `cardano-testnet`.

Cleanup to start over can be done by:

``` shell
git clean -dxf devnet/
git restore devnet/
```

## Prepare devnet

This command was used to prepare the `--node-env`:

``` shell
cardano-testnet create-env --output devnet --num-pool-nodes 3 --slot-length 1 --testnet-magic 164 --params-mainnet
```

We checked this in because the `cardano-node` we are using is older than `cardano-testnet` and the topology files it generates need patching:

```json title="Generated topology.json"
{
    "bootstrapPeers": null,
    "localRoots": [
        {
            "accessPoints": [
                "node_2",
                "node_3"
            ],
            "advertise": false,
            "diffusionMode": "InitiatorAndResponder",
            "hotValency": 2,
            "trustable": true,
            "warmValency": 2
        }
    ],
    "peerSnapshotFile": null,
    "publicRoots": [
        {
            "accessPoints": [],
            "advertise": false
        }
    ],
    "useLedgerAfterSlot": -1
}
```
