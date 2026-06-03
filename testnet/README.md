# Leios testnet relay

A minimal setup for joining the public Leios prototype testnet
(`leios-node.play.dev.cardano.org`) as a non-block-producing relay.

Useful for any work that needs a real-world Leios node:

- Smoke-testing a locally built `cardano-node` against live traffic
  (chain catchup, EB announcement and fetch behaviour, ChainSync /
  BlockFetch / LeiosNotify / LeiosFetch interactions, etc.).
- Reproducing reports from the testnet — feeding a `db-analyser`
  snapshot, replaying logs.
- Running `cardano-cli query` and other tooling against a node that
  follows the real testnet chain.

## Getting started

Run the relay with all dependencies automatically provided using nix:

```shell
nix run github:input-output-hk/ouroboros-leios#leios-testnet-relay
```

Or enter the `nix develop` shell (also available via `direnv allow`)
and follow [without nix instructions](#without-nix).

### Without Nix

Install these prerequisites:

- `cardano-node` patched with Leios support (the `leios-prototype`
  branch). Build instructions in the top-level repo.
- `cardano-cli` compatible with the cardano-node version.
- `jq` for the run script's config inspection.
- `curl` if you intend to refresh the pinned config snapshot.

Ensure they are on your PATH, or point at a specific binary:

```shell
CARDANO_NODE=/path/to/cardano-node ./run.sh
```

## What's included

`run.sh` will:

1. Stage the pinned configs (under `config/`) into a working directory
   (default `./tmp-testnet`).
2. Launch a single `cardano-node` in non-producing mode bound to
   `0.0.0.0:3010`, connected to the testnet relay
   (`leios-node.play.dev.cardano.org:3001`) per the pinned `topology.json`.
3. Surface the node socket at `${WORKING_DIR}/node.socket` and a
   prometheus endpoint at `127.0.0.1:12798`.

While it's running, observe progress:

```shell
export CARDANO_NODE_NETWORK_ID=164
export CARDANO_NODE_SOCKET_PATH=tmp-testnet/node.socket
watch -n1 "cardano-cli query tip"
```

## Configuration

Override defaults by setting environment variables before running. See
`run.sh` for the full list and their defaults:

| Env var       | Default                       | Notes                                  |
|---------------|-------------------------------|----------------------------------------|
| `CARDANO_NODE`| `cardano-node`                | Path to the binary                     |
| `WORKING_DIR` | `./tmp-testnet`               | Where the node's DB / socket go        |
| `PORT`        | `3010`                        | Local listening port                   |
| `HOST_ADDR`   | `0.0.0.0`                     | Bind address                           |
| `LOG_FILE`    | `${WORKING_DIR}/node.log`     | Where `tee` writes the combined log    |

Example:

```shell
WORKING_DIR=my-relay PORT=3011 ./run.sh
```

## Trace events to watch

The pinned `config.json` sets `Consensus.LeiosKernel`,
`Consensus.LeiosPeer`, `LeiosFetch.Remote`, and `LeiosNotify.Remote`
to `Debug` with no rate limit. Greppable highlights:

- `"kind":"LeiosBlockForged"` / `"kind":"LeiosBlockCertified"` — EB
  production and certification (only emitted by block producers, but
  visible as `MsgLeiosBlockOffer` receives here).
- `"kind":"LeiosBlockAcquired"` / `"kind":"LeiosBlockTxsAcquired"` —
  EB body / tx-closure arrived from a peer.
- `"kind":"CertRBStaged"` / `"kind":"CertRBReleased"` — the CertRB
  staging area (issue #890) parking a block whose EB closure isn't
  local yet, and releasing it once the closure arrives.

## Clean up

To reset, remove the working directory:

```shell
rm -rf tmp-testnet
```

## About the configuration

The `config/` directory holds a pinned snapshot of
[`cardano-playground/static/book.play.dev.cardano.org/environments-pre/leios`](https://github.com/input-output-hk/cardano-playground/tree/next-2026-05-15/static/book.play.dev.cardano.org/environments-pre/leios)
at branch `next-2026-05-15`:

- Genesis files (byron, shelley, alonzo, conway, dijkstra).
- Node configuration (`config.json`) and topology (`topology.json` +
  `peer-snapshot.json`).

The topology points at a single bootstrap relay
(`leios-node.play.dev.cardano.org:3001`); the node will fan out from
there via ledger peers once it's synced enough to know about them
(`useLedgerAfterSlot` in `topology.json`).

To re-pin when the testnet rolls (or to try a different branch):

```shell
./pin-config.sh                    # default: next-2026-05-15
./pin-config.sh some/other-branch  # specific ref
```

The script fetches every required file from the raw GitHub URL and
overwrites the local `config/` snapshot. Re-commit if you want others
to pick up the change.

## Notes

- Network magic is **164** (shared with `demo/proto-devnet`).
- No KES / VRF / op-cert keys are provided — the node operates as a
  non-block-producing relay. Adding pool credentials would let it
  forge, but is out of scope here.
