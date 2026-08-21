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

### With Docker

A pre-built relay image is published on every push to `main`:

```shell
docker run --rm -p 3010:3010 -v testnet-data:/data \
  ghcr.io/input-output-hk/ouroboros-leios/cardano-node-testnet:latest
```

The image bakes in the pinned `cardano-playground` snapshot and runs the
node directly (no process-compose / X-ray observability — that's
host-side; see `./run.sh` for the full setup). Built from
[`./Dockerfile`](./Dockerfile) on top of the generic
`cardano-node-leios` base — a minimal `dockerTools.streamLayeredImage`
holding statically-linked `cardano-node` + `cardano-cli` from the
`cardano-node-leios` flake input (see [`../nix/release.nix`](../nix/release.nix)).


### Without Nix

Install these prerequisites:

- `process-compose` for orchestrating the relay and observability stack.
- `cardano-node` patched with Leios support (the `leios-prototype`
  branch). Build instructions in the top-level repo.
- `cardano-cli` compatible with the cardano-node version.
- `jq` and `envsubst` for config inspection / templating.
- `curl` if you intend to refresh the pinned config snapshot.

When `XRAY=1` (the default), also install the X-ray stack dependencies:
`prometheus`, `loki`, `grafana`, `alloy`, `ss_http_exporter` — see
[`../demo/extras/x-ray`](../demo/extras/x-ray) for details.

Ensure they are on your PATH, or point at a specific binary:

```shell
CARDANO_NODE=/path/to/cardano-node ./run.sh
```

## What's included

`run.sh` orchestrates a `process-compose` session with:

1. The Leios relay (`Node`) — a single `cardano-node` in non-producing
   mode bound to `0.0.0.0:3010`, connected to the testnet relay
   (`leios-node.play.dev.cardano.org:3001`) per the pinned `topology.json`.
2. A tip watcher (`ObserveTip`) — `cardano-cli query tip` re-run on the
   node socket every 0.5s.
3. The X-ray observability stack (enabled by default, disable with
   `XRAY=0`): Alloy scrapes the node's Prometheus endpoint and tails
   logs into Loki; Grafana exposes them at <http://localhost:3000>.

The pinned configs (under `config/`) are staged into a working
directory (default `./tmp-testnet`). The node socket lands at
`${WORKING_DIR}/node.socket`, the Prometheus endpoint at
`127.0.0.1:12798`, and the combined log at `${WORKING_DIR}/node.log`.

For just the node — no process-compose, no observability — run
[`./run-node.sh`](./run-node.sh) directly.

## Configuration

Override defaults by setting environment variables before running. See
`run.sh` / `run-node.sh` for the full list and their defaults:

| Env var       | Default                       | Notes                                  |
|---------------|-------------------------------|----------------------------------------|
| `CARDANO_NODE`| `cardano-node`                | Path to the binary                     |
| `WORKING_DIR` | `./tmp-testnet`               | Where the node's DB / socket / log go  |
| `PORT`        | `3010`                        | Local listening port                   |
| `HOST_ADDR`   | `0.0.0.0`                     | Bind address                           |
| `METRICS_PORT`| `12798`                       | Prometheus scrape target               |
| `XRAY`        | `1`                           | Set `0` to skip the observability stack|
| `LOG_FILE`    | `${WORKING_DIR}/node.log`     | Combined log (consumed by `run-node.sh`)|

Example:

```shell
WORKING_DIR=my-relay PORT=3011 ./run.sh
```

## Observability with X-ray

The X-ray stack is on by default. Grafana is reachable at
<http://localhost:3000>. To run just the relay without it:

```shell
XRAY=0 ./run.sh
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

The `config/` directory holds a pinned snapshot of the `musashi`
network configuration served at
[`book.play.dev.cardano.org/environments-pre/leios`](https://book.play.dev.cardano.org/adv-musashi.html):

- Genesis files (byron, shelley, alonzo, conway, dijkstra).
- Node configuration (`config.json`) and topology (`topology.json` +
  `peer-snapshot.json`).

The topology points at a single bootstrap relay
(`leios-node.play.dev.cardano.org:3001`); the node will fan out from
there via ledger peers once it's synced enough to know about them
(`useLedgerAfterSlot` in `topology.json`).

To re-pin when the testnet rolls (or to try a staging URL):

```shell
./pin-config.sh                    # default: book.play.dev.cardano.org
./pin-config.sh https://other/env  # override base URL
```

The script overwrites the local `config/` snapshot with the files at
that base. Re-commit if you want others to pick up the change.

## Notes

- Network magic is **164** (shared with `demo/proto-devnet`).
- No KES / VRF / op-cert keys are provided — the node operates as a
  non-block-producing relay. Adding pool credentials would let it
  forge, but is out of scope here.
