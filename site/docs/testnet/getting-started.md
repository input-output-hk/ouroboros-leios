---
sidebar_position: 1
description: Install the Leios node, run a relay, and sync it against the public testnet.
---

# Install and run a node

:::info Musashi Dōjō
Welcome to the **Musashi Dōjō**, the testnet and training hall for Ouroboros Leios.

The journey starts by learning to **install** and **run** a Leios node —
and, for the adventurous, how to **register a pool**.

The **Earth phase** — the first of the dojo's five phases of intense
experimentation, learning, and development — begins in July. Now is the
time to get familiar with this implementation.

Bring your questions to the dojo floor: join the
**[Musashi Dōjō Discord](https://discord.gg/Bx2qvsjCte)** for advice and
guidance when you hit a snag, and to raise any issues, concerns, or bugs
you find.
:::

## Where to start

1. **Install and run a node** (this page) — get a relay syncing against
   the testnet.
2. [Register a stake pool](./register-stake-pool.md) — become a block
   producer.

:::warning This is a prototype
The Leios testnet runs pre-release code that is rebuilt and redeployed
continuously. Expect the chain to be reset, the configuration to be
re-pinned, and these instructions to change constantly. Run it on
a throwaway machine or container, not on anything you rely on. Nothing
here touches mainnet or real ada.
:::

## What to expect in the early days

The testnet opens as a training ground, not a finished product. Expect
rough edges, especially at the start — that is the point of practicing in
the open. 

A rough picture of the early days:

- **Run nodes.** The first goal is simply a healthy population of nodes
  following the chain — relays, and a growing number of block producers.
  Standing one up (this guide) is the most useful thing you can do on day
  one.
- **Load comes from IO — and from you.** Leios only does its job under
  transaction load: endorser blocks get produced and certified when there
  is enough traffic to warrant them. IO drives a baseline with
  **tx-centrifuge** (an evolution of the transaction generator we have run
  on benchmark clusters for years), injecting transactions so Leios
  activates under realistic conditions.
- **Dapps are welcome.** Connect to the testnet and drive your own load —
  including script execution — to see how your workload behaves under
  Leios. Heads-up: not all tooling is **Dijkstra-era** ready yet, so
  some things may be missing or rough. It may not be a smooth start; that
  is expected.
- **Tool builders are welcome too.** If you maintain explorers, indexers,
  wallets, or SDKs, this is a good time to begin integrating with the
  Dijkstra era and the Leios testnet — start whenever you see fit. Early
  feedback is exactly what this phase is for.

:::tip Watch the chain
**[KleioScan](https://kleioscan.com/#/leios)** — an early Leios testnet
explorer built by [Kostas Dermentzis](https://github.com/kderme) — lets you watch blocks, including
endorser blocks, as they land.
:::

## The network at a glance

|                     |                                                                                                          |
|---------------------|----------------------------------------------------------------------------------------------------------|
| **Network**         | Ouroboros Leios public prototype testnet                                                                 |
| **Bootstrap relay** | `leios-node.play.dev.cardano.org:3001`                                                                   |
| **Network magic**   | `164`                                                                                                    |
| **Faucet**          | [faucet.leios.play.dev.cardano.org](https://faucet.leios.play.dev.cardano.org/basic-faucet)              |
| **Node release**    | [`prototype-2026w25`](https://github.com/input-output-hk/ouroboros-leios/releases/tag/prototype-2026w25) |
| **Node version**    | reports `cardano-node 11.0.1.164`                                                                        |

## System requirements

The network is fresh and will be respun every couple of weeks. Thus, the load on
validating nodes is light by testnet standards — a small machine is plenty, but
requires a reasonably fast disk:

|               |                                                    |
|---------------|----------------------------------------------------|
| **OS / arch** | Linux **x86-64** (to use the prebuilt binaries)    |
| **CPU**       | 2 cores is fine; more only speeds the initial sync |
| **RAM**       | 4 GB comfortable (the node uses ~2–2.5 GB)         |
| **Disk**      | SSD, ~25 GB                                        |


:::info Requirements will change
Keep an eye out for these system requirements changing, especially the later
phases which will have more load and parameter exploration, which requires more
resources. In any case, we would like to [hear from your
experience](https://discord.gg/Bx2qvsjCte) running it on your individual
hardware or cloud provider.
:::

## Run a relay

You need a `cardano-node` (the Leios prototype) following the testnet as a
**relay**: a node that syncs the chain but does not produce blocks. Get
this stable before adding block-producer credentials in the
[next guide](./register-stake-pool.md).

A few ways to start one — pick whichever fits your setup:

- **Nix** — one command builds, installs, and runs the node together
  with a Grafana + Loki + Prometheus stack. Every dependency is
  provided.
- **Prebuilt binaries** — download the statically linked binaries and
  run them with the repository's launch script. Compatible with the
  same observability stack if you install the extra tooling, or run
  the node on its own and bring your own tools.
- **Docker** — the same binaries packaged as a container image, for
  setups that already orchestrate nodes that way. No observability
  stack included.

Then continue to [Confirm you are syncing](#confirm-you-are-syncing).

### Nix

[Nix](https://nixos.org/download/) installs the node and all of its
dependencies reproducibly.

**1. Install Nix with flake support.** Any recent installer will do —
the [official installer](https://nixos.org/download/) or
[Determinate Systems'](https://determinate.systems/posts/determinate-nix-installer/)
both enable flakes out of the box. The first time you run a flake-based
command Nix will ask whether to accept its substituter settings — say
yes so the IOG binary cache from our flake kicks in. To skip the prompt
once and for all, add this to your nix.conf:

```
accept-flake-config = true
```

**2. Run the relay.** A single command runs a fully provisioned relay —
the node, a live tip-watcher, and the observability stack — with no clone
required:

```shell
nix run github:input-output-hk/ouroboros-leios#leios-testnet-relay
```

With the cache in play this should be **a few minutes** of downloads,
not hours of compilation.

<details>
<summary>If it starts compiling `cardano-node` from source</summary>

The flake-config trust didn't apply — usually because your user isn't
in `trusted-users` on a multi-user install, so the daemon ignores the
flake's substituter settings and falls back to no cache. Add the cache
to your global config and restart the daemon:

```shell
echo "extra-substituters = https://cache.iog.io" | sudo tee -a /etc/nix/nix.conf
echo "extra-trusted-public-keys = hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ=" | sudo tee -a /etc/nix/nix.conf
sudo systemctl restart nix-daemon
```

The [IOG Nix setup guide](https://github.com/input-output-hk/iogx/blob/main/doc/nix-setup-guide.md)
covers the full configuration.

</details>

The node binds to `0.0.0.0:3010` and keeps its database, socket, and
log under `./tmp-testnet`. A Grafana dashboard opens at
`http://localhost:3000` — see
[Out-of-the-box observability](#out-of-the-box-observability) for what
it gives you. Head to [Confirm you are syncing](#confirm-you-are-syncing).

:::tip Want the CLI on your PATH?
To use `cardano-node` and `cardano-cli` directly (for example, to register a
pool later), you may want to use this nix dev shell:

```shell
nix develop github:input-output-hk/ouroboros-leios#dev-testnet
cardano-node --version   # expect: cardano-node x.y.z.164
```
:::

## Option 2 — Without Nix: prebuilt binaries

The release ships statically linked binaries for **Linux x86-64** — they
carry all their dependencies inside, so there is nothing else to install
to run them.

**1. Install the tools to download and verify them.**

```shell
sudo apt update
sudo apt install -y curl jq git
```

`curl` downloads files, `jq` reads the JSON output used throughout these
guides, and `git` fetches the testnet configuration below.

**2. Download the node, the CLI, and the checksums.**

```shell
mkdir -p ~/leios && cd ~/leios

BASE=https://github.com/input-output-hk/ouroboros-leios/releases/download/prototype-2026w25
curl -L -O "$BASE/cardano-node"
curl -L -O "$BASE/cardano-cli"
curl -L -O "$BASE/SHA256SUMS"
```

**3. Verify the download.** Confirm the files arrived intact before you
run them:

```shell
sha256sum -c SHA256SUMS
```

You should see `cardano-node: OK` and `cardano-cli: OK`. If you see
`FAILED`, delete the files and download them again.

**4. Install them onto your `PATH`.**

```shell
chmod +x cardano-node cardano-cli
sudo install -m 755 cardano-node cardano-cli /usr/local/bin/
```

Confirm `cardano-node --version` reports
`cardano-node 11.0.1.164 - linux-x86_64 - ghc-9.6`. The `.164` marks the
Leios prototype build.

**5. Get the testnet configuration.** Clone the repository for the pinned
config and the launch script:

```shell
cd ~/leios
git clone https://github.com/input-output-hk/ouroboros-leios
cd ouroboros-leios/testnet
```

The `testnet/config/` folder holds everything the node needs to find and
trust the network: the genesis files, the node configuration
(`config.json`), and the topology (`topology.json`) that points at the
public bootstrap relays.

**6. Start the relay.** `run-node.sh` launches a single `cardano-node` as
a non-producing relay, bound to `0.0.0.0:3010`. Give it a working
directory for its database, socket, and log:

```shell
WORKING_DIR=~/leios/relay ./run-node.sh
```

Within a few seconds you will see the node connect to peers and begin
adding blocks (`AddedToCurrentChain`). The socket lands at
`~/leios/relay/node.socket` and the log at `~/leios/relay/node.log`.

:::tip Keep it running in the background
This runs in the foreground and streams log lines. To leave it running
while you work in the same terminal, start it under a terminal
multiplexer such as `tmux` (`sudo apt install -y tmux`, then `tmux`, then
run the command). Detach with `Ctrl-b d`.
:::

:::note Want the dashboards too?
The Grafana + Loki + Prometheus stack is exactly what **Option 1**
provides out of the box. You can also get it on this path by running
`./run.sh` instead of `./run-node.sh`, but it needs extra tools on your
`PATH` (`process-compose`, `envsubst`, and the observability stack) — the
Nix dev shell from Option 1 supplies them all. A prebuilt **Docker**
image carrying both binaries is also published:
`ghcr.io/input-output-hk/ouroboros-leios/cardano-node-testnet:latest`.
:::

## Confirm you are syncing

If you used **Option 1**, the relay's process dashboard already shows live
sync in its tip-watcher pane — you can watch it there. To query the node
yourself (or if you used **Option 2**), open a **second terminal** with
`cardano-cli` available, point it at the node's socket, and ask for the
chain tip:

```shell
export CARDANO_NODE_NETWORK_ID=164
# Option 2: the WORKING_DIR you chose (e.g. ~/leios/relay/node.socket).
# Option 1: ./tmp-testnet/node.socket (from the nix develop shell).
export CARDANO_NODE_SOCKET_PATH=~/leios/relay/node.socket
cardano-cli query tip
```

You will see something like:

```json
{
    "block": 48521,
    "epoch": 11,
    "era": "Dijkstra",
    "slot": 969905,
    "syncProgress": "46.36"
}
```

Run it again every minute — `block`, `slot`, and `syncProgress` should
climb. When `syncProgress` reads `100.00`, your node is fully caught up
and following the testnet.

:::warning Syncing happens in bursts, not a smooth climb. Don't restart.
As your node catches up through the transaction-heavy part of the chain,
it fetches large endorser blocks and their full transaction closures from
a handful of peers. This makes sync **lurch**: `syncProgress` and the
block height sit still for thirty seconds to a couple of minutes, then
jump forward in a burst. If you run `query tip` during a pause it looks
frozen even though the node is healthy and working.

**Resist the urge to restart** during a pause — a restart throws away
catch-up progress. Leave the node running and let it ride. To tell a
genuine hang from a pause, watch over a few minutes: if the block height
eventually jumps, it is working.
:::

## Watch Leios at work (optional)

The pinned configuration turns on debug tracing for the Leios
subsystems, so you can watch endorser blocks move through your node. Tail
the log and filter for the Leios events (Option 2 path shown; on Option 1
the log is at `./tmp-testnet/node.log`, or use the Loki/Grafana view):

```shell
tail -f ~/leios/relay/node.log | grep -E 'Leios|CertRB'
```

Greppable highlights:

- `"kind":"LeiosBlockForged"` / `"kind":"LeiosBlockCertified"` — an
  endorser block being produced and certified (emitted by block
  producers; at a relay you see the offers arrive).
- `"kind":"LeiosBlockAcquired"` / `"kind":"LeiosBlockTxsAcquired"` — an
  endorser-block body or its transaction closure arriving from a peer.
- `"kind":"CertRBStaged"` / `"kind":"CertRBReleased"` — a ranking block
  held back until its endorser-block closure is local, then released
  once it arrives.

Seeing these flow through a relay you stood up yourself is the protocol
behaving in public exactly as the design intends.

---

**Next:** [Register a stake pool →](./register-stake-pool.md)
