---
sidebar_position: 2
title: Register a stake pool
description: Register a Leios stake pool (block producer) on the public testnet, magic 164.
---

import Tabs from '@theme/Tabs';
import TabItem from '@theme/TabItem';

# Register a stake pool

This is the second of two guides. It assumes you have already
[installed and synced a relay](./getting-started.md).

This is the adventurous path. Running a relay confirms your node can
follow the chain; registering a **stake pool** lets it forge blocks —
both ordinary Praos ranking blocks and Leios endorser blocks — and makes
you a full participant in the Earth-phase work.

:::info About BLS keys — what changes soon
For the first few days of the testnet, registering a stake pool uses
**exactly the same method you use on Cardano today** — the keys and
certificates below. In the coming days the engineering team will release
a node version that requires stake pools to additionally register a new
**BLS key**. BLS keys are an essential part of Leios: they are what pools
use to vote on and certify endorser blocks. When that release lands, this
guide will add the extra registration step. Until then, the standard flow
on this page is all you need.
:::

:::note First, get `cardano-cli` and `cardano-node` on your PATH
Every command in this guide uses `cardano-cli`, and the final step runs
`cardano-node` directly — so you need both available.

- **Installed with Nix?** Drop into the `dev-testnet` shell, which puts
  the tools on your `PATH`:
  ```shell
  nix develop github:input-output-hk/ouroboros-leios#dev-testnet
  ```
- **Installed the prebuilt binaries?** They are already on your `PATH` —
  nothing extra to do.
:::

## What you need first

- **Test ada** from the
  [faucet](https://faucet.leios.play.dev.cardano.org/basic-faucet). It
  sends a fixed amount automatically (10,000 test ada) — far more
  than enough to cover the **stake-pool deposit (500 ada)**, the
  **stake-address deposit (2 ada)**, your **pledge**, and transaction
  fees.
- A **public IP address and an open port** so other nodes can reach your
  node.
- An **accurate clock** — a block producer must keep precise time.
  Install and enable NTP:
  ```shell
  sudo apt install -y chrony
  sudo systemctl enable --now chrony
  ```

Keep the environment from the previous guide set in your shell —
`$WORKING_DIR` points at the relay's working directory, and with
`CARDANO_NODE_NETWORK_ID` exported every `cardano-cli` command targets
magic `164` automatically (no `--testnet-magic` flag needed):

```shell
export WORKING_DIR=~/leios-testnet         # or wherever you put the relay
export CARDANO_NODE_NETWORK_ID=164
export CARDANO_NODE_SOCKET_PATH="$WORKING_DIR/node.socket"
```

Work in a dedicated keys folder under `$WORKING_DIR` and **back it up** —
these keys control your pool:

```shell
mkdir -p "$WORKING_DIR/keys" && cd "$WORKING_DIR/keys"
```

:::note Era command group
The commands below use the `dijkstra` era command group
(`cardano-cli dijkstra ...`), because the testnet is currently in the
**Dijkstra** era at the chain tip. Confirm with the `era` field of
`cardano-cli query tip`; if it ever reads something else, switch the era
word in these commands to match.
:::

## Payment and stake keys

```shell
# Payment key pair (holds funds)
cardano-cli dijkstra address key-gen \
  --verification-key-file payment.vkey \
  --signing-key-file payment.skey

# Stake key pair (controls delegation)
cardano-cli dijkstra stake-address key-gen \
  --verification-key-file stake.vkey \
  --signing-key-file stake.skey
```

## Fund a payment address

```shell
cardano-cli dijkstra address build \
  --payment-verification-key-file payment.vkey \
  --stake-verification-key-file stake.vkey \
  --out-file payment.addr

cat payment.addr
```

Copy that address into the
[faucet](https://faucet.leios.play.dev.cardano.org/basic-faucet) to
receive test ada. Confirm it arrived:

```shell
cardano-cli dijkstra query utxo --address "$(cat payment.addr)"
```

You should see one or more UTxO entries (a `TxHash#TxIx` and an amount).

## Node operational keys

```shell
# Cold keys (your pool's identity — keep offline / backed up)
cardano-cli dijkstra node key-gen \
  --cold-verification-key-file cold.vkey \
  --cold-signing-key-file cold.skey \
  --operational-certificate-issue-counter-file opcert.counter

# KES keys (hot keys, rotated periodically)
cardano-cli dijkstra node key-gen-KES \
  --verification-key-file kes.vkey \
  --signing-key-file kes.skey

# VRF keys (used to win block-production slots)
cardano-cli dijkstra node key-gen-VRF \
  --verification-key-file vrf.vkey \
  --signing-key-file vrf.skey
```

## Operational certificate

Compute the current KES period from the chain tip and the genesis
parameter, then issue the certificate that binds your KES key to your
cold key:

```shell
slotsPerKESPeriod=$(jq -r '.slotsPerKESPeriod' "$WORKING_DIR/config/shelley-genesis.json")
slotNo=$(cardano-cli query tip | jq -r '.slot')
kesPeriod=$(( slotNo / slotsPerKESPeriod ))

cardano-cli dijkstra node issue-op-cert \
  --kes-verification-key-file kes.vkey \
  --cold-signing-key-file cold.skey \
  --operational-certificate-issue-counter-file opcert.counter \
  --kes-period "$kesPeriod" \
  --out-file opcert.cert
```

## Register stake address and pool

Two things go on-chain together: your **stake address** (a 2 ada deposit)
and your **pool** (a 500 ada deposit). Build both certificates, then
submit them in a single transaction.

Stake-address registration certificate:

```shell
cardano-cli dijkstra stake-address registration-certificate \
  --stake-verification-key-file stake.vkey \
  --key-reg-deposit-amt "$(cardano-cli dijkstra query gov-state | jq .currentPParams.stakeAddressDeposit)" \
  --out-file stake-reg.cert
```

Pool registration certificate — replace `<YOUR_PUBLIC_IP>` with your node's
public IP (the address other nodes will use to reach it):

```shell
cardano-cli dijkstra stake-pool registration-certificate \
  --cold-verification-key-file cold.vkey \
  --vrf-verification-key-file vrf.vkey \
  --pool-pledge 1000000000 \
  --pool-cost 170000000 \
  --pool-margin 0.05 \
  --pool-reward-account-verification-key-file stake.vkey \
  --pool-owner-stake-verification-key-file stake.vkey \
  --pool-relay-ipv4 <YOUR_PUBLIC_IP> \
  --pool-relay-port 3010 \
  --out-file pool-reg.cert
```

:::tip
`--pool-pledge 1000000000` is 1000 test ada — a reasonable pledge for a testnet
pool. `--pool-cost 170000000` (170 ada) and `--pool-margin 0.05` (5%) are
typical values; adjust to taste. `--pool-relay-port` must match the port
your node listens on (`3010` by default in this guide).
:::

Submit both certificates in one transaction. `transaction build` queries
the node for protocol parameters and your UTxOs to balance the fee and
return the change automatically — you just pick an input and a change
address. Pull your funded input straight from `query utxo` (this assumes
a single UTxO at the address — true right after the faucet payment),
then sign with three keys (payment, stake, cold) and submit:

```shell
TXIN=$(cardano-cli dijkstra query utxo --address "$(cat payment.addr)" | jq -r 'keys[0]')

cardano-cli dijkstra transaction build \
  --tx-in "$TXIN" \
  --change-address "$(cat payment.addr)" \
  --certificate-file stake-reg.cert \
  --certificate-file pool-reg.cert \
  --out-file pool-reg-tx.raw

cardano-cli dijkstra transaction sign \
  --tx-body-file pool-reg-tx.raw \
  --signing-key-file payment.skey \
  --signing-key-file stake.skey \
  --signing-key-file cold.skey \
  --out-file pool-reg-tx.signed

cardano-cli dijkstra transaction submit \
  --tx-file pool-reg-tx.signed
```

## Delegate stake to your pool

Your pledge only counts once your own stake is delegated to your pool.
Build a delegation certificate and submit it in its own transaction.
Your UTxO set changed in the previous step, so the snippet re-queries it
for the current input. Two signatures here — payment and stake:

```shell
cardano-cli dijkstra stake-address stake-delegation-certificate \
  --stake-verification-key-file stake.vkey \
  --cold-verification-key-file cold.vkey \
  --out-file delegation.cert

TXIN=$(cardano-cli dijkstra query utxo --address "$(cat payment.addr)" | jq -r 'keys[0]')

cardano-cli dijkstra transaction build \
  --tx-in "$TXIN" \
  --change-address "$(cat payment.addr)" \
  --certificate-file delegation.cert \
  --out-file delegation-tx.raw

cardano-cli dijkstra transaction sign \
  --tx-body-file delegation-tx.raw \
  --signing-key-file payment.skey \
  --signing-key-file stake.skey \
  --out-file delegation-tx.signed

cardano-cli dijkstra transaction submit \
  --tx-file delegation-tx.signed
```

:::tip Get real stake from the faucet
Your pledge alone (1000 test ada) is far too little for the pool to be
selected to forge. The
[faucet](https://faucet.leios.play.dev.cardano.org/basic-faucet) can also
**delegate ~1,000,000 test ada** to your pool, giving it meaningful active
stake. The faucet's **delegate** widget needs your **bech32 pool id**
(`pool1…`) — get it with:

```shell
cardano-cli dijkstra stake-pool id --output-bech32 --cold-verification-key-file cold.vkey
```
:::

## Verify registration

Capture your **pool id** (from the cold key) and your **stake address**:

```shell
POOL_ID=$(cardano-cli dijkstra stake-pool id --cold-verification-key-file cold.vkey --output-format hex)
STAKE_ADDR=$(cardano-cli dijkstra stake-address build --stake-verification-key-file stake.vkey)
echo "pool id: $POOL_ID"
echo "stake address: $STAKE_ADDR"
```

Check the pool is registered on-chain — this should print your pool's
parameters (pledge, cost, margin, VRF):

```shell
cardano-cli dijkstra query pool-state --stake-pool-id "$POOL_ID"
```

Check the delegation took effect — `stakeDelegation` should point at
your pool id:

```shell
cardano-cli dijkstra query stake-address-info --address "$STAKE_ADDR"
```

If both look right, your pool is registered.

## Restart as block producer

Stop the relay and restart it with the KES key, VRF key, and operational
certificate so it can forge — extending the `cardano-node run`
invocation from the previous guide (or, on the Nix path, replacing
`nix run …#leios-testnet-relay` since that wrapper only runs a
non-producing relay).

:::tip Keep it up
By now you should have settled on a way to keep the node running in the
background and watch its uptime — `tmux`/`screen`, a `systemd` unit, or
the Docker invocation below. A block producer that drifts offline
silently mints no blocks and earns no rewards, so make sure something is
watching it.
:::

Run it from `$WORKING_DIR`, which holds the config and database:

<Tabs groupId="runtime">
<TabItem value="binary" label="cardano-node" default>

```shell
cd "$WORKING_DIR"
cardano-node run \
  --config config/config.json \
  --topology config/topology.json \
  --database-path db \
  --socket-path node.socket \
  --host-addr 0.0.0.0 \
  --port 3010 \
  --shelley-kes-key keys/kes.skey \
  --shelley-vrf-key keys/vrf.skey \
  --shelley-operational-certificate keys/opcert.cert
```

</TabItem>
<TabItem value="docker" label="Docker">

Stop the relay container from the previous guide and start a producer
that mounts the same `$WORKING_DIR` — reusing the synced database and
the pinned config under `config/` — plus the keys underneath it:

```shell
docker rm -f leios-relay

docker run -d --name leios-producer \
  -p 3010:3010 \
  -v "$WORKING_DIR:/data" \
  -w /data \
  ghcr.io/input-output-hk/ouroboros-leios/cardano-node-testnet:prototype-2026w27 \
  cardano-node run \
    --config config/config.json \
    --topology config/topology.json \
    --database-path db \
    --socket-path node.socket \
    --host-addr 0.0.0.0 \
    --port 3010 \
    --shelley-kes-key keys/kes.skey \
    --shelley-vrf-key keys/vrf.skey \
    --shelley-operational-certificate keys/opcert.cert
```

Follow it with `docker logs -f leios-producer`.

</TabItem>
</Tabs>

Once your pool is registered and your node is forging, you are a block
producer on the testnet. Block production begins after the stake snapshot
takes effect — roughly two epochs after registration.

## What to send back

The testnet is where the protocol practices in public, and what you see
is part of the practice. If your node will not sync, a command here
fails, a trace event looks wrong, or the chain behaves in a way you did
not expect — that is exactly the signal the team wants.

When you report, include three things: the command or action you took,
what you expected, and what actually happened. Attach your node version
(`cardano-node --version`) and the relevant log lines.

- **Discord:** the [Musashi Dōjō Discord](https://discord.gg/Bx2qvsjCte) —
  advice, guidance, and the place to raise issues, concerns, or bugs.
- **Issues:** [Ouroboros Leios repository](https://github.com/input-output-hk/ouroboros-leios/issues)
- **Design reference:** [CIP-0164](https://github.com/cardano-foundation/CIPs/blob/master/CIP-0164/README.md)
