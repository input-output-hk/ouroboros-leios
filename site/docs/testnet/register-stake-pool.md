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

## BLS keys

BLS keys are keys that pools use to vote on and certify endorser blocks.
You need them to register a Leios-enabled stake pool — in Dijkstra the BLS
key is **structural**, not optional: `stake-pool registration-certificate`
refuses to build a certificate without one.

```shell
# BLS key pair (Leios voting/certification key)
cardano-cli dijkstra node key-gen-BLS \
  --verification-key-file bls.vkey \
  --signing-key-file bls.skey
```

The scheme is BLS12-381 in its *minimal signature size* variant, so the
verification key is 96 bytes (in G2) and a signature is 48 bytes (in G1).
You can see that in the key file's envelope type:

```shell
jq -r .type bls.vkey
# BlsVerificationKey_bls12-381-BLS-Signature-Mininimal-Signature-Size
```

:::note You never pass the proof of possession yourself
Registration needs a *proof of possession* — a signature over your own
public key that stops someone registering a key they do not hold (a rogue
key attack, which matters because Leios aggregates signatures). The CLI
derives it for you from the **signing** key, which is why the registration
step below takes `--bls-signing-key-file` and not the verification key.
`issue-pop-BLS` exists if you ever need the proof on its own.
:::

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
:::tip Joining the Rewards Program?
The [Rewards Program](./rewards-program.md) rewards stake pool
operators for running a pool on MusashiNet and sharing operational data.
Proving you control the pool requires an **Application Code** in the
metadata of *this* transaction, so read that page and apply before you
submit, and you avoid sending a second registration certificate later.
Applying needs only your pool id, which you already have:

```shell
cardano-cli dijkstra stake-pool id --output-bech32 --cold-verification-key-file cold.vkey
```
:::

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
  --bls-signing-key-file bls.skey \
  --pool-pledge 1000000000 \
  --pool-cost 170000000 \
  --pool-margin 0.05 \
  --pool-reward-account-verification-key-file stake.vkey \
  --pool-owner-stake-verification-key-file stake.vkey \
  --pool-relay-ipv4 <YOUR_PUBLIC_IP> \
  --pool-relay-port 3010 \
  --out-file pool-reg.cert
```

:::info What the BLS key does once it is on-chain
The registration certificate carries your BLS verification key and its
proof of possession (96 + 48 bytes on top of an ordinary registration).
The ledger stores the key together with **the epoch you registered it in**,
and that pair is what the Leios committee is drawn from — see
[Verify your BLS key](#verify-your-bls-key) and
[Rotate your BLS key](#rotate-your-bls-key) below.

Reach out on the [Musashi Dōjō Discord](https://discord.gg/AyUXD9VHn) if
you need help to register a pool.
:::

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

## Verify your BLS key

`query pool-state` reports a pool as ledger **state**, so alongside pledge,
cost and margin you get your BLS key and the epoch it was registered in:

```shell
cardano-cli dijkstra query pool-state --stake-pool-id "$POOL_ID" \
  | jq '.[].poolParams.spsBlsKey'
```

```json
{
  "bksKey": {
    "blsPubKey": "99786f625a1c9973d15990047f23120c0c1f9fa801b31ce24144...",
    "blsPossessionProof": "98f08ec21b63e8f7cbf042dd4df9c1527f1d14cc973c..."
  },
  "bksRegisteredIn": 0
}
```

Two things to check:

- `blsPubKey` matches the key you registered. Compare it against your own
  file — `bls.vkey` stores the key CBOR-wrapped, so strip the 4-character
  `5860` header before comparing:

  ```shell
  jq -r .cborHex bls.vkey | cut -c5-
  ```

- `bksRegisteredIn` is the epoch the ledger stamped your key with. This is
  **not** decoration: it is what key expiry is measured from, so note it.

A `null` here means the pool is registered but has **no** BLS key — it can
win blocks but can never vote on endorser blocks.

## See your pool on the Leios committee

The committee is not a separate registry; it is derived from the stake
snapshot at each epoch boundary. The rule (`selectLeiosCommittee`) is:

1. take the pools in the snapshot, ordered by stake, descending
2. keep the top `leiosCommitteeSize` of them — each gets seats weighted by
   its stake
3. offer a seat *its key* only while the key is still honoured, i.e. while
   `currentEpoch < bksRegisteredIn + maxKeyAge`

Step 3 is the one to remember: an aged-out key does not lose you the seat,
it leaves you **seated but keyless** — holding committee weight you cannot
vote with. That is worse than not being seated, because the seat is not
reallocated to someone who could have used it.

`query stake-snapshot` reports the committee itself, so none of this has
to be reconstructed by hand:

```shell
cardano-cli dijkstra query stake-snapshot --all-stake-pools \
  | jq '.leiosCommittee'
```

```json
[
  {
    "poolId": "e0a714319812c3f773ba04ec5d6b3ffcd5aad85006805b047b082541",
    "weight": { "numerator": 2, "denominator": 3 },
    "key": { "bksKey": { "blsPubKey": "a5756554…", "blsPossessionProof": "8114c1b1…" },
             "bksRegisteredIn": 191 },
    "voting": true
  }
]
```

Seats appear in committee order, and a seat's position in the list is the
index votes reference. Find yours by `poolId`:

```shell
cardano-cli dijkstra query stake-snapshot --all-stake-pools \
  | jq --arg pool "$POOL_ID" '.leiosCommittee[] | select(.poolId == $pool)'
```

Read `key` and `voting` together — that pair is the whole point:

| `key` | `voting` | meaning |
| --- | --- | --- |
| present | `true` | seated and voting |
| present | `false` | **seated but keyless** — your key aged out |
| `null` | `false` | seated, but you never registered a key |

No output at all means your pool did not make the top
`leiosCommitteeSize` by stake this epoch.

:::note Which snapshot this is
`leiosCommittee` is the committee seated on the `set` snapshot — the one
governing the *current* epoch, which is what the network is voting with
right now. The per-pool `stakeMark` figures in the same output are the
snapshot taken at the start of this epoch, so they tell you where you will
rank when the committee is next reseated.
:::

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
  --shelley-bls-key keys/bls.skey \
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
  ghcr.io/input-output-hk/ouroboros-leios/cardano-node-testnet:prototype-2026w30 \
  cardano-node run \
    --config config/config.json \
    --topology config/topology.json \
    --database-path db \
    --socket-path node.socket \
    --host-addr 0.0.0.0 \
    --port 3010 \
    --shelley-kes-key keys/kes.skey \
    --shelley-vrf-key keys/vrf.skey \
    --shelley-bls-key keys/bls.skey \
    --shelley-operational-certificate keys/opcert.cert
```

Follow it with `docker logs -f leios-producer`.

</TabItem>
</Tabs>

Once your pool is registered and your node is forging, you are a block
producer on the testnet. Block production begins after the stake snapshot
takes effect — roughly two epochs after registration.

**Getting rewarded for it.** The
[Rewards Program](./rewards-program.md) pays up to 100
pools for staying reachable, sharing telemetry and producing blocks. If
you did not apply before registering, you can still join by submitting an
updated registration certificate carrying your Application Code.

## Rotate your BLS key

BLS keys age out. The ledger honours a key only while

```
currentEpoch < bksRegisteredIn + maxKeyAge
```

so a key you registered and never touched again eventually stops counting,
and — as described above — your pool stays **seated but keyless**: it holds
committee weight it cannot vote with. Nothing warns you; `bksRegisteredIn`
simply stops being recent enough.

Rotating is the same operation as registering: submit a fresh pool
registration certificate carrying the new key. The ledger treats a
registration for a pool that already exists as an **update**, and re-stamps
`bksRegisteredIn` with the epoch the update takes effect in, which restarts
the clock.

```shell
# 1. new key pair, kept beside the old one until the rotation is on-chain
cardano-cli dijkstra node key-gen-BLS \
  --verification-key-file bls-new.vkey \
  --signing-key-file bls-new.skey

# 2. re-register: every other field stays exactly as it was
cardano-cli dijkstra stake-pool registration-certificate \
  --cold-verification-key-file cold.vkey \
  --vrf-verification-key-file vrf.vkey \
  --bls-signing-key-file bls-new.skey \
  --pool-pledge 1000000000 \
  --pool-cost 170000000 \
  --pool-margin 0.05 \
  --pool-reward-account-verification-key-file stake.vkey \
  --pool-owner-stake-verification-key-file stake.vkey \
  --pool-relay-ipv4 <YOUR_PUBLIC_IP> \
  --pool-relay-port 3010 \
  --out-file pool-rotate.cert

# 3. submit it on its own (no stake-address certificate this time)
TXIN=$(cardano-cli dijkstra query utxo --address "$(cat payment.addr)" | jq -r 'keys[0]')

cardano-cli dijkstra transaction build \
  --tx-in "$TXIN" \
  --change-address "$(cat payment.addr)" \
  --certificate-file pool-rotate.cert \
  --out-file pool-rotate.raw

cardano-cli dijkstra transaction sign \
  --tx-body-file pool-rotate.raw \
  --signing-key-file payment.skey \
  --signing-key-file cold.skey \
  --out-file pool-rotate.signed

cardano-cli dijkstra transaction submit --tx-file pool-rotate.signed
```

:::warning Do not swap the node's key until the rotation is seated
The node signs votes with whatever `--shelley-bls-key` it was started
with, and the committee is only re-drawn at an epoch boundary. Restart the
node with `bls-new.skey` **after** the new key shows up in the committee's
snapshot, not when the transaction is submitted. Restarting early means
signing with a key the committee does not hold — your votes are dropped.
:::

Watch the rotation land, then cut over:

```shell
# repeat until bksRegisteredIn advances to the new epoch
cardano-cli dijkstra query pool-state --stake-pool-id "$POOL_ID" \
  | jq '.[].poolParams.spsBlsKey.bksRegisteredIn'
```

Once that reads the newer epoch and the following epoch boundary has
passed, restart the node pointing `--shelley-bls-key` at `bls-new.skey`,
and keep the old key until you have seen the node vote again.

**How often?** Rotate well before `bksRegisteredIn + maxKeyAge`, not at it
— the update takes an epoch boundary to take effect, so a rotation
submitted in the last epoch of validity is already too late. Note that
`maxKeyAge` is not currently exposed as a protocol parameter, so check the
testnet's announced value rather than deriving it from
`query protocol-parameters`.

## What to send back

The testnet is where the protocol practices in public, and what you see
is part of the practice. If your node will not sync, a command here
fails, a trace event looks wrong, or the chain behaves in a way you did
not expect — that is exactly the signal the team wants.

When you report, include three things: the command or action you took,
what you expected, and what actually happened. Attach your node version
(`cardano-node --version`) and the relevant log lines.

- **Discord:** the [Musashi Dōjō Discord](https://discord.gg/AyUXD9VHn) —
  advice, guidance, and the place to raise issues, concerns, or bugs.
- **Issues:** [Ouroboros Leios repository](https://github.com/input-output-hk/ouroboros-leios/issues)
- **Design reference:** [CIP-0164](https://github.com/cardano-foundation/CIPs/blob/master/CIP-0164/README.md)
