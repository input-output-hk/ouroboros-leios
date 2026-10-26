# Devnet genesis

Shared by proto-devnet and dozen-devnet (the latter reads this directory via
`SHARED_CONFIG_DIR`). Everything here is deliberately test-only. Two parts of it
are non-obvious enough to write down, because JSON cannot hold a comment and
both look like arbitrary numbers otherwise.

## Epoch geometry (shelley-genesis.json + byron-genesis.json)

```text
shelley  securityParam    40
shelley  epochLength    3600      # 1 hour at slotLength 1
shelley  activeSlotsCoeff 0.05
byron    protocolConsts.k 40      # must equal securityParam
```

**Both k values must match.** The hard-fork combinator takes Byron's:

```haskell
k = assert (kByron == kShelley) kByron     -- Cardano/Node.hs:878
```

and that assert is compiled out of a release build, so a mismatched pair starts
happily and fails much later somewhere unrelated. It cost us a devnet: with
kByron=2160 and kShelley=40, the ChainDB immutabilised at depth 2160 and so
never immutabilised anything, leaving the immutable tip at Origin, while the
Leios announcement validator forecast from that tip with a 3k/f = 2400 horizon
derived from kShelley. At slot 2408 every announcement began failing
`OutsideHorizon`, which by design tears down the Leios mini-protocol with that
peer -- so all voting stopped network-wide 40 minutes in, with the chain itself
looking perfectly healthy.

Mainnet uses `epochLength = 10k/f`, but that is convention. The only rule the
node enforces is `epochLength >= 3k/f`, in `validateGenesis`
(`EpochNotLongEnough`). Between the floor and the convention sit two thresholds
that matter more than the ratio:

| window | slots | wall time | why it matters |
| --- | ---: | ---: | --- |
| 3k/f | 2400 | 40 min | Stability window. Also the hard floor. |
| 4k/f | 3200 | 53 min | Praos only updates the candidate nonce while `slot + 4k/f < firstSlotNextEpoch` (`Praos.hs`). An epoch at or below this **freezes epoch randomness permanently**. |
| 8k/f | 6400 | 107 min | Reward pulsing starts at 4k/f into the epoch and is forced complete by 8k/f. This is the real reason mainnet picks 10k/f. |
| epoch | 3600 | 60 min | |

So `k` had to stay **under 45** for a one-hour epoch to keep its nonce alive at
all; 40 leaves a 400-slot window (~20 expected blocks) feeding the next epoch's
nonce, where k=44 would leave only 80 slots (~4 blocks).

We are knowingly under 8k/f: the reward pulser gets forced to finish at the
epoch boundary instead of pacing through the epoch. With three pools and four
funded addresses that computation is trivial, so it buys a one-hour governance
turnaround for no practical cost.

`securityParam` 40 also means only 40 blocks of rollback (~13 min of chain at
f=0.05), and the 40-minute stability window is the slack available for
restarting nodes without the chain outrunning them.

## Protocol version and funds (shelley-genesis.json)

```text
protocolVersion   12.0
initialFunds      three delegators 30M ADA each, utxo1 5M, utxo2 5M
```

The chain starts at protocol version 12 because the worst-case Plutus load
(`PlutusBench`) uses builtins that only exist from there on: `multiScalarMul`
and `replicateByte` are priced only in the 350-entry PlutusV3 cost model, which
needs PV12 and has to be enacted on chain (`EnactPlutusCostModel`).

`utxo2` is funded for that bench alone, so it never competes with the
tx-firehoses (the delegators) or a governance action (`utxo1`) for a UTxO. The
two share the 10M ADA `utxo1` used to hold: the initial funds already add up to
`maxLovelaceSupply`.

## Governance (conway-genesis.json)

```text
committeeMinSize  0
committee         { members: {}, threshold: 0 }
initialDReps      3 keys, held in ../drep-keys/
delegs            each delegator's stake -> one DRep
```

`committeeMinSize` **must be 0** for any governance action to ratify here. The
constitutional committee is empty, and the ledger only reads an empty committee
with threshold 0 as accepting when `activeCommitteeSize >= committeeMinSize`
(`Conway/Governance/Internal.hs`); otherwise the committee counts as voting No
and every `ParameterChange` sits until it expires. This is the same shortcut
cardano-testnet takes (`ucppCommitteeMinSize = 0`) and is not something a real
network should do — it means the CC approves everything automatically.

The three `initialDReps` are keys in `../drep-keys/`, and each of the three
delegator staking credentials is `DelegVote`-delegated to one of them, so all
three voting Yes is 100% of delegated stake and clears every DRep threshold
(highest is `ppGovGroup` at 0.75). The DReps that were here before had no
signing keys anywhere in the repo and so could never vote.

See `../../dozen-devnet/propose-pparam-update.sh` for the submit/vote/enact
cycle, including the parameters the CLI cannot currently express.
