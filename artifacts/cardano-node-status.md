# Leios Production Staging Branches (`cardano-node` and Dependencies)

**Created:** 2026-09-16
**Status:** Snapshot — reviewed data, but see the warning below.
**Provenance:** 🤖 (LLM-generated from GitHub branch/pin inspection, reviewed by Brian W. Bush)
**Parent document:** [Catalog of Leios Simulations and Models](./leios-simulation-model-catalog.md) — this page covers the *production implementation* the catalog's simulators and models are measured against.

> [!WARNING]
>
> **This is fast-moving work.** Everything below is a snapshot taken **2026-09-16**. The `leios-prototype` branches receive near-daily commits, dependency pins are bumped continuously (the node repinned consensus the day before this snapshot), and personal staging branches appear and merge weekly. Treat every commit hash and date here as stale on arrival; re-verify against the live branches before relying on any of it. The *conventions* (branch naming, pin discipline) are the durable content.

## Where the code is staged

The convention — stated in [`ouroboros-leios/demo/README.md`](https://github.com/input-output-hk/ouroboros-leios/blob/main/demo/README.md) and verified against the build pins — is **one `leios-prototype` branch per repository under `IntersectMBO`**. The node's [`cabal.project`](https://github.com/IntersectMBO/cardano-node/blob/leios-prototype/cabal.project) `source-repository-package` stanzas pin exact commits of each dependency, and at this snapshot every Leios-relevant pin was **exactly the HEAD of that dependency's `leios-prototype` branch** — i.e., the branch set moves in lockstep, node last.

### Core stack (all `IntersectMBO/<repo>`, branch `leios-prototype`)

| Repository | HEAD @ 2026-09-16 | Last commit | Latest work on the branch |
|---|---|---|---|
| [cardano-node](https://github.com/IntersectMBO/cardano-node/tree/leios-prototype) | `7e33674` | **2026-09-16** | LeiosDB volatile/immutable split; LeiosDB stats as node metrics (G. Lukyanov); cardano-testnet and tx-generator fixes (S. Nagel) |
| [ouroboros-consensus](https://github.com/IntersectMBO/ouroboros-consensus/tree/leios-prototype) | `b56977b` | 2026-09-15 | Immutable/volatile split of LeiosDB + garbage collection v2 |
| [ouroboros-network](https://github.com/IntersectMBO/ouroboros-network/tree/leios-prototype) | `4b3ab76` | 2026-06-30 | "Fixes due to BeareBytes class" — least-recently-moved of the set (see note below) |
| [cardano-ledger](https://github.com/IntersectMBO/cardano-ledger/tree/leios-prototype) | `1587f21` | 2026-09-06 | Fixed DST in BLS DSIGN instances |
| [cardano-api](https://github.com/IntersectMBO/cardano-api/tree/leios-prototype) | `e32d8c0` | 2026-09-07 | Adopt new cardano-base BLS API |
| [cardano-cli](https://github.com/IntersectMBO/cardano-cli/tree/leios-prototype) | `517ffe9` | 2026-09-07 | capi bump |
| [cardano-base](https://github.com/IntersectMBO/cardano-base/tree/leios-prototype) | `fbfb3f0` | 2026-09-03 | BLS proof-of-possession fixes |

Non-Leios `source-repository-package` pins in the node at this snapshot: `typed-protocols` (plain commit pin — no Leios branch exists there), `kes-agent`, `ekg-forward`.

### Deviations and periphery

- **[cardano-db-sync](https://github.com/IntersectMBO/cardano-db-sync/branches)** uses weekly naming instead: the active branch at this snapshot is **`leios-w36`** (2026-09-09, "Update to Leios prototype w36"); `leios-prototype-remake` is stale (2026-05-31). The **"wNN" weekly-release vocabulary** (w32–w36 seen so far; also used in red-team deployment coordination on Slack) lives here and in ops, *not* as cardano-node tags — the node carries only the demo tags `leios-202510-demo` and `leios-prototype-demo-202511`.
- **Deployment/config:** [`input-output-hk/cardano-playground`](https://github.com/input-output-hk/cardano-playground) branch **`leios-red-team`** (2026-08-24); the published testnet configuration is `environments-pre/leios` (network name **"musashi"**) on [book.play.dev.cardano.org](https://book.play.dev.cardano.org/environments-pre/leios/config.json), which [`ouroboros-leios/testnet/pin-config.sh`](https://github.com/input-output-hk/ouroboros-leios/blob/main/testnet/pin-config.sh) snapshots.
- **`tx-firehose`** (the devnet/testnet load generator) is a `bench/` package **inside** cardano-node@leios-prototype, not a separate repository.
- **No Leios branches** exist in `plutus` or `typed-protocols`.

### Feature staging (personal branches ahead of `leios-prototype`)

Feature work stages on personal-prefix branches before merging, visible in each repo's branch list at this snapshot — a useful watch-list for what lands next ❓🤖 (branch names only; contents not read):

- `bladyjoker/leios-prototype/{in-memory-db-improvements, late-join, **optimistic-mempool**, 2026w32}` — on **both** cardano-node and ouroboros-consensus. The optimistic-mempool pair is directly relevant to this project's planned mempool study.
- `ch1bo/leios-*` on cardano-ledger/cardano-api (committee selection and snapshotting, BLS key certs, protocol-parameter updates).
- `geo2a/*` (node — LeiosDB work), `nfrisby/*` (network — `leios-prototype-plus-matchedBlock`, demo branches), `karknu/*` and `mw/*` (network — mux demo, `mw/hello-smol-world`).
- ouroboros-network's bare `leios-prototype` being ~2.5 months quiet while `karknu/*` moved through August suggests networking work is staging via personal branches (or in the mux-demo / smol-world line) rather than that it has stopped ❓🤖 — worth confirming with Marcin Szamotulski or Karl Knutsson whether the branch's staleness is meaningful.

## How to re-verify (the durable part)

```bash
# Branch HEADs
for r in cardano-node ouroboros-consensus ouroboros-network cardano-ledger cardano-api cardano-cli cardano-base; do
  gh api "repos/IntersectMBO/$r/branches/leios-prototype" \
    --jq '"'$r' \(.commit.sha[:9]) \(.commit.commit.committer.date[:10])"'
done

# The node's dependency pins (compare against the HEADs above)
gh api "repos/IntersectMBO/cardano-node/contents/cabal.project?ref=leios-prototype" \
  --jq .content | base64 -d | grep -A3 source-repository-package
```

## Sources

- [`demo/README.md` § Prototypes — ouroboros-leios](https://github.com/input-output-hk/ouroboros-leios/blob/main/demo/README.md) (names the three core `leios-prototype` branches and the flake-input convention)
- `cardano-node@leios-prototype` [`cabal.project`](https://github.com/IntersectMBO/cardano-node/blob/leios-prototype/cabal.project) — pin ↔ branch-HEAD correspondence verified per repo, 2026-09-16, via GitHub API
- Branch listings and commit metadata via GitHub API, 2026-09-16 (all repos above)
- [facts.md § Upstream Artifacts](../facts.md) — the same snapshot recorded as dated facts
