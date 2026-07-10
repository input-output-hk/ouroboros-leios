# Changelog for the leios-prototype

We are using the ouroboros-leios repository to cut releases on preliminary versions of the cardano-node. This is the change log of things in the prototype and may be useful to keep track of what to expect also from deployed nodes on the Leios testnet.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).
As a minor extension, we may also keep `UNRELEASED` changes on top of it.

## prototype-2026w28 - 2026-07-10

Fixes "no such table: ebs" and block re-application and un-certified eb application

- Fix [Some new nodes die with: LeiosDbException "no such table: ebs" #983](https://github.com/input-output-hk/ouroboros-leios/issues/983)
- Fix block re-application so it uses the Leios workflow as block application
- Fix unconditional application of uncertified EBs from the ImmDB on startup

## prototype-2026w27b - 2026-07-08

Fixes permanent stalling when syncing from genesis.

- Fix use of headerContainsLeiosCert for HFC
- Fix pruning logic which was deleting some EBs from an acquired set of EBs
- Fix pipelined LeiosFetch client from incorrect discards
- Fix NTC chainsync server certificate gate on EB inlining

## prototype-2026w27a - 2026-07-08

The partial fix to the previous `prototype-2026w27` release.
Improves the overall stability of the network significantly (no forks)
but still suffering from the stall when syncing from Genesis.

- Fix SQLite segfaults due to use after free in `sqlite3_finalize`.
- Improve SQLite LeiosDB performance that uses `JSON1` queries

## prototype-2026w27 - 2026-07-05

**BREAKING** changes to block serialization as we added proper Leios certificates and also changed how EB announcements are encoded in block headers.

**Requires respin:** Delete your local state and use the new `musashi` network config from https://book.play.dev.cardano.org/adv-musashi.html

- Resolve `LeiosDbConfig` relative to `--database-path` [#959](https://github.com/input-output-hk/ouroboros-leios/issues/959)
  - This will put `leios.db` next to `volatile/` storage by default. Can be overridden using relative or absolute paths in `LeiosDbConfig.Filepath` .

- Replace staging area with out of order processing of EBs in chain selection [consensus#2076](https://github.com/IntersectMBO/ouroboros-consensus/pull/2076)
  - Should result in (slightly) faster catch-up and less/no timeouts of the block fetch protocol.
  - No API changes, but different error calls if things go bad.

- Aggregate and verify proper Leios certificates in block bodies [#790](https://github.com/input-output-hk/ouroboros-leios/issues/790), [ledger#5872](https://github.com/IntersectMBO/cardano-ledger/pull/5872) and [consensus#2102](https://github.com/IntersectMBO/ouroboros-consensus/pull/2102)
  - The last big part of the voting and certification pipeline will require enough votes (75% of stake) before endorsed transactions can get applied and contribute to the throughput.
  - Still basic committee selection of "everyone votes".
  - No equivocation detection or EB tx validation (yet).
  - L_hdr = 1, L_vote = 4, L_diff = 3 (implicitly via min cert age >= 10 slots)

- More changes to the block header encoding of announcements [ledger#5889](https://github.com/IntersectMBO/cardano-ledger/pull/5889).

## prototype-2026w26 - 2026-06-26

Minor fixes to the Dijkstra era cli plumbing. No node updates in this release

- Fix `cardano-cli dijkstra transaction build` commands and improve stake pool instructions with it.
- Build and add macos (arm64) binaries to the release.

## prototype-2026w25 - 2026-06-19

Stabilization release on EB fetching / staging plus the two Dijkstra-era query
fixes in api/cli. No N2N or N2C wire format changes since w24.

- Fixed stalls of block fetch. This improves staying in sync and catching up behavior.
  - First round of fixes to the staging area [#2074](https://github.com/IntersectMBO/ouroboros-consensus/pull/2074)
  - Second round of improvements to the fetching logic [#2083](https://github.com/IntersectMBO/ouroboros-consensus/pull/2083)
  - We are looking into a more holistic change to catching up semantics, ideally with better performance next.

- Fix `db-synthesizer`to honor `ExperimentalHardForksEnabled` [#2077](https://github.com/IntersectMBO/ouroboros-consensus/pull/2077)

- Fix `cardano-cli` queries about stake and governance. This should be fairly usable now on `Dijkstra`.

> [!IMPORTANT]
>
> The network mini-protocols and CDDL wire formats in [CIP-164](https://github.com/cardano-foundation/CIPs/blob/master/CIP-0164/README.md) have evolved and the prototype is not consistent with them (yet). Use the `leios-prototype` branch in [cardano-blueprint](https://cardano-scaling.github.io/cardano-blueprint/pr-preview/pr-67/network/node-to-node/leios-notify/index.html) for network protocol descriptions and CDDLs, as well as the `leios-prototype` branch in [cardano-ledger](https://github.com/IntersectMBO/cardano-ledger/blob/leios-prototype/eras/dijkstra/impl/cddl/data/dijkstra.cddl#L19) for the block format used currently.

## prototype-2026w24 - 2026-06-11

A few hot fixes and some progress on the voting pipeline of the prototype

- Fixed CertRB data not available [#2058](https://github.com/IntersectMBO/ouroboros-consensus/pull/2058)
  - Using a staging area, which traces staging and release of CertRBs that are missing transactions
  - Also fixed CertRB resolution on restart (when loading from immutable db)

- Fixed UNIQUE constraint violations are caught and traced [#2062](https://github.com/IntersectMBO/ouroboros-consensus/pull/2062)
  - Visible through new `LeiosDbInsertCollision` trace with Warning severity
  - Kept the constraint to detect race conditions in production

- Fixed N2C inlining / encoding of certifying ranking blocks.

- Added vote signing and committee selection [#2039](https://github.com/IntersectMBO/ouroboros-consensus/pull/2039)
  - Votes are now signed and validated. A basic (everyone votes) committee is selected and used for vote validation.
  - **BREAKING** N2N wire format change: LeiosNotify.MsgVote signature is now BLS signature, not a placeholder Bool.
  - New trace: `LeiosBlockCertified`

## prototype-2026w23 - 2026-06-09

This version was first deployed to the leios testnet and also used
partially on the node diversity workshop for the very first experiments.

This is includes roughly:

- Based on PV12 / Dijkstra enabled node version 11.0.1
- Forges EBs when mempool full enough
- Diffuses EBs and their closures as they are offered (no dedicated EB announcement)
- Votes on completed EB closures (no "too old" or other validation)
- Assumes all EBs that are older than 10 slots as certified
- Includes certificates in RBs when cert old enough
- Resolves transactions from certificates when adopting a block
- No certificate verification whatsoever
- Inlines transactions for the N2C chain sync server

