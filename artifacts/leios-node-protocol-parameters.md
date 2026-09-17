# Protocol Parameters and Admission Inequalities in the Leios Prototype Node

**Created:** 2026-09-17
**Status:** Draft for review.
**Provenance:** 🤖 (LLM-generated from direct source reading, pending human review)
**Companion documents:** [Timing-inequalities timeline](./leios-timing-inequalities.svg) (the diagram of § 2 and § 7) · [Mempool/TxCache map](./leios-node-mempool-txcache.md) · [Transaction-lifecycle diagram](./leios-node-tx-lifecycle.svg) · [Staging branches](./cardano-node-status.md)

> [!WARNING]
>
> **Fast-moving code.** Pinned to the same 2026-09-16 build set as the companion documents: `ouroboros-consensus @ b56977b`, `cardano-node @ 7e33674`, and — newly cloned for this document, both still exactly at the node's `cabal.project` pins — `cardano-ledger @ 1587f21` and `cardano-base @ fbfb3f0`. Deployed values are from the musashi configs fetched **2026-09-17** (`book.play.dev.cardano.org/environments-pre/leios`), which redeploys weekly.

This document answers: **which parameters, and which inequalities over them, decide whether ranking blocks (RBs), endorser blocks (EBs), votes, and certificates are created and accepted or rejected** in the `leios-prototype` node — and where each parameter actually lives.

Terminology used below: Cardano Improvement Proposal 164 (CIP-0164); execution units (ExUnits); key-evolving signature (KES); verifiable random function (VRF); operational certificate (OCert); Boneh–Lynn–Shacham (BLS) signature; and software transactional memory (STM).

## 1. Where the parameters live: five tiers

| Tier | Examples | Governable? |
|---|---|---|
| **Dijkstra ledger protocol parameters** ([`PParams.hs:199-230`](https://github.com/IntersectMBO/cardano-ledger/blob/1587f21a7d1306dc590c2749a5c66232ef66aad0/eras/dijkstra/impl/src/Cardano/Ledger/Dijkstra/PParams.hs#L199)) | `leiosAnnouncementPeriodLength` (L_hdr, ms), `leiosVotePeriodLength` (L_vote, ms), `leiosDiffusionPeriodLength` (L_diff, ms), `leiosCommitteeSize` (N_c, Word16), `leiosQuorumStakeThreshold` (τ, UnitInterval), `maxEndorserBlockReferencesSize`, `maxEndorserBlockTxsSize`, `maxEndorserBlockExUnits`, `maxRefScriptSizePerEndorserBlock` | Yes — on-chain governance (all in the `NetworkGroup`/`SecurityGroup` update groups) |
| **Derived from `Globals`** | `maxKeyAge = ⌈maxKESEvo·slotsPerKESPeriod / slotsPerEpoch⌉ + 2` epochs ([`Snap.hs:145`](https://github.com/IntersectMBO/cardano-ledger/blob/1587f21a7d1306dc590c2749a5c66232ef66aad0/eras/dijkstra/impl/src/Cardano/Ledger/Dijkstra/Rules/Snap.hs#L145)) — deliberately *not* a parameter, "keeps voting-key rotation in step with KES rotation" | Indirectly (KES setup) |
| **Consensus wall-clock stubs** | `lHdrWait = 3 s` (stub for **3·L_hdr**, doubling as the equivocation-observation window), `lVoteWindow = 4 s` (stub for L_vote) ([`LeiosVoting.hs:140-147`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosVoting.hs#L140)) — TODO-marked to be read from the ledger, *which already carries them* | No — recompile |
| **Demo/wire constants** | `maxMsgLeiosBlockBytesSize = 500 kB` ([`LeiosDemoTypes.hs:2214`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoTypes.hs#L2214), "from CIP-0164's recommendations"), `maxEBClosureSize = 12 MB` (`:2248`), `maxTxsPerEb = maxEbTxCount(500 kB) = 13,888` (`:2241`), `fetchPriorityWindowSlots = 10` (stub for L in slots), job caps 64 KiB / 20,000 txs, ingress queues ([`:929`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoTypes.hs#L929)) | No — recompile |
| **Node configuration** | `MempoolCapacityBytesOverride` (musashi: **2,000,000 B**), `LeiosDbConfig` | Per-deployment |

The known hazard at the boundary between tiers 1 and 4 is spelled out in a FIXME at [`LeiosDemoTypes.hs:2202-2211`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoTypes.hs#L2202): governance can raise `maxEndorserBlockReferencesSize` / `maxEndorserBlockTxsSize` past the wire constants (the ledger's own example values, 512 KiB and 12 MiB, already exceed the 500 kB and 12 MB here), and "nothing rejects that today" — the forge merely **clamps** where it reads ([`Mempool.hs:752-792`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Ledger/Mempool.hs#L752), `min Leios.maxTxsPerEb …`). Musashi's deployed values (100 kB / 1 MB) are safely inside the wire limits.

## 2. The inequalities, decision by decision

### 2.1 EB creation (forge) — capacity inequalities

[`partitionMempool`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/NodeKernel/Forge.hs#L739) takes one snapshot and splits by **measure**, so every capacity below is a coordinate-wise `≤` enforced by `snapshotTake`:

- **RB:** `rbCap = blockCapacityTxMeasure` — the ordinary Praos block measure.
- **EB:** `ebCap = ebCapacityTxMeasure` = [`leiosEndorserBlockMeasure`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Ledger/Mempool.hs#L752), a `DijkstraMeasure` whose coordinates are all ledger parameters:
  - Σ tx bytes ≤ `maxEndorserBlockTxsSize` (musashi: 1,000,000 B)
  - Σ ExUnits ≤ `maxEndorserBlockExUnits` (musashi: 310 M mem / 100 G steps)
  - Σ ref-script bytes ≤ `maxRefScriptSizePerEndorserBlock` (musashi: 4,000,000 B)
  - tx **count** ≤ `min(maxTxsPerEb^wire, maxEbTxCount(maxEndorserBlockReferencesSize))` — the references-size parameter converted to a count using the 36 B **minimum** encoded entry size ([`maxEbTxCount`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoTypes.hs#L2217-L2235)); musashi: `(100,000 − 5) div 36 = 2,777` vs the wire bound `(500,000 − 5) div 36 = 13,888`, so the parameter-derived count governs.
- This fourth coordinate is only a count proxy for the reference-list byte limit. Actual [`leiosEbBytesSize`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoTypes.hs#L1043-L1049) sums each 34-byte encoded hash and the variable-width encoding of that transaction's size. Consequently, `tx count ≤ maxEbTxCount(limit)` is necessary but does **not** imply `actual encoded references size ≤ limit`; the honest forge precisely enforces three resource coordinates and this conservative-minimum count conversion, not the fourth byte inequality itself. ⚠️ **RISK**
- An EB is forged and announced **iff the overflow prefix is non-empty** (`mkEb = case nonEmpty fbEbTxs of Nothing -> pure Nothing …`, [`Forge.hs:161`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Ledger/Forge.hs#L161)); the announcement (hash, size) then rides in the RB header.

### 2.2 CertRB creation (forge) — `decideLeiosCertify`

[`Forge.hs:288-362`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/NodeKernel/Forge.hs#L288). The block being forged certifies iff **all** of:

1. The tip header's protocol state carries an announcement: `protocolStateLeiosAnnouncement ≠ Nothing` (so certification is only possible in the announcing RB's **direct successor** — "the linear aspect of linear Leios").
2. The gap has elapsed: `currentSlot − announcedSlot > minGap`, where

   `minGap = ⌈(3·leiosAnnouncementPeriodLength + leiosVotePeriodLength + leiosDiffusionPeriodLength) / slotLength⌉`

   ([`minCertificationGap`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoTypes.hs#L2257), milliseconds over the era's slot length, rounded up). The source predicate is `elapsed ≤ minGap ⇒ Nothing`. **Musashi genesis ⇒ ⌈14000 ms / 1000 ms⌉ = 14 slots** (see § 5 for the conflict with the earlier Slack claim of 10).
3. The closure is locally present: `leiosDbLookupEbClosure ≠ Nothing` (with an in-code TODO questioning whether this should instead warn on cert-without-closure).
4. A certificate has been assembled for the tip's hash: `queryCert voteState announcingRb = Just cert`.

Otherwise the block is an ordinary TxRB (§ 2.1). There is no other timing upper bound at forge time: an announcement older than the gap still certifies as long as it is still the tip's announcement.

### 2.3 Vote creation — `runLeiosVoting` / `goVote`

[`LeiosVoting.hs:240-400`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosVoting.hs#L240). Prerequisite: the node has a `topLevelConfigVotingKey` (else the whole thread is disabled). Per acquired EB closure (`AcquiredEbTxs`), in order, each failure traced as a `LeiosNotVotedReason`:

1. **Timing (wall clock, stub-parameterized):** the window is `[onset(announcedSlot) + lHdrWait, onset + lHdrWait + lVoteWindow]` = onset + [3 s, 7 s]. Checked **twice**: `now > deadline ⇒ TooLate` before opening a forker ([`:321`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosVoting.hs#L321)), and again after closure validation ([`:353`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosVoting.hs#L353)) because "applying a closure takes real time." The 3 s pre-wait is the **equivocation-observation window** (observe a second announcement before signing). A closure completing after the window opens is checked immediately.
2. **Chain condition:** the volatile tip's header state must announce exactly this EB (`tipAnnouncerFor`), else `ChainTipDoesNotAnnounce`.
3. **Committee seat:** `getLeiosSeatId vk (getLeiosCommittee ls) = Just seatId`, else `NotOnCommittee` — the seat is found by *searching the committee for our BLS verification key*.
4. **Closure validity:** `validateEbClosure = EbClosureValid`, else `EbTxsInvalid` (reapply-on-cache-hit per the lifecycle map § 4.2).
5. Sign (`signLeiosVote`, BLS over the announcing RB hash) and `addVote` locally; a non-`Added` result is traced `VoteRejected`.

**Known gaps, in-code:** a `FIXME: Check the EB references size, txs size, ex units and ref scripts capacities` sits *above the closure validation* — a voter does **not** check the § 2.1 capacity caps; and a TODO records the **epoch-boundary seat race** (the positional `LeiosSeatId` may become someone else's seat between the forker read and `addVote`).

### 2.4 Vote acceptance and certificate assembly — `LeiosVoteState.addVote`

[`LeiosVoteState.hs:98-188`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosVoteState.hs#L98). For every vote, local or received via `MsgLeiosVotes` (the LeiosNotify client feeds them straight in, [`NodeToNode.hs:575`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/Network/NodeToNode.hs#L575)):

1. **Dedup:** exact-vote set membership ⇒ `AlreadyKnown` (BLS verification deliberately outside the STM transaction — "the pairing is ms-scale").
2. **Committee & threshold come from the current selected tip's ledger state** (`ChainDB.getCurrentLedger`, [`NodeKernel.hs:796-802`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/NodeKernel.hs#L796)); no committee ⇒ `NoCommittee`.
3. **Vote validity** ([`validateLeiosVote`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoTypes.hs#L1180)): the seat index resolves on the committee (`SignerNotInCommittee`), the seat has a key (`SignerHasNoKey`), and the BLS signature over the announcing-RB hash verifies (`InvalidSignature`). Success yields the **seat's weight**.
4. **Tally and quorum:** per announcing-RB point, `totalW := psTotal + weight − oldWeightOfThisSeat` (re-votes replace, not add), and the certificate is assembled **eagerly, exactly once**, when

   `totalW ≥ threshold`, with `threshold = unboundRational (ppLeiosQuorumStakeThreshold)` ([`Ledger.hs:1024-1056`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Ledger/Ledger.hs#L1024); musashi: 0.75)

   via `aggregateLeiosCert` (BLS aggregation over the accumulated signatures; [`LeiosVoteState.hs:158`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosVoteState.hs#L158)).

**Weight semantics:** `Weight = Rational` ([`Cardano/Crypto/Leios.hs:120`](https://github.com/IntersectMBO/cardano-base/blob/fbfb3f05d8092492f000264edca2d7a1a105741a/cardano-crypto-leios/src/Cardano/Crypto/Leios.hs#L120)); a seat's weight is its pool's **share of the epoch's total active stake** (`lcWeight`, ledger-computed), so committee weights sum to ≤ 1 and τ compares like CIP-0164's inequality `Σ stake(votes) ≥ τ · stake_total-active`.

**Known gaps, in-code:** votes are **not epoch-tagged** — "TODO: disallow votes from different epoch"; and the cached certificate is not tagged with the committee that produced it ("FIXME … keep track of which committee the cert is for"). There is also still no vote-state GC.

### 2.5 Certificate / CertRB acceptance — `applyBlock` + `verifyLeiosCert`

Ledger-DB validation of a block carrying a cert ([`Forker.hs:595-660`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Storage/LedgerDB/Forker.hs#L595)), each failure a distinct `LeiosExtValidationError`:

1. Parent's chain-dep state announces an EB, else `LeiosCertificateWithoutAnnouncement`.
2. `FIXME: Check the min certification gap between announcement and certification` — **the § 2.2 gap inequality is not checked here** ([`:618`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Storage/LedgerDB/Forker.hs#L618)); forge-side only.
3. The announcing RB hash is determinable (non-genesis parent), else `LeiosCertificateAfterGenesis`.
4. A committee exists on the ledger state, else `LeiosMissingCommittee`; a threshold exists, else `LeiosMissingThreshold`.
5. [`verifyLeiosCert`](https://github.com/IntersectMBO/cardano-base/blob/fbfb3f05d8092492f000264edca2d7a1a105741a/cardano-crypto-leios/src/Cardano/Crypto/Leios.hs#L289) over (committee, τ, announcing-RB hash, cert):
   - committee ≤ 65,536 seats (`MalformedCommittee`), signer bitfield exactly `⌈N_c/8⌉` bytes (`MalformedSigners`);
   - **every set bit resolves to a keyed seat** — any bit on a keyless seat rejects up front (`SignerWithoutKey`);
   - **`Σ seatWeight(signers) ≥ τ`**, else `InsufficientWeight`;
   - the **aggregate BLS12-381 verification** over the aggregated public keys and the announcing-RB hash passes, else `InvalidSignature`. (Proofs of possession were checked at committee construction, `mkLeiosCommittee`.)
6. `FIXME: Check the EB references size, txs size, ex units and ref scripts capacities` — **the § 2.1 capacity caps are not checked at acceptance either.**
7. The closure resolves from the LeiosDb and applies (`resolveAndApplyLeiosClosure`), then `tickThenApply` of the CertRB itself — ordinary ledger rules over the spliced transactions.

Chain selection separately **parks** a CertRB whose closure is absent (transient exclusion, lifecycle map § 4.3) — availability gating, not validity.

### 2.6 Announcement and EB-body acceptance (network layer)

- **Announcement** ([`validateAnnouncementHeader`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoLogic/Announcements/Validate.hs)): the announced slot must lie in the forecast window anchored at the **immutable tip** — below-anchor and beyond-horizon both **disconnect** (an unbounded supply of bogus far-future slots makes ignoring unsafe). It then runs deliberately relaxed, out-of-context chain-dependent validation: the VRF election proof and KES/OCert signature are checked fully, the OCert counter upper bound is skipped, and a too-small or unknown counter becomes `StaleOCIN` — accepted from the peer but neither processed nor relayed — rather than rejection ([`Leios.hs:255-277`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Ledger/Leios.hs#L255-L277)). Applicable envelope limits also run. Per upstream peer, ≤ 2 distinct announcements per election (`ElState`); a third or repeat disconnects.
- **EB body** (`processLeiosBlock`): size equals the request/offer-carried size (the poisonable check on the worry list), hash matches, no duplicate tx references; wire cap `maxMsgLeiosBlockBytesSize = 500 kB` and closure-fetch cap `maxEBClosureSize = 12 MB` (a FIXME notes this is unrelated to the ledger's `maxEndorserBlockTxsSize` today).

### 2.7 Header-level Leios rules: specified, not implemented

The Praos protocol layer records the announcement into the chain-dep state but a TODO at [`Praos.hs:526-537`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus-protocol/src/ouroboros-consensus-protocol/Ouroboros/Consensus/Protocol/Praos.hs#L526) lists the header checks **not yet enforced**, with intended error constructors:

- `LeiosCertRBWithoutAnnouncement` — a set cert bit requires the predecessor to announce;
- `LeiosCertTooYoung` — "check the slot gap against L" (the **follower-side gap check**, same hole as § 2.5 item 2);
- `LeiosEbTooBig` — the maximum EB body (references) size;
- `LeiosEbTxsTooBig` — the maximum closure size;
- `LeiosEbCertExclusivity` — a set cert bit requires an empty tx sequence.

Consequently the **announced size field is nowhere validated against a parameter** at this snapshot — [`Validate.hs`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoLogic/Announcements/Validate.hs)'s module comment claiming Dijkstra header rules "already fold in … the EbBody size bound" is contradicted by this TODO in the same commit (another stale comment, joining the two found on 2026-09-17). ❓🤖 **SCRUTINY:** verified by reading `updateChainDepState`'s Dijkstra path; a deeper ledger-side check could hide elsewhere, but grep finds no consumer of `maxEndorserBlockReferencesSize` outside `PParams.hs` and the forge measure.

## 3. The committee: who may vote, with what weight

Seating is a **ledger** responsibility (the consensus-side [`selectCommitteeByStake`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoTypes.hs#L1105) is used only by test tooling, and its haddock — "cumulative stake reaches σ_c" — mismatches its code, which counts *seats*):

- At each epoch boundary the SNAP rule seats the committee **on the fresh mark snapshot**, judged for the epoch it will actually vote in (`eNo + 1`), sized by `leiosCommitteeSize` ([`Snap.hs:90-140`](https://github.com/IntersectMBO/cardano-ledger/blob/1587f21a7d1306dc590c2749a5c66232ef66aad0/eras/dijkstra/impl/src/Cardano/Ledger/Dijkstra/Rules/Snap.hs#L90)); consensus then reads it from `ssStakeSet` so voting weight and block-production weight stay in step ([`Ledger.hs:1024`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Ledger/Ledger.hs#L1024)).
- [`selectLeiosCommittee`](https://github.com/IntersectMBO/cardano-ledger/blob/1587f21a7d1306dc590c2749a5c66232ef66aad0/libs/cardano-ledger-core/src/Cardano/Ledger/State/LeiosCommittee.hs#L70): the **top `N_c` pools by stake, descending, ties by ascending pool id** — CIP-0164's *stake-based truncation* scheme. The CIP identifies weighted Fait Accompli with Local Sortition (wFA^LS) as the scheme from earlier drafts; current committee selection is deterministic, with no sortition.
- A seated pool is **keyless** (occupying a seat but unable to vote — and any cert bit on it invalidates the cert) if it has no registered BLS key, the proof of possession fails, or the key has aged out: keys are honored only while `epoch < registeredIn + maxKeyAge`, with `maxKeyAge = ⌈maxKESEvo · slotsPerKESPeriod / slotsPerEpoch⌉ + 2` epochs (musashi: `⌈62·129600/21600⌉ + 2 = 374` six-hour epochs).
- Genesis boot: [`seatInitialLeiosCommittee`](https://github.com/IntersectMBO/cardano-ledger/blob/1587f21a7d1306dc590c2749a5c66232ef66aad0/eras/dijkstra/impl/src/Cardano/Ledger/Dijkstra/Transition.hs#L70) seats the mark snapshot with a one-epoch key allowance, since SNAP never ran.
- Hard bound: ≤ 65,536 seats (`LeiosSeatId` is a `Word16`; the cert bitfield is `⌈N_c/8⌉` bytes — 113 B at musashi's N_c = 900).

## 4. Enforcement asymmetry — the summary picture

| Rule | Forge (creation) | Voter | Acceptance (ledger/header) |
|---|---|---|---|
| EB capacity caps (tx bytes / ExUnits / ref-scripts / reference bytes) | ⚠️ first three exact; reference bytes reduced to a minimum-size count proxy | ❌ FIXME | ❌ FIXME (`Forker.hs`) + TODO (`Praos.hs`); no ledger rule consumes the params |
| Minimum certification gap | ✅ `decideLeiosCertify` | n/a | ❌ FIXME (`Forker.hs:618`) / TODO `LeiosCertTooYoung` |
| Vote window (3 s / 7 s from announced-slot onset) | n/a | ✅ but **hard-coded stubs**, not the ledger's L_hdr/L_vote | ❌ received votes face no timing check (no epoch check either — TODO) |
| Quorum `Σ weight ≥ τ` | ✅ (assembles eagerly at threshold) | n/a | ✅ `verifyLeiosCert` — **the one fully-enforced acceptance rule** |
| Vote signature/committee membership | ✅ (own seat lookup) | ✅ | ✅ (per-vote at ingest; aggregate at cert) |
| CertRB carries no txs (cert exclusivity) | ✅ by construction (`mkBody`) | n/a | ❌ TODO `LeiosEbCertExclusivity` |
| Actual encoded references size ≤ references-size param | ❌ count clamp alone does not imply the byte inequality | ❌ | ❌ TODO `LeiosEbTooBig`; body checked only against the peer's own offer |

The pattern is asymmetric but not simply creation-versus-acceptance: **the honest producer precisely enforces transaction bytes, ExUnits, and reference-script bytes, and approximates the reference-list byte limit with a minimum-size count ceiling; the corresponding Byzantine-facing acceptance checks are FIXME/TODO**, except the quorum-and-signature core of certificate verification, which is complete. This sharpens the scope-candidate conformance property (workstream (e)): the timing rule is only one of five header-level checks awaiting enforcement.

## 5. Deployed values (musashi, fetched 2026-09-17)

From [`dijkstra-genesis.json`](https://book.play.dev.cardano.org/environments-pre/leios/dijkstra-genesis.json) (the configuration's Dijkstra genesis hash begins `aa1238f5…`), [`shelley-genesis.json`](https://book.play.dev.cardano.org/environments-pre/leios/shelley-genesis.json) (slot = 1 s, epoch = 21,600 slots, f = 0.05, k = 108), and [`config.json`](https://book.play.dev.cardano.org/environments-pre/leios/config.json):

| Parameter | Value | Derived |
|---|---|---|
| `leiosAnnouncementPeriodLength` (L_hdr) | 1,000 ms | — |
| `leiosVotePeriodLength` (L_vote) | 4,000 ms | vote window: onset +3 s … +7 s (matches the consensus stubs) |
| `leiosDiffusionPeriodLength` (L_diff) | 7,000 ms | — |
| ⇒ `minCertificationGap` | — | **⌈14,000/1,000⌉ = 14 slots** |
| `leiosCommitteeSize` (N_c) | 900 | cert bitfield 113 B |
| `leiosQuorumStakeThreshold` (τ) | 0.75 | — |
| `maxEndorserBlockReferencesSize` | 100,000 B | `maxEbTxCount` ⇒ **≤ 2,777 txs/EB** (wire count 13,888 not binding); this count does not guarantee the actual encoded list is ≤ 100,000 B |
| `maxEndorserBlockTxsSize` | 1,000,000 B | 1 MB closures — well under the 12 MB fetch cap |
| `maxEndorserBlockExecutionUnits` | 310 M mem / 100 G steps | — |
| `maxRefScriptSizePerEndorserBlock` | 4,000,000 B | — |
| `MempoolCapacityBytesOverride` (node config) | 2,000,000 B requested | [`computeMempoolCapacity`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Mempool/Capacity.hs#L54-L82) rounds up to whole block measures: `ceil(2,000,000 / 90,112) × 90,112` = **2,072,576 B effective byte coordinate**; CIP-0164's ≥ 2×(RB + EB-txs) at these params wants 2,180,224 B ❓🤖 |

> [!WARNING]
> ❓🤖 **SCRUTINY — the 10-vs-14 gap discrepancy.** Slack (2026-08-26, kleioscan thread) and our earlier documents state a 10-slot certification gap on musashi, and the in-code comment on `fetchPriorityWindowSlots = 10` says "~14 s on mainnet, ~10 on the testnet." The genesis fetched 2026-09-17 yields **14 slots**. Either the weekly redeploys changed the periods between August and now, or the earlier "10" described a differently-parameterized week (or conflated the fetch-window constant). Unresolved; re-verify against the current week with:
> `curl -sL https://book.play.dev.cardano.org/environments-pre/leios/dijkstra-genesis.json | python3 -c "import json,sys; g=json.load(sys.stdin); print((3*g['leiosAnnouncementPeriodLength']+g['leiosVotePeriodLength']+g['leiosDiffusionPeriodLength'])/1000)"`

## 6. CIP-0164 cross-check

- **Quorum:** the CIP's inequality `Σ_{v∈votes} stake(v) ≥ τ · stake_total-active` is exactly `verifyLeiosCert`'s check under the share-of-active-stake weight normalization; the CIP constrains `0.5 < τ < σ(N_c)` and calls τ "the safety-critical parameter of the voting layer." No prototype code enforces the `0.5 < τ` lower bound or the `τ < σ(N_c)` feasibility bound on governance updates. ❓🤖
- **Committee scheme:** the CIP now specifies **stake-based truncation** (top-N_c, deterministic — "quorum failure is not caused by sortition randomness"), with weighted Fait Accompli with Local Sortition (wFA^LS) relegated to earlier drafts. Our previous documents' wFA^LS/sortition committee tags were stale against the current CIP and are corrected as of this document.
- **Timing:** the CIP's L_hdr/L_vote/L_diff appear in the ledger as millisecond durations; the CIP cadence 3·L_hdr + L_vote + L_diff = 14 s matches musashi's genesis exactly (at 1 s slots ⇒ 14 slots).
- **Certificate size:** `⌈N_c/8⌉`-byte bitfield + one BLS12-381 aggregate signature, as in the CIP's certificate section.

## 7. The timing timeline: CIP-0164's vote conditions against the implementation

Diagrammed in [leios-timing-inequalities.svg](./leios-timing-inequalities.svg). Two findings came out of checking the CIP's numbered rules one at a time rather than reading the timing code on its own terms.

### 7.1 The certification gap is off by one slot

[CIP-0164 step 5](https://github.com/cardano-foundation/CIPs/blob/d07a30bca36a28535afa151915bb4900b2116d3a/CIP-0164/README.md#specification) says a certificate may be included if `RB′` is **at least** `gap` slots after the announcing RB, i.e. `slot(RB′) − s ≥ gap`. The implementation's guard is

```haskell
| unSlotNo currentSlot - unSlotNo (Leios.pointSlotNo ebPoint) <= unSlotNo minGap -> pure Nothing
```

([`Forge.hs:322`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/NodeKernel/Forge.hs#L322)) — it rejects `elapsed = gap`, so it certifies only at `slot(RB′) − s ≥ gap + 1`. The EB point carries the announcing RB's own slot (`forgeLeiosEb fbCurrentSlotNo`), so the two comparisons are over the same quantity and the difference is real: **the node is one slot stricter than the specification.** Nothing in the source records whether that is deliberate conservatism or an off-by-one; the neighbouring comment is an unrelated `TODO` about the closure-presence guard.

It also moves the stranding arithmetic. Any RB elected while the pending EB cannot yet be certified becomes the announcer's successor and strands it, so the at-risk window is the intervening slots:

| | at-risk slots | P(stranded) at f = 0.05 |
|---|---|---|
| CIP-0164 rule (`≥ gap`) | gap − 1 = 13 | 1 − 0.95¹³ ≈ **48.7%** |
| Implementation (`> gap`) | gap = 14 | 1 − 0.95¹⁴ ≈ **51.2%** |

Worth flagging for anyone reading both literatures: the CIP quotes `0.95¹³ ≈ 51%` for the probability that no intervening RB is produced — hence that the EB **survives under this model** — while our own notes quote ≈51% as the probability it is **skipped**. The two numbers are near-identical and mean opposite things. Our `1 − (1−f)^gap` formula happens to be exactly right for the deployed code, because the implementation's extra slot widens the window to `gap`.

### 7.2 Two CIP vote conditions are absent; one is enforced incidentally outside voting

[CIP-0164 step 3](https://github.com/cardano-foundation/CIPs/blob/d07a30bca36a28535afa151915bb4900b2116d3a/CIP-0164/README.md#specification) lists six conditions under which a committee member votes. Against `runLeiosVoting`/`goVote` at this snapshot:

| CIP vote condition | Implementation |
|---|---|
| 1. The RB header arrived within L_hdr | **Not enforced as a voting condition.** The delay passed into `processAnnouncementCentrally` supports body/closure age telemetry. Separately, [`announcementValidity`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoLogic.hs#L1662-L1723) uses announcement age for coarse network policy: after 5 minutes do not relay; after 10 minutes reject as too old. Neither guard compares arrival with L_hdr. |
| 2. No equivocating RB header seen for the slot | **Not enforced at vote time.** `PeerState`/`ElState` detect a second announcement and disconnect the peer, and `lHdrWait` exists precisely as the observation window ("we want to observe the second announcement (and drop the vote)"), but `AnnouncementEquivocation` is consumed only by `announcementTraceFields` for tracing. `goVote` never consults it, and `LeiosNotVotedReason` has no equivocation constructor. |
| 3. Validation finished before 3·L_hdr + L_vote | **Enforced**, from the 3 s / 4 s stubs; checked twice (before opening a forker, and again after closure validation). |
| 4. The EB is the one announced by the voter's chain tip | **Enforced** (`tipAnnouncerFor`). |
| 5. The EB's txs are a valid extension of the announcing RB | **Enforced** (`validateEbClosure`). |
| 6. The EB contains at least one transaction | **Not a vote rule.** Enforced incidentally at ingest: `leiosDbInsertEbBody` calls `error "empty EB body (programmer error)"` in both backends. An empty peer EB passes `processLeiosBlock`'s size/hash/duplicate checks (its hash and 1-byte size are computable by the sender), so it reaches that call — which runs on the per-peer LeiosFetch thread (`nextLeiosFetchClientCommand`, "on the main peer thread"), so the effect is to drop that peer, the same mechanism the deliberate `invalidReply` rejections use. The rule is honored, but by a path labeled as unreachable. |

A fourth gap sits outside the CIP's list: **received votes face no timing check at all.** `LeiosVoteState.addVote` validates dedup, seat, key, and signature, and `LeiosVote` carries only `(announcingRbHash, voterId, voteSignature)` — no slot and no timestamp — so a deadline check is not expressible at ingest without a chain lookup. The voting window is therefore an honest-node self-restraint, not a validated rule, and a tally can in principle cross τ from votes that arrive long after the window shut.

## Sources

Source read at `ouroboros-consensus @ b56977b`, `cardano-ledger @ 1587f21`, `cardano-base @ fbfb3f0` (all permalinked inline; ledger and base branch tips verified identical to the node's `cabal.project` pins on 2026-09-17) and [CIP-0164 @ `d07a30b`](https://github.com/cardano-foundation/CIPs/blob/d07a30bca36a28535afa151915bb4900b2116d3a/CIP-0164/README.md). Musashi files fetched 2026-09-17: [`config.json`](https://book.play.dev.cardano.org/environments-pre/leios/config.json), SHA-256 `a5caf918d9b8ca4783edb44e56da5f7bd46d218ea50266a9b6aac1c35bd3800c`; [`dijkstra-genesis.json`](https://book.play.dev.cardano.org/environments-pre/leios/dijkstra-genesis.json), SHA-256 `e3a0f8edd086e0c1fccc9fa04b58fa76b8f735ce1214f854072078f7c823e8be` and configuration genesis hash `aa1238f505479a9b104d2cc001b4bf951062cd527200bea9a1857bdd0dc41085`; [`shelley-genesis.json`](https://book.play.dev.cardano.org/environments-pre/leios/shelley-genesis.json), SHA-256 `da8508afc546a0b1824d93629a7a5fc8c0898d85095c2cf1b25730eb99d5a151` and configuration genesis hash `1944510a4fd91415444285231058f6f6ff0f6f3ff3d0356c76c00c5a77f29567`.
