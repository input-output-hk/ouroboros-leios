# Leios Cheatsheet

A living reference for the protocols, mechanisms, and terms this effort touches. Intended as an onboarding resource for a new team member on day one: every entry is objective, self-contained, and carries at least one source link.

**Maintenance rule** (from [AGENTS.md](../AGENTS.md) § Conventions): update this file whenever a Leios mechanism, block class, parameter, or comparable protocol is newly discussed or explored more deeply — including anything mentioned in an assessment, journal entry, or brainstorming document. Do not let the vocabulary of a document exist only inside that document.

**Entry format.** One H3 per term or protocol. Two to five sentences, written for a reader who has general distributed-systems vocabulary but no Leios background. State what it is, what problem it solves, and how it differs from the nearest neighbor. Close with at least one source link. Where a figure appears, give its layer (paper, formal specification, simulator, implementation, deployed network) and its parameterization.

> [!NOTE]
>
> First populated 2026-09-17 from the transaction-lifecycle and protocol-parameter work: the block classes, certification mechanics, the prototype's three stores, and the Leios parameter set with its deployed musashi values. The Ouroboros Family, Comparators, and Baselines sections remain stubs.

---

## Ouroboros Family

*(To be populated: Praos, Genesis, Peras, Leios — what each adds and what it assumes.)*

## Leios Mechanisms

Implementation statements below are pinned to the `leios-prototype` snapshot of 2026-09-16 (`ouroboros-consensus@b56977b`, `cardano-node@7e33674`); design statements cite [Cardano Improvement Proposal 164 (CIP-0164) @ `d07a30b`](https://github.com/cardano-foundation/CIPs/blob/d07a30bca36a28535afa151915bb4900b2116d3a/CIP-0164/README.md). See the [transaction-lifecycle diagram](./leios-node-tx-lifecycle.svg) for how these fit together.

### Ranking block (RB)

The ordinary Praos block, renamed in Leios to distinguish it from endorser blocks: it is still produced by verifiable random function (VRF) leader election and still carries the chain's ordering and security. In Linear Leios an RB additionally either announces a new endorser block (a TxRB) or certifies the previously announced one (a CertRB). Throughput scales because most transaction data moves in endorser blocks, while RBs stay small and diffuse on the unchanged Praos path. Source: [CIP-0164 § Specification](https://github.com/cardano-foundation/CIPs/blob/d07a30bca36a28535afa151915bb4900b2116d3a/CIP-0164/README.md#specification).

### Endorser block (EB)

A block of transaction *references* (32 bytes each, body up to 512 kB in the CIP design) produced alongside a TxRB by the same elected pool, holding the transactions that overflow the RB's own capacity. An EB contributes throughput only if a later RB certifies it; its transactions then enter the ledger as if they had been in that RB. The set of referenced transaction bytes is the EB's *closure*, which nodes assemble from their mempools and by fetching. Source: [CIP-0164 § Endorser blocks](https://github.com/cardano-foundation/CIPs/blob/d07a30bca36a28535afa151915bb4900b2116d3a/CIP-0164/README.md#specification); implementation: `forgeLeiosEb` ([`Shelley/Ledger/Forge.hs`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Ledger/Forge.hs)).

### EB announcement

A signed (EB hash, size) field inside the announcing RB's header, adjacent to the election proof — so every announcement has a slot, an author, and Praos authentication. Peers relay announcements urgently over LeiosNotify (best-effort per peer: the enqueue is dropped for a peer with no protocol credit) and also fold them in from ChainSync headers. An election admits at most two distinct announcements per upstream peer (equivocation evidence); a third or a repeat disconnects that peer. Implementation: [`LeiosDemoLogic/Announcements.hs`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoLogic/Announcements.hs) (pinned snapshot).

### TxRB versus CertRB

The two roles an RB can play. A TxRB carries its own transactions and announces a fresh EB from the mempool overflow. A CertRB carries **no regular transactions on the wire — its body holds the Leios certificate**; at validation time the certified EB's closure is spliced in from local storage and applied before the CertRB itself. A follower that lacks the closure parks the CertRB outside chain selection until the closure arrives, then reprocesses it. Implementation: `mkBody`/`partitionMempool` and the ChainDB cert-filter ([`ChainSel.hs`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Storage/ChainDB/Impl/ChainSel.hs), pinned snapshot); design: [CIP-0164 § Certification](https://github.com/cardano-foundation/CIPs/blob/d07a30bca36a28535afa151915bb4900b2116d3a/CIP-0164/README.md#specification).

### Votes, quorum, and certificates

A deterministic committee — the top `leiosCommitteeSize` pools by stake, using CIP-0164's stake-based truncation rather than the weighted Fait Accompli with Local Sortition (wFA^LS) scheme of earlier drafts — validates an announced EB's closure and votes within a bounded window; votes are tallied per announcing RB with each seat weighted by its pool's share of active stake, and a compact certificate (a ⌈N_c/8⌉-byte signer bitfield plus one aggregate Boneh–Lynn–Shacham (BLS) signature) is assembled the moment the tally reaches `leiosQuorumStakeThreshold` (τ). Both are Dijkstra governance parameters — musashi runs τ = 0.75 with 900 seats. Voting timing in the prototype is wall-clock-stubbed: the window opens 3 s after the announced slot's onset and closes 4 s later, even though the ledger already carries L_hdr/L_vote as parameters. CIP-0164 lists six conditions for casting a vote: the voter enforces the deadline, chain-tip announcement, and closure validity; it does not check timely header arrival or equivocation, while the nonempty-EB condition is enforced incidentally during database ingestion rather than by the voter. See the [timing-inequalities timeline](./leios-timing-inequalities.svg). Implementation: [`LeiosVoteState.hs`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosVoteState.hs), [`LeiosVoting.hs`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosVoting.hs); design: [CIP-0164 § Votes and certificates](https://github.com/cardano-foundation/CIPs/blob/d07a30bca36a28535afa151915bb4900b2116d3a/CIP-0164/README.md#specification).

### Minimum certification gap

The number of slots that must elapse after an EB's announcement before any RB may certify it — a *minimum wait* that gives the network time to fetch and validate the closure. Because certification must happen in the announcing RB's direct successor (the "linear" in Linear Leios), a successor RB elected *inside* the gap can never certify the pending EB and strands it; this — not "no certificate arriving in time" — is the dominant skip mechanism. At the pinned snapshot only the honest forge enforces the gap; follower block validation does not yet check it (an open `FIXME`), and the forge's guard rejects the CIP's own boundary slot, so it is one slot stricter than the specification ([details](./leios-node-protocol-parameters.md#71-the-certification-gap-is-off-by-one-slot)). The gap is computed as ⌈(3·L_hdr + L_vote + L_diff)/slotLength⌉ over the millisecond-valued Dijkstra parameters; musashi's genesis (fetched 2026-09-17) yields 14 slots — matching the CIP cadence — while an Aug-2026 Slack claim of 10 slots is unreconciled ❓. Implementation: `decideLeiosCertify` ([`Forge.hs`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/NodeKernel/Forge.hs#L288)).

### Stage lengths (L_hdr, L_vote, L_diff)

CIP-0164's timing budgets: L_hdr (announcement diffusion), L_vote (voting window), L_diff (body diffusion), giving the certification cadence 3·L_hdr + L_vote + L_diff (14 s at the CIP's 1/4/7 s values). They exist in the ledger as the millisecond-valued Dijkstra governance parameters `leiosAnnouncementPeriodLength` / `leiosVotePeriodLength` / `leiosDiffusionPeriodLength` (musashi: 1000/4000/7000 ms), but the prototype's voting and fetch code still hard-codes stand-ins (3 s / 4 s / a 10-slot window) with TODOs to read the ledger. L splits fetch priority: EBs younger than L are fetched oldest-first, staler ones freshest-first. Design: [CIP-0164](https://github.com/cardano-foundation/CIPs/blob/d07a30bca36a28535afa151915bb4900b2116d3a/CIP-0164/README.md); implementation constants: [`LeiosDemoTypes.hs`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoTypes.hs#L911).

### LeiosNotify and LeiosFetch

The two new node-to-node mini-protocols (numbers 18 and 19). LeiosNotify pushes announcements, EB-body offers, and votes to each peer through a credit-based queue; LeiosFetch pulls EB bodies (`MsgLeiosBlock`) and batches of missing transactions (`MsgLeiosBlockTxs`). A node offers a body as soon as it holds it, but offers the transaction closure only once complete — the CIP's serve-when-secured rule, realized as two distinct LeiosDb notifications. At the pinned snapshot both protocols live on the consensus branch as `LeiosDemoOnlyTestNotify.hs` / `LeiosDemoOnlyTestFetch.hs`. Implementation: [`NodeToNode.hs`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/Network/NodeToNode.hs); design: [CIP-0164 § Network](https://github.com/cardano-foundation/CIPs/blob/d07a30bca36a28535afa151915bb4900b2116d3a/CIP-0164/README.md#network).

### Mempool (Leios changes)

Still the Praos mempool — full `applyTx` admission, pull-based TxSubmission, default capacity twice the block measure (byte-overridable) — extended with a transaction-hash index (`getLeiosTxIndex`) so EB closures can be assembled from it, a no-cache snapshot path for the certifying forge (whose rebased ledger state invalidates the cached snapshot), and bounded revalidation: snapshot computation is time-capped (`reapplyUntilTimeout`) and post-adoption `Sync` converges off-lock to a small under-lock residual. The CIP's larger capacity formula (≥ 2 × (RB + EB measure)) is pending `ouroboros-consensus#2280`. Implementation: [`Ouroboros/Consensus/Mempool/`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Mempool); design: [CIP-0164 § Mempool design](https://github.com/cardano-foundation/CIPs/blob/d07a30bca36a28535afa151915bb4900b2116d3a/CIP-0164/README.md#mempool-design).

### LeiosTxCache

A bounded in-memory *index* (not a byte store) over the transactions referenced by recently announced EBs, recording per transaction whether its bytes are acquired and whether it has been validated — so voting can cheaply re-apply already-validated transactions and fetch logic can skip disk lookups. It is windowed to the 128 freshest announcements with reference-counted eviction, and its ordering contract (index evicts before the database prunes) prevents false hits. The production handle is a SipHash-based open-addressing hash table sized for ~2M entries, property-tested against a pure reference. Implementation: [`LeiosTxCache.hs`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosTxCache.hs) and submodules (pinned snapshot).

### LeiosDb

The on-disk (SQLite; in-memory for tests) store of EB points, bodies, and transaction bytes, split volatile/immutable with reference-counting garbage collection. Rows track closure completeness (`missingTxCount`: NULL = body absent, >0 = missing, 0 = just completed, −1 = completion notified) and a status byte (0 volatile, 1 certified-pinned, 2 copied-to-immutable, 3 GC-marked; certified rows go 0→1→2, cleanup marks 0→3 or 2→3, and a late promotion can rescue 3→1). Completion events drive both downstream offers and the reprocessing of parked CertRBs. Implementation: [`LeiosDemoDb/`](https://github.com/IntersectMBO/ouroboros-consensus/blob/b56977baae0740f563060a8a9171c78be865b357/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoDb) (pinned snapshot).

## Protocol Parameters

The Leios parameter set lives in the Dijkstra era's protocol parameters ([`PParams.hs`](https://github.com/IntersectMBO/cardano-ledger/blob/1587f21a7d1306dc590c2749a5c66232ef66aad0/eras/dijkstra/impl/src/Cardano/Ledger/Dijkstra/PParams.hs#L199), governable on-chain); deployed values are from musashi's `dijkstra-genesis.json` fetched 2026-09-17 (weekly redeploys — re-fetch before relying on them). Full analysis, including which of these are actually enforced and where: [protocol parameters and admission inequalities](./leios-node-protocol-parameters.md).

| Parameter | CIP symbol | Type | musashi (2026-09-17) | Read by |
|---|---|---|---|---|
| `leiosAnnouncementPeriodLength` | L_hdr | ms | 1,000 | `minCertificationGap` (forge); voting stub ignores it |
| `leiosVotePeriodLength` | L_vote | ms | 4,000 | `minCertificationGap`; voting stub ignores it |
| `leiosDiffusionPeriodLength` | L_diff | ms | 7,000 | `minCertificationGap` |
| `leiosCommitteeSize` | N_c | seats (Word16) | 900 | ledger SNAP rule (committee seating) |
| `leiosQuorumStakeThreshold` | τ | unit interval | 0.75 | vote tally; `verifyLeiosCert` |
| `maxEndorserBlockReferencesSize` | — | bytes | 100,000 (⇒ count ceiling 2,777; actual encoded size not guaranteed) | forge EB count proxy only |
| `maxEndorserBlockTxsSize` | — | bytes | 1,000,000 | forge EB measure only |
| `maxEndorserBlockExUnits` | — | execution units (ExUnits) | 310 M mem / 100 G steps | forge EB measure only |
| `maxRefScriptSizePerEndorserBlock` | — | bytes | 4,000,000 | forge EB measure only |

Non-parameter constants that behave like parameters: the consensus vote-window stubs (3 s / 4 s wall clock), the wire limit `maxMsgLeiosBlockBytesSize = 500 kB`, the fetch caps (12 MB closure; 64 KiB / 20,000-tx jobs; 10-slot priority window), and `maxKeyAge` (derived from the key-evolving signature (KES) setup: ⌈KES lifetime in epochs⌉ + 2; 374 epochs on musashi). Node config can override mempool capacity; musashi requests 2,000,000 B, which `computeMempoolCapacity` rounds to 2,072,576 B at its 90,112 B block-capacity byte coordinate.

## Comparators

*(To be populated: directed-acyclic-graph (DAG)-based mempool-and-consensus designs and other high-throughput chains, as they get assessed.)*
