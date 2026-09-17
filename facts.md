# Key Facts — Ouroboros Leios Exploration

Verified facts established through this effort. Updated as new findings are confirmed. Cross-reference with [AGENTS.md](./AGENTS.md) for conventions.

**Rules for this file.** One fact per bullet. Every fact carries (a) its date of confirmation, (b) its source — a URL, an upstream commit, or a repo-relative path to the experiment that established it — and (c) the layer it is about: paper, formal specification, simulator, implementation, or deployed network. A quantitative fact also carries the parameterization it holds at. A fact that is superseded is struck through rather than deleted, with the replacement immediately below it.

> [!NOTE]
>
> Empty as of 2026-09-16. This effort is in scope discovery and has confirmed nothing yet. Do not populate this file with claims carried over from upstream documents without verifying them here first — a fact in this file is one *we* checked.

---

## Upstream Artifacts

- **Leios simulator/model repositories** (verified via GitHub API, 2026-09-16; layer: repository metadata and READMEs at each default-branch HEAD):
  - `input-output-hk/leios-tools` — the actively maintained Rust simulator (`sim-rs`), the `net-rs` N2N stack, `shared-rs`; extracted from `ouroboros-leios` with history.
  - `input-output-hk/ouroboros-leios` — Haskell simulation (outdated for Leios per its own README), DeltaQ tooling, analysis notebooks, post-CIP models, demos, Antithesis stacks, trace verifier.
  - `input-output-hk/ouroboros-leios-formal-spec` — Agda spec of Linear Leios with safety/liveness proofs and certified trace verifier.
  - `input-output-hk/leios-peernet` — Spyros Voulgaris's Java/PeerNet block-diffusion simulator; **private** repository (accessible to this effort's token); dormant since 2025-02-21.
  - `input-output-hk/leios-adversarial-tools` — **private**; holds the Piranha node/cluster (`net-node`, `net-cluster`, `net-ui`, `behaviours/`); inaccessible to this effort's token as of 2026-09-16.
  - `IntersectMBO/ouroboros-network` PR #5424 ("smol world") — Marcin Wójtowicz's discrete-event simulator with loss+RTO transport; open branch `mw/hello-smol-world`.
  - `ouroboros-leios` PR #880 — Nick Frisby's Mininet LeiosFetch test bed; open branch `nfrisby/april2026-checkpoint`.
- **No pre-existing summary document of Leios simulators** existed before 2026-09-16 (source: Sebastian Nagel, [#team-leios thread](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1789559134074159?thread_ts=1789558993.289409&cid=C074AHSKJF7); layer: project record). The catalog at [artifacts/leios-simulation-model-catalog.md](./artifacts/leios-simulation-model-catalog.md) now fills this gap.
- **Spyros Voulgaris (AUEB) network-modeling deliverables in hand** are two PDF reports — TECHREP1 (network overlays) and TECHREP3 (time-budget analysis) — shared in #team-leios on 2026-05-15 (Slack files `F0B3YR7BAR3`, `F0B45RA27RA`); the simulator code producing them was not found on GitHub/Slack/Drive as of 2026-09-16 (layer: document search).

- **Leios simulator/model deep-dive facts** (verified by source reading, 2026-09-16; commit pins in the [dossiers](./artifacts/leios-simulation-model-catalog/)):
  - sim-rs's default transport is a TCP congestion-window model ported from the Haskell `ModelTCP.hs` (`tcp-congestion-control: true` shipped default); no loss model is active in any shipped config (layer: sim-rs source @ leios-tools `7b08aaa`).
  - The `cleanup-policies` config key is honored only by the Haskell simulator (pipeline-keyed pruning threads); it is a no-op in sim-rs (layer: source, both simulators).
  - The AUEB TECHREP1 ("Efficient Network Overlays…") is dated February 2021, authored by Kolyvas & Voulgaris, and used the **PeerNet** simulator; the 2026-05-15 Slack posting resurfaced Praos-era reports (layer: report PDFs).
  - The Agda formal spec models the mempool as an abstract environment-fed `List Tx`; the trace verifier cannot adjudicate mempool-management behavior (layer: formal spec @ HEAD 2026-09-15).
  - The prototype node exports mempool-alignment telemetry: LeiosTxCache funnel (txsInEb ≥ tracked ≥ acquired ≥ validated) and mempool-hit metrics, wired into the proto-devnet `cardano-leios-diffusion` dashboard (layer: dashboard JSON + metric names, ouroboros-leios @ `11be715`).
  - The ΔQ Linear Leios analyses (Hauser 2026) include a mempool/TxCache two-state Markov model; the measured miss rate is π₁ ≈ 0.06 (layer: reports in-repo). Kuhn's Rust `delta_q` tool is discontinued (Feb 2025; dead end — B. Bush, 2026-09-16).
  - "smol world" (ouroboros-network PR #5424) is two commits (2026-08-28/31), a draft with no review activity; its design docs and experiment driver are not on the branch (layer: branch @ `8d169f7`).

- **Leios production staging branches** (verified via GitHub API + `cardano-node@leios-prototype` `cabal.project`, 2026-09-16; layer: repository branches and build pins). The convention is a **`leios-prototype`** branch per repo under `IntersectMBO`, with the node's cabal.project pinning exactly the dependency branch HEADs: cardano-node `7e33674` (2026-09-16), ouroboros-consensus `b56977b` (2026-09-15), ouroboros-network `4b3ab76` (2026-06-30), cardano-ledger `1587f21` (2026-09-06), cardano-api `e32d8c0` (2026-09-07), cardano-cli `517ffe9` (2026-09-07), cardano-base `fbfb3f0` (2026-09-03). cardano-db-sync deviates: active branch `leios-w36` (2026-09-09), plus `leios-prototype-remake` (stale, May 2026). No leios branches in typed-protocols or plutus. Deployment config: `input-output-hk/cardano-playground` branch `leios-red-team` (2026-08-24) and the published `environments-pre/leios` ("musashi") config on book.play.dev.cardano.org. `tx-firehose` is a `bench/` package inside cardano-node@leios-prototype, not a separate repo. The "wNN" weekly names (w32–w36) appear in db-sync branches and deployment coordination, not as cardano-node tags (only `leios-202510-demo`, `leios-prototype-demo-202511` exist).

- **Lifecycle-audit implementation facts** (verified by source reading during the 2026-09-17 accuracy review of the [transaction-lifecycle diagram](./artifacts/leios-node-tx-lifecycle.svg); layer: implementation @ ouroboros-consensus `b56977b`):
  - The **minimum certification gap is a minimum wait** (`currentSlot − announcementSlot ≤ minGap ⇒ Nothing` in `decideLeiosCertify`), and certification must occur in the announcing RB's direct successor — so a successor RB elected *inside* the gap strands the pending EB. Enforcement is **forge-side only**: follower validation carries `FIXME: Check the min certification gap` (`Forker.hs:618`), with no other validation-side use of `getMinCertificationGap`.
  - A **CertRB's wire body carries the Leios certificate and no regular transactions** (`mkBody`: tx sequence `Seq.empty`, certificate via `leiosCertBlockBodyL`); "empty body" comments are shorthand.
  - **Missing-closure CertRB parking is implemented**: `ignoreUnacquiredCertRB`/`...Suc` transiently hide a CertRB and its successors from chain-selection candidates until the closure arrives; `leiosAcquiredEbsRunner` + `chainSelReprocessLeiosEb` reprocess on `AcquiredEbTxs`.
  - **Fetch priority is two-tiered** (`fetchPriorityTiers`): EBs within L = 3·L_hdr + L_vote + L_diff of the current slot are requested oldest-first, staler EBs then freshest-first; slot unknown (syncing) ⇒ one oldest-first tier.
  - **Vote timing is wall-clock-stubbed**: window opens at announced-slot onset + `lHdrWait = 3 s`, deadline + `lVoteWindow = 4 s` later (both TODO-marked to become ledger protocol parameters); the check runs immediately if the closure completes after the window opens.
  - The ≤ 2-announcements-per-election limit is enforced per upstream peer by `PeerState`/`ElState` (third or repeat ⇒ disconnect); `ElBimap` is the downstream relay gate for equivocation evidence.
  - **Offer gating is two-level**: LeiosDb emits `AcquiredEb` on body insert (→ `MsgLeiosBlockOffer`) and `AcquiredEbTxs` only on closure completion (→ `MsgLeiosBlockTxsOffer`); a completed SQLite row stores `missingTxCount = −1` as the notified sentinel.
  - Mempool `Sync` is bounded by a **converging off-lock catch-up loop** (`syncDeltaCap = 256` under-lock target, `syncMaxIters = 8` safety valve); `reapplyUntilTimeout` bounds *snapshot* computation, not `Sync`. Default mempool capacity is 2× the ordinary block measure, byte-overridable; the CIP's ≥ 2 × (RB+EB) formula awaits `ouroboros-consensus#2280`.
  - Demo fetch-job caps: `maxJobBytesSize = 64 KiB`, `maxJobTxCount = 20000`. LeiosDb EB statuses are not one linear chain: certified 0→1→2, cleanup 0→3 and 2→3, and promotion rescues 3→1.
  - Two source comments are **stale at this very commit**: ChainSync announcement folding *is* wired (`leiosMsgRollForwardCallback` → `processAnnouncementCentrally ReceivedViaChainSync`), and "proper EB announcements not implemented" reduces to body-size validation still trusting request/offer-carried state.

## Protocol Parameters

*(To be established: the parameter set, its symbols, its defaults, and where those defaults are defined upstream.)*

## Baselines

*(To be established: the Cardano Praos baseline figures that Leios claims are measured against, with their sources.)*

## Environment and Toolchain

*(To be established: what builds and runs locally, at which versions, and what it took. See the per-experiment `lessons-learned.md` files for the detail.)*
