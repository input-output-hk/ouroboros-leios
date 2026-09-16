# Deep Dive 5: "smol world" (ouroboros-network PR #5424)

**Created:** 2026-09-16
**Status:** Draft for review.
**Provenance:** 🤖 (LLM-generated from source-code reading, pending human review)
**Read at:** [`IntersectMBO/ouroboros-network`](https://github.com/IntersectMBO/ouroboros-network) branch `mw/hello-smol-world`, HEAD `8d169f7` ("TCP engine fixes", 2026-08-31); PR [#5424](https://github.com/IntersectMBO/ouroboros-network/pull/5424) (draft).
**Parent entry:** [catalog § smol world](../leios-simulation-model-catalog.md#5-smol-world-ouroboros-network-pr-5424)

Marcin Wójtowicz's compact, self-contained discrete-event model of **Linear Leios EB diffusion under realistic transport and egress contention** — and, in its Phase-2 form, of **mempool alignment**: whether EB certification acts as a ratchet that converges nodes' mempools. Self-described (module header) as "the model the ΔQ report could not supply." At 1,360 lines of dependency-light Haskell (base/containers/vector/random only — no io-sim, no typed protocols), it is the smallest artifact in the catalog with the deepest transport fidelity.

---

## 1. Provenance and status

The branch is **very recent, not long-lived**: exactly two commits atop master-of-2026-08-24 — `075cc92` "hello smol-world" (2026-08-28, the whole package in one commit) and `8d169f7` "TCP engine fixes" (2026-08-31) — then no pushes. The PR is a **draft** with zero review activity. But the code is clearly the tip of a larger private working corpus: comments cite `design.md`, `mechanics.md §9`, `mainnet_tx_ttl.md`, an "improved-ΔQ report" (Praos Table 1), a reference "TCP estimator" implementation, reviewer feedback rounds ("rev-16 §4.2", "rev-17 §4.4"), decision tags (D2, D12, D20), experiment phases (Phase 2, Phase 4), and CLI flags (`--diverge`, `--ttl-mixture`, `calibrate`, `rounds`) — **none of which are on the branch**. There is no executable, driver, test, or doc in the package: library only. The experiment harness and design documents live in Marcin W.'s private environment. The Sept-2026 Wójtowicz/Knutsson egress-stability presentation almost certainly ran on this corpus ❓🤖 (inference from timing/authorship, as before).

## 2. Architecture

Four layers, all deterministic (every stochastic input is seeded; randomness via context hashing and `StdGen`):

1. **Topology** (`Topology.hs`, `Types.hs`, `Stake.hs`, `Metrics.hs`): a *stratified small-world generator* — nodes in clusters ⊂ regions ⊂ continents (defaults: 750 nodes, 30 clusters, 6 regions, 3 continents, valency 20 ≈ real Cardano), a configured fraction of links kept local (0.6) and, of the rest, a region-kept fraction; log-normal stake (σ = 1.2) as the mainnet-skew stand-in; optional hub bias (target selection ∝ stake^b) and a static **"churn relaxation"** — rewiring rounds approximating Cardano's peer-churn steady state, with a Pearson stake↔inbound-degree metric to sanity-check the induced bias. RTTs come in **three tiers** (intra-cluster 10–50 ms, intra-continent 50–125, inter-continent 125–250), justified by "the improved-ΔQ report's Praos Table 1," sampled per cluster-pair with per-edge fuzz.
2. **Transport** (`TCP.hs`): per-flow **CUBIC congestion control with full RTO semantics**, "a faithful Haskell port of the TCP estimator's `simulate_one_run`": slow start → CUBIC congestion avoidance (C = 0.4, β = 0.3, fast convergence with correct wMax bookkeeping — the Aug-31 commit fixed three subtle CUBIC corners against Linux `bictcp` behavior), fast-retransmit vs. RTO decided by per-window burst counts, prefix crediting on timeout, RTO = clamp(RTT + 4·RTTVAR, 200 ms, 120 s), BDP-derived window cap, idle reset, and a **warm-idle lever** (a configurable fraction of nodes modeled with `tcp_slow_start_after_idle=0`). Optional RTT jitter, spurious-fast-retransmit reordering, and SACK on/off.
3. **Loss**: two independent sources — **emergent congestion loss**, computed per round from each serving node's egress fair-share (when a flow's window rate exceeds its share, the excess overflows; heavy oversubscription → RTO, mild → cut), and **baseline Gilbert–Elliott** good/bad two-state chains, parameterized *per RTT tier*. No other artifact in the catalog models loss at all in its default configuration.
4. **Diffusion DES** (`Diffusion.hs`): time advances in fixed bins (heterogeneous RTTs preclude a global RTT round); each flow's cwnd updates on its own RTT boundaries. The per-hop exchange is Cardano-faithful and pull-based: announce push (one-way delay) → downstream **pulls the EB body** (tx references, 32 B each, ≤ 512 kB cap) from the *first* announcer (round-trip + transfer) → **pulls the closure** (all referenced txs, π₁ = 1) from the same peer. A node serves downstream once it has *secured* body+closure; it votes only after *applying* the closure (CPU cost α + β·n_txs — deliberately the marginal slope, not the mean).

## 3. Leios semantics modeled

CIP-0164 quantities appear directly: 32-byte tx references, 512 kB EB body cap, 0.75 stake quorum, a **deterministic truncated committee** with cumulative stake-coverage parameter σ_c (the wFA^LS shape), the certification-cadence window 3·L_hdr + L_vote + L_diff = 14 slots, Praos active-slot coefficient, and a voter deadline. `DiffResult` separates **network-only quorum time** (75% stake has secured) from **voted quorum time** (secured + applied) — a clean decomposition none of the bigger simulators expose as directly. `simulateBattle` models **two rival EBs splitting the committee** (each voter commits to whichever it can validate first), reporting committed-and-voted weight per side and whether either reaches quorum — i.e., whether the slot is wasted; the header notes it is optimistic on reach (ignores routing commitment) but captures the dominant committee-split effect.

## 4. Mempool and transaction caches

**The catalog's only mempool-*alignment* model, and directly on our study topic.** `Mempool.hs` models per-node pending-transaction state carried across rounds of a multi-round ("Phase 2") experiment, over a shared tx-id universe where **id = global submission order = age**:

- **The mempool proper** (`mpSet` + byte counter): hard byte cap with **blocking admission** — a full mempool *refuses* new txs and the pull stalls upstream; **no drop, no eviction** ("the reviewer's rev-16 §4.2 semantics"). This is the opposite discipline from sim-rs's backlogs-and-drops and from the real node's bounded-queue behavior — a deliberate modeling choice worth interrogating when we compare.
- **The EB-cache** (`mpCache`): byte-capped store where **fetched EB closures are planted** ("the byte half of write-back") — txs a node's churning mempool never held but which it now possesses because it fetched a closure. Eviction is coarse **LRU-by-id** (oldest first). Cache cap 0 disables it (the pre-Phase-2 baseline).
- **Possession = mempool ∪ EB-cache** — what a node can *vote* on, and the pool from which the **promotion walk** (`promoteHead`) reconstructs the attested closure as a forge-order head.
- **Forge order** (`oldestClosure`): promoted head first (in EB order, possession-backed), then mempool tail oldest-first, up to a byte budget. Empty head ⇒ pure age order (the promotion-free baseline). The module header calls the split "load-bearing": planting (bytes) and promotion (ordering) are two halves of one mechanism, and "the alignment ratchet needs both."
- **Drainage**: `includeClosure` — a certified closure's txs leave mempool, cache, and head (plus the Praos-floor inline-RB drain of oldest txs); **TTL expiry** — either a single age threshold (`expireBelow`) or, notably, a **measured mainnet TTL mixture** (`expireWhere`, per `mainnet_tx_ttl.md`: never-expiring / hours / 180–360 s classes), under which "the head thins but cannot evaporate."
- **Metrics**: `overlapBytes` — byte-weighted overlap of a closure against possession (vote-side) or mempool-only — i.e., a direct quantitative definition of **mempool alignment**.

**Residence times:** mempool txs stay until on-chain inclusion or TTL expiry (never evicted by pressure — admission blocks instead); EB-cache entries until inclusion, TTL, or byte-pressure LRU eviction; there are no other caches (the diffusion layer models the EB payload as byte counts per flow, not stored objects).

## 5. Faithfulness, determinism, performance

- **Transport fidelity: highest of any simulator in the catalog** (CUBIC + RTO + fast-retransmit + SACK toggle + Gilbert–Elliott + emergent egress-contention loss). The Haskell `ols`/sim-rs `ModelTCP` lineage has slow-start only, no loss; leios-peernet has latency multiples.
- **Protocol breadth: deliberately narrow.** One EB (or two rivals) per run; no Praos chain dynamics, no vote *diffusion* (votes are counted at apply-time, not transported), no RB/certificate objects, no mini-protocol multiplexing, no attackers. Tx sizes uniform. The topology is synthetic (no pseudo-mainnet import).
- **Determinism**: fully seeded and pure; suitable for exact regression comparisons.
- **Performance**: trivially fast at its 750-node default ❓🤖 (not benchmarked in this pass; pure in-memory DES over IntMap/IntSet).

## 6. Assessment against the four catalog dimensions

- **Faithfulness.** Transport and egress contention: best in class. Leios logic: correct CIP-0164 timing/committee/quorum constants around a stylized single-EB pipeline. Mempool: a *hypothesis-shaped* model (blocking admission, write-back cache, promotion walk) built to study alignment, not to reproduce `cardano-node` — its assumptions are exactly what our study should test.
- **Status.** Draft PR, three weeks old, two commits, unreviewed; active private corpus behind it (driver, design docs, reviewer rounds).
- **Scope.** EB diffusion time-to-quorum, sibling-EB battles, and multi-round mempool alignment under TTL churn.
- **Performance.** Small and fast; single-machine, single EB per run.

## 7. Gaps and follow-up questions

1. **Recover the private corpus**: `design.md`, `mechanics.md`, `mainnet_tx_ttl.md`, the experiment driver behind `calibrate`/`rounds`/`--diverge`/`--ttl-mixture`, and the reviewer exchange (rev-16/17) — ask Marcin Wójtowicz. Without the driver, the library is not runnable as published.
2. **Which "TCP estimator" is the port's reference?** (Also the "improved-ΔQ report" for the RTT tiers — likely Kuhn-lineage; worth pinning.)
3. **Cross-validation opportunity**: same topology + EB size in smol world vs. sim-rs (`tcp-envelope` with loss) vs. the Mininet test bed would calibrate all three loss stories — the catalog's gap #2 has its natural first experiment here.
4. **Mempool-model confrontation**: blocking admission vs. sim-rs's backlogs vs. `cardano-node`'s actual TxSubmission backpressure — decide which discipline our alignment study adopts, and justify it against the real node.
5. Whether the Sept-2026 stability analysis used exactly this code, and where its BitTorrent-grounded theory is written down.

## Sources

- Source read at `mw/hello-smol-world` @ `8d169f7`: `smol-world/src/SmallWorld/{Diffusion,TCP,Topology,Mempool,Metrics,Types,Stake,Rand}.hs`, `smol-world.cabal`; commit messages `075cc92`, `8d169f7`
- [PR #5424](https://github.com/IntersectMBO/ouroboros-network/pull/5424) (draft; body text quoted in the catalog entry)
- [Egress-stability high-five — #high-fives, 2026-09-07](https://input-output-rnd.slack.com/archives/C011H74QZNF/p1788799962666299) (internal)
- [Catalog entry 5 and its sources](../leios-simulation-model-catalog.md#5-smol-world-ouroboros-network-pr-5424)
