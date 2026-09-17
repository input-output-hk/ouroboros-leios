# Mempool-Alignment Quantities: kleioscan ↔ Node Telemetry ↔ Models

**Created:** 2026-09-16
**Status:** Draft for review.
**Provenance:** 🤖 (LLM-generated, pending human review)
**Companions:** [Mempool/TxCache map](./leios-node-mempool-txcache.md) (the code behind the telemetry) · [Simulation/model catalog, mempool table](./leios-simulation-model-catalog.md#mempool-and-transaction-cache-representations) (the models)

Mempool alignment is measured today at three layers that use different words for overlapping quantities. This note fixes the correspondences so that a number from one layer can be checked against another — the prerequisite for the reconciliation experiment proposed in the catalog. Layer definitions:

- **Chain-derived** (kleioscan `musashi` fragmentation panel, Kostas Dermentzis): computed from on-chain EB/RB contents only — what any observer can measure, with no node cooperation.
- **Node-local telemetry** (the `TraceLeiosBodyHits` funnel and `FetchArrivalBytes`, emitted at EB-body arrival; Grafana `cardano-leios-diffusion`): what one instrumented node sees.
- **Model quantities**: ΔQ's π₁, smol world's `overlapBytes`, the hypergeometric overlap, `linleios`'s p_eb, sim-rs's lifecycle metrics.

## 1. The master table

| Quantity | Layer | Definition (verified source) | Corresponds to |
|---|---|---|---|
| `mempoolHits / txsInEb` | node | Fraction of an arriving EB's referenced txs found in the local mempool (`getLeiosTxIndex` pull in `processLeiosBlock`) | ≈ **pairwise mempool overlap with the producer** — the hypergeometric `E[s]/m = 1/ξ` (catalog dive 10), since an honest EB is a snapshot of the producer's mempool; ≈ smol world's `overlapBytes closure (mpSet mp)` (count- vs byte-weighted, § 2.1) |
| `missedBoth / txsInEb` | node | Fraction in **neither** mempool nor TxCache — the actual network-fetch set | ≈ **ΔQ's π₁** as *defined* ("not already in the voter's local mempool… must fetch it over the network", `pi1_derivation.md` § 1) — but see § 2.2: π₁'s *measurement* used a Praos proxy; ≈ `1 − overlapBytes closure (possession mp)` in smol world (possession = mempool ∪ EB-cache mirrors mempool ∪ TxCache) |
| combined hit rate `(txsInEb − missedBoth)/txsInEb` | node | The dashboard's headline number (`TraceLeiosBodyHits` doc) | ≈ **π₂ = 1 − π₁**; the quantity whose byte-weighted form drives ΔQ fetch time and smol world's write-back |
| funnel `tracked / txsInEb` | node | Share of the EB's txs the **TxCache** already tracked at body insert (`ibsTracked`) | No direct model analog — bounded by the 128-announcement window; the models' caches are age/slot-windowed instead. Expected ≪ 1 ("most… are already in the node's mempool; the cache path only ever accounts for the remainder") |
| funnel `acquired`, `validated` | node | Of tracked txs: already fetched; already applied (by Mempool or LeiosVoting) | `validated/txsInEb` ≈ the share licensing `reapplyTx` in `validateEbClosure` — ΔQ's reapply-vs-apply mixture weight; the "differ by about an order of magnitude" note (validation-share vs never-seen) is the panel's own calibration hint |
| `FetchArrivalBytes` (good/extra/evicted/invalid) | node | Byte classification of arrivals by `TxArrivalPrior` | `extra` = redundant deliveries ≈ duplicate-fetch overhead models ignore; `evicted` = arrivals past the cache window — a residence-time diagnostic (catalog mempool-table column 2) |
| **Tx duplication** ("overlap") | chain | Txs endorsed by more than one EB | sim-rs's **TX redundancy** metric (2025 experiment decks); in smol world, exactly the **promotion walk / ratchet** re-proposing an uncertified EB's txs — high duplication under low skip is *healthy ratcheting*, under high skip it is churn |
| **EB skip rate** | chain | Fraction of announced EBs never certified | 1 − (`linleios` EB efficiency); ΔQ's 1 − P_certified. **Baseline is spacing, not fragmentation**: P_interrupted = 1 − (1−f)^(at-risk slots), f = 0.05. The exponent is the *intervening* slot count, which differs by layer: the implementation's guard (`elapsed ≤ minGap ⇒ Nothing`) puts `gap` slots at risk (≈ 51.2% at gap 14), while CIP-0164's `≥ gap` rule puts `gap − 1` at risk (≈ 48.7%) — see [the parameter note](./leios-node-protocol-parameters.md) § 7.1. Beware that the CIP quotes ≈ 51% as the *survival* probability, not the skip probability. The fragmentation signal is the **excess**: skip − baseline ≈ baseline-weighted (1 − P_quorum), and P_quorum is where π₁/diffusion enter |
| **Skipped-EB coverage** | chain | ❓ disputed in-thread ("no idea what this is saying") — plausibly: share of a skipped EB's txs that still reached the ledger later (via mempool → later EB/RB) | If so: the chain-visible measure of the **ratchet working** — smol world's head "thins but cannot evaporate"; complement of the mempool-sim's captured-tx loss. Needs Kostas's definition ❓ |
| **Potential loss** | chain | ❓ disputed ("we don't lose transactions, do we?") — plausibly txs of skipped EBs not yet re-included | Under honest churn should → 0 as coverage completes (txs return via mempool); persistent nonzero would indicate TTL expiry or genuine fragmentation — smol world's TTL-churn regime |

## 2. Caveats that break naive equalities

1. **Counts vs bytes.** The funnel and kleioscan count *transactions*; ΔQ's fetch-size term and smol world's `overlapBytes` weight by *bytes*. Under mainnet's heavy-tailed tx sizes these differ materially; any reconciliation must compute both (the node's `FetchArrivalBytes` already gives the byte side of arrivals).
2. **π₁'s measurement is a Praos proxy.** `pi1_derivation.md` estimates π₁ ≈ 0.06 from the 2025 three-region instrumentation as **P(tx not seen in local mempool before appearing in a Praos block)** — a *block-arrival* proxy predating the Leios testnet. The funnel's `mempoolHits` is the direct EB-time measurement of the same idea; the first real test of π₁ is simply comparing them. (Also: the derivation covers 3 vantage points, BAU window, business-as-usual load.)
3. **Vantage differs.** Node telemetry is one relay's view; kleioscan aggregates the chain, i.e. the *producers'* mempools; the hypergeometric model is pairwise-symmetric. `mempoolHits/txsInEb` measures receiver-vs-producer overlap, which equals pairwise overlap only under the model's uniform-diffusion assumption — the deviation is itself informative (the measurement corpus already found small-world concentration).
4. **The TxCache window is short and count-based** (128 announcements), unlike every model cache (slot/age windows). `tracked` therefore under-approximates what the CIP's set-S would track; `fetchArrivalEvicted` bytes flag when this bites.
5. **Skip-rate baselines shift with parameters.** The kleioscan thread (2026-08-26) computed with gap 10, but musashi's genesis fetched 2026-09-17 yields gap 14 (= the CIP cadence) — the gap in force must be recomputed from the current week's `dijkstra-genesis.json` before baselining (❓🤖; see [the parameter note](./leios-node-protocol-parameters.md) § 5). Comparing skip rates across periods requires re-baselining (Nagel's exact point in the wording thread).
6. **Duplicate EB references are node-rejected but chain-legal across EBs** — duplication is per-tx-across-EBs, never within one EB (`processLeiosBlock` rejects those).

## 3. The reconciliation experiment, now concrete

One dataset, four checks (this instantiates catalog gap #2's mempool half):

1. **Telemetry vs π₁**: collect `TraceLeiosBodyHits` from testnet nodes (or a Piranha observer); compare `1 − combined hit rate` (count- and byte-weighted) against π₁ ≈ 0.06 and against a re-run of the Praos proxy on the same nodes. Divergence measures the proxy error, not an inconsistency.
2. **Telemetry vs hypergeometric**: from mempool sizes (m) and offered load (k) on the same nodes, predict overlap `1/ξ`; compare to `mempoolHits/txsInEb`. Deviation quantifies the non-uniform-diffusion (small-world) correction.
3. **Chain vs analytic skip**: kleioscan skip rate vs 1 − P_certified from ΔQ/`linleios` with the *measured* π₁ plugged in (and the gap in force that week — 10 per the Aug thread, 14 per the 2026-09-17 genesis ❓🤖) — closing the measured-alignment → certification-probability pipeline end to end.
4. **Ratchet visibility**: correlate tx duplication and (once defined) skipped-EB coverage with skip episodes; smol world predicts duplication spikes exactly when EBs skip and the head re-proposes.

Instrumentation exists for all four (map § 2.3, § 6; catalog dive 12); the only new artifact needed is the collection/analysis script.

## 4. Open items

- Get **Kostas Dermentzis's definitions** for skipped-EB coverage and potential loss (both marked disputed above) — without them rows 9–10 of the table stay conjectural. *Deferred by decision 2026-09-16: hold off on asking until we know more.*
- Confirm whether testnet nodes export `leios_logmetrics_*` (catalog dive 12 follow-up #1).
- The byte-weighted funnel exists only as `FetchArrivalBytes` classes, not per-EB; a small telemetry addition (byte-weighted `TraceLeiosBodyHits`) would let check 1 run in both weightings without post-processing.

## Sources

- [`pi1_derivation.md`](https://github.com/input-output-hk/ouroboros-leios/blob/11be71594ef1d71db7917ced11ccd54795335c07/analysis/deltaq/improved-leios/pi1_derivation.md) (§ 1 definition and § 2 data source read in full)
- `LeiosTxCache.API`/`LeiosDemoLogic.processLeiosBlock` and the dashboard panel documentation — permalinked in the [mempool/TxCache map](./leios-node-mempool-txcache.md)
- [kleioscan wording thread — #team-leios, 2026-08-26 (internal)](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1787731043191039); [kleioscan musashi panel](https://kleioscan.com/#/musashi/leios)
- Catalog dives [5](./leios-simulation-model-catalog/05-smol-world.md), [8](./leios-simulation-model-catalog/08-deltaq-models.md), [9](./leios-simulation-model-catalog/09-markov-linleios.md), [10](./leios-simulation-model-catalog/10-postcip-mempool-models.md), [12](./leios-simulation-model-catalog/12-execution-environments.md)
