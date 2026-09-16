# Deep Dive 10: The Post-CIP Mempool and Constraint Models

**Created:** 2026-09-16
**Status:** Draft for review.
**Provenance:** 🤖 (LLM-generated from source and document reading, pending human review)
**Read at:** [`ouroboros-leios/post-cip/`](https://github.com/input-output-hk/ouroboros-leios/tree/main/post-cip) @ `11be715` — `mempool-model/`, `mempool-sim-web/` (+ `mempool-sim-viz/`, `clique-cover/`), `mempool-measurements/`, `constraint-model/`, `empirical-distributions/`. Primary authors Brian W. Bush (Nov 2025–Feb 2026) and Yves Hauser / William Wolff (continuing through Sept 2026).
**Parent entry:** [catalog § Mempool and constraint models](../leios-simulation-model-catalog.md#10-mempool-and-constraint-models-post-cip)

The mempool-dedicated family — a **theory / simulation / measurement triad** built to answer how synchronized real mempools are, how adversaries can poison them, and what EB processing costs at the CPU — plus the empirical-distribution corpus that calibrates everything else in the catalog. This is the row our upcoming mempool study extends.

## 1. `mempool-model/` — the mathematical model (Bush, through Feb 2026)

A closed-form model of mempool behavior on an idealized Ouroboros network, validated against the simulator (§ 2) and the measurements (§ 3):

- **Diffusion**: the topology idealized as a directed regular random graph (argued from the churn design's anti-scale-free tendency); hop-count recursion whose closed form is a logistic curve with mean log_k N — for mainnet (k = 20, N ≈ 25,000) ≈ 3.4–3.75 hops, 99% coverage in 4 hops, matching the anecdotal diameter 5–6. Typical λ = 4 hops.
- **Mempool overlap**: pairwise shared-tx count under random diffusion is **hypergeometric** in the "overburden" ξ = global txs / pool capacity; theory matches the simulator well once ξ ≥ 3/2. A generalization with node-private tx sets explains the observed ~81% commonality at ξ = 1 as ~10% of txs being "captured" by nearby block production (consistent with τ ≈ 2 s at f = 1/20).
- **Poisoned mempools** (front-running): an adversarial node replaces received txs with conflicting ones; under first-come-first-served conflict exclusion, the poisoned fraction ≈ 1 − (1 − p_adv)^(λ−1) — slope (λ−1)·p_adv for unbiased racing, slope 1·p_adv when the adversary forwards with delay. **Both slopes confirmed by the simulator** (N = 10,000, k = 20: predicted 2.074 and 1.0; `adversarial-scatter.svg`).
- **Rules of thumb from measurements**: regional mempools >90% synchronized in business-as-usual; synchronization drops as block utilization rises; ~90% of blocks contain only previously-mempooled txs below 85% utilization; tx-to-block delay matches the geometric active-slot distribution; and a topology surprise — 22% of txs arrive from a common 9% of remote peers, and ~half of txs travel >7,000 km — suggesting mainnet is **more small-world than the RRG ideal** (operators customize connectivity), which quietly supports smol world's topology philosophy (dive 5) over pure random graphs.

## 2. `mempool-sim-web/` — the mempool simulator (Bush; extended by Hauser/Wolff through Sept 2026)

A TypeScript discrete-event simulation (~1,700 lines; CLI + browser, with `mempool-sim-viz/` as a Vite/TS interactive front-end) of tx propagation with adversarial front-running — notable for a README that is **a model-card of simplifications**, stating for every mechanism what is optimistic vs realistic (a documentation standard worth adopting):

- **Network**: edge-swap-randomized ring lattice (≈ RRG), identical per-link latency/bandwidth, delay = latency + (80 + size)/bandwidth + negligible jitter; **no queuing or contention** (explicitly "optimistic under load"); optional coarse churn; adversaries rewire in.
- **Mempool mechanics**: 3-step offer/request/send gossip per tx (first-offer-wins, bidirectional announcement — both marked "matches real protocol"); **no validation delay** on admission; bitmap-based first-seen-wins conflict exclusion standing in for UTxO conflicts; greedy block fill; tx removal *globally instant* at production but per-node on diffusion.
- **Leios EB mode**: EBs emerge from **mempool overflow** (txs left after filling the RB), wire size 32 B × refs; certification is a **coin flip at the next RB** (`ebCertificationRate`, default 0.5) — certified RBs carry only the certificate and the EB's txs leave all mempools; uncertified EBs' txs stay available. EB-referenced txs a node lacks are fetched by a 2-step protocol with **omniscient peer selection** (global bitmap lookup, single-source, marked optimistic); fetched txs by default re-enter normal gossip (`--no-eb-tx-cache` isolates the cache question).
- **Experiments**: `experiment-praos`/`-praos-0ms`/`-leios`/`-0`/`-1` sweep adversary fractions (TSV outputs + notebooks); `clique-cover/` applies Leiden community detection to mempool snapshots (conflict/overlap structure analysis ❓🤖 — purpose inferred from code, no ReadMe).

**Caches and residence (standing section):** per-node mempool = a set with first-seen-wins conflict exclusion, drained by block production (global-instant at the producer, per-node on block arrival) and EB certification; no byte cap found ❓; no TTL. The EB-tx fetch path is the model's TxCache analog — its default behavior (fetched txs join the mempool and re-gossip) vs `--no-eb-tx-cache` is precisely the write-back question smol world and the CIP TxCache pose, in a third form.

## 3. `mempool-measurements/` — instrumented mainnet nodes (Bush, through Feb 2026)

Three instrumented `cardano-node`s (eu-central-1, us-east-1 ❓, ap-northeast-1) logging mempool arrivals and blocks; scripts + SQL + R notebooks. The source of: the >90% regional synchronization result, the utilization-dependence, the mempool-vs-block conditional probabilities, the tx-travel-distance distributions, and the shared-peer concentration table. **Downstream, this corpus is the empirical basis for the ΔQ model's mempool premise and π₁ ≈ 0.06** (dive 8) — making it the most load-bearing measurement set in the catalog for our topic. Caveat recorded in its own title: "empirical, *anecdotal*" — three vantage points, business-as-usual traffic only.

## 4. `constraint-model/` — EB processing as a scheduling problem (Bush; extended through Sept 2026)

An optimization model (Python: OR-tools/PuLP) of a voter's CPU work when an RB+EB arrives: the tx DAG rooted in prior ledger state, with three phases per tx — **verify** (parallel, on arrival), **apply** (parallel, needs ancestors arrived), **reapply** (sequential along the DAG) — scheduled onto n_CPU cores to minimize completion (vote) time, with arrival times external. Scenarios at 2/6/12 MB EBs; the 12 MB result: makespan ≈ 3.74 s at 21.9% CPU utilization — i.e., **the critical path, not CPU count, binds** (61% wallclock idle), with Perfetto trace visualizations. This is the CPU-side complement to the diffusion models: the α + β·n_txs apply cost in smol world and the batch distributions in ΔQ compress what this model resolves in full DAG detail.

## 5. `empirical-distributions/` — the calibration corpus

`block-edf.csv` / `tx-edf.csv`: binned **joint** empirical distributions of block and tx metrics for mainnet since epoch 350 (from cardano-db-sync + db-analyser), designed so Monte Carlo samplers and ΔQ models can consume them directly — and the improved-ΔQ report does exactly that (dive 8's timing re-derivation). Marginal-and-joint-preserving binning; sum out unwanted dimensions.

## 6. Assessment against the four catalog dimensions

- **Faithfulness.** The triad's strength is *mutual validation*: theory ↔ simulation (poisoning slopes, hypergeometric overlap) and theory ↔ mainnet measurement (synchronization, arrival distributions). The simulator's optimism is documented per-mechanism rather than hidden. The Leios EB mode is deliberately stylized (overflow-driven EBs, coin-flip certification) — good for mempool questions, not for certification timing (that's dives 5/8/9).
- **Status.** Measurements and math model settled (Feb 2026); simulator and constraint model actively extended (Hauser/Wolff, through Sept 2026).
- **Scope.** Mempool synchronization, fragmentation, poisoning/front-running, EB-fetch write-back, and EB CPU scheduling — plus the calibration corpus.
- **Performance.** All lightweight (TS sim at N = 10,000; solver minutes for 12 MB scenarios).

## 7. Follow-up questions

1. This row + dive 5 + dive 8 now give **three formulations of the same alignment question** (mechanistic ratchet, statistical π₁, hypergeometric overlap) with one measurement set behind them. The obvious next artifact is a short reconciliation note: do the hypergeometric overlap model, the π₁ Markov chain, and smol world's overlapBytes agree on today's mainnet parameters? Cheap, and it would harden all three.
2. The measurement corpus predates the Leios testnet — **re-running the three-node instrumentation against the testnet** (or via Piranha, dive 7) would give the first EB-era alignment data.
3. `clique-cover/` needs a ReadMe (purpose currently inferred from code).
4. The sim's "no queuing or contention" optimism is exactly what smol world's egress fair-share models — a targeted comparison at matched load would quantify how much that optimism matters for poisoning results.

## Sources

- Read at `ouroboros-leios@11be715`: [`post-cip/mempool-model/ReadMe.md`](https://github.com/input-output-hk/ouroboros-leios/blob/main/post-cip/mempool-model/ReadMe.md) (full), [`post-cip/mempool-sim-web/ReadMe.md`](https://github.com/input-output-hk/ouroboros-leios/blob/main/post-cip/mempool-sim-web/ReadMe.md) (full), `mempool-measurements/ReadMe.md`, `constraint-model/ReadMe.md` + `results-12MB.txt`, `empirical-distributions/ReadMe.md`, `clique-cover/main.py`, directory inventories; commit dates via GitHub API
- Cross-links: [Dive 5](./05-smol-world.md), [Dive 7](./07-piranha-net-rs.md), [Dive 8](./08-deltaq-models.md), [Dive 9](./09-markov-linleios.md)
- [Catalog entry 10](../leios-simulation-model-catalog.md#10-mempool-and-constraint-models-post-cip)
