# Deep Dive 8: The DeltaQ Models

**Created:** 2026-09-16
**Status:** Draft for review.
**Provenance:** 🤖 (LLM-generated from source and report reading, pending human review)
**Read at:** [`ouroboros-leios`](https://github.com/input-output-hk/ouroboros-leios) @ `11be715` — `delta_q/` (Rust tool), `analysis/deltaq/linear-leios/` (Haskell model + report), `analysis/deltaq/improved-leios/` (successor report + Python analysis), `analysis/deltaq/linear-leios-preliminaries.md`, `analysis/deltaq/tx-lifecycle.ipynb`.
**Parent entry:** [catalog § DeltaQ models](../leios-simulation-model-catalog.md#8-deltaq-models)

Three generations of ΔQ System Development (ΔQSD) work — algebraic composition of completion-time distributions — applied to Leios. The deep dive found the family is larger and more mempool-relevant than the catalog entry recorded: the Linear Leios models contain an explicit **mempool + TxCache Markov model** with an empirically calibrated miss rate, and the successor report is the **"improved-ΔQ report"** that smol world (dive 5) cites for its RTT tiers.

---

## 1. The tool: `delta_q/` (Roland Kuhn, 2024–25) — discontinued

A general-purpose Rust + web-UI implementation of ΔQSD, begun upstream as [`rkuhn/deltaq-rs`](https://github.com/rkuhn/deltaq-rs) (Sept 2024) and continued inside `ouroboros-leios/delta_q/`: CDF constructors and the standard operators (sequence `->-`, weighted choice `L<>R`, all `∀`, any `∃`), with two extensions beyond the published theory — **load analysis** (resource-usage step functions attached to outcomes via `WITH metric[...]`, propagated through the combinators with delay-convolution and load-factor scaling `->-×X`) and **bounded recursion** for repeating structures; also gossip-diffusion operators. Editable/persistable named expressions; compiled to WASM for the browser.

**Status: a dead end.** Development stopped in February 2025 — the final substantive commits are a *proposal* for a ΔQ `STRETCHED` operator and ΔQ report/Logbook updates; everything since is dependency maintenance. Brian W. Bush confirms the effort reached a dead end (2026-09-16). It is kept in the catalog for completeness: its Leios-phase models (`models.txt`), simulator cross-check outputs, and the sim-rs export path (`txn_diffusion.sh`) remain usable artifacts, and the 2026 ΔQ analyses (§ 2, § 4) took the Haskell `deltaq` route instead — a datum in itself about which ΔQ toolchain future work should build on.

A detail that closes a loop with dive 4: the shipped [`models.txt`](https://github.com/input-output-hk/ouroboros-leios/blob/main/delta_q/models.txt) opens with **"TR1 wrong Cardano model" / "TR1 used Cardano model"** — ΔQ encodings of AUEB **TECHREP1**'s Cardano diffusion model (the 0.012/0.069/0.268 s RTT triple, path-length-weighted hop ladders). The 2021 AUEB reports were thus already re-derived in ΔQ form during the 2024–25 phase. Also present: comparison outputs against the Haskell/Rust simulators (`comparison_hs.txt`, `comparison_rs.txt`) — the tool was cross-checked against the simulators, and sim-rs still exports traces to it (`txn_diffusion.sh`, dive 1).

## 2. The Linear Leios model: `analysis/deltaq/linear-leios/` (Yves Hauser, Jan–Jul 2026)

A Haskell library on [DeltaQ-SD/deltaq](https://github.com/DeltaQ-SD/deltaq) answering CIP-0164's central timing question — does a certified EB reach all honest block producers within Δ_EB? — for the proposed (L_hdr=1, L_vote=4, L_diff=7). Four executables (estimates, plots, stats, outcome diagrams); a new approximate **`sampled` backend** (Hauser's deltaq fork) alongside the exact piecewise-polynomial one, with the accuracy-vs-tractability trade-off managed by keeping the model low-complexity and pushing detail into **empirical mixture distributions**:

- **Network**: the Praos performance model's random-graph diffusion — per-hop ΔQ from three RTT classes (0.012 / 0.069 / 0.268 s, equal weight), n-hop sequential composition blended by the path-length distribution of a 2,500-node degree-10 random graph. (A mainnet-derived path-length distribution from `topology-checker` is implemented but unused — a noted realism upgrade left on the table.)
- **CPU**: `applyTx`/`reapplyTx` timing distributions **measured on a mainnet node** (apply: ~28% < 5 ms, ~8% > 10 ms; reapply much cheaper), aggregated per block by a CLT scale-mixture over a uniform tx count.
- **Committee/quorum**: per-SPO Poisson sortition over the mainnet-fitted power-law stake distribution (2,500 SPOs, expected committee 600, τ = 3/4), quorum by normal approximation — with P_quorum logic borrowed from an early version of the Markov model (dive 9 territory) and P_interrupted from the Praos Poisson process.

**Headline results**: EB diffusion+validation completes within L = 14 slots with **97.4%** probability (median 4.52 s, p95 12.23 s); certification probability per opportunity ≈ **0.356** (dominated by P_interrupted ≈ 50% at f = 1/20). Explicit limitations: honest-only, no freshest-first delivery, tail percentiles sensitive to input assumptions.

## 3. Mempool and TxCache in the ΔQ model (standing section)

§4.2 of the report is a **statistical mempool-alignment model** — the analytic counterpart to smol world's mechanistic one (dive 5) and the direct consumer of the post-CIP mempool measurements (dive 10):

- Premise, from [`post-cip/mempool-measurements`](https://github.com/input-output-hk/ouroboros-leios/tree/main/post-cip/mempool-measurements): **mempools are well synchronized; fragmentation is the exception.** When an EB arrives, its referenced txs are *expected* to already be in the local mempool.
- Linear Leios's **TxCache** (the CIP's cache of explicitly network-fetched txs) is modeled jointly with the mempool as a **two-state Markov chain** (states: in-mempool vs handled-by-TxCache) whose stationary distribution gives long-run hit/miss fractions; the original report uses p = 0.5, q = 0.9 ⇒ miss rate π₁ = 1/6 ≈ 0.17.
- A cache **hit** costs a constant lookup; a **miss** costs a network fetch through the Praos diffusion ΔQ; an EB with n references completes at the max of n parallel single-tx outcomes, F_single(t)ⁿ, mixed over uniform n.
- The **improved report updates the miss rate empirically to π₁ ≈ 0.06** (§5.5 sensitivity sweep) — i.e., measured mempool alignment is considerably better than the first model's default assumption.

**No caches with residence times exist here** — ΔQ models are stateless distributions — but the π₁ parameter *is* the compressed representation of everything the mempool/TxCache machinery does, which makes it the natural coupling point between our future mempool study and parameter-level security analysis: a mempool-alignment experiment produces a π₁ distribution; this model turns π₁ into certification probability.

## 4. The successor: `analysis/deltaq/improved-leios/` (Yves Hauser, Aug 2026; reviewed in PR #1051)

"Improved ΔQ Model for Linear Leios EB Diffusion" — a corrected and extended analysis, and the resolution of dive 5's open reference: **this is the "improved-ΔQ report" whose "Praos Table 1" RTTs smol world's topology tiers cite** (the report takes its RTTs "from the original Praos paper's Table 1"). Key advances over §2's model:

- **Three structural bug fixes** to the prior analysis (RB path structure; EB closure size; scale-mixture vs fixed-N reapplication).
- A proper **discretized-CDF numerical backend**; per-tx timing re-derived from the empirical `block-edf.csv`.
- **Two TCP congestion-control models bounding network sensitivity**: Reno via the **Mathis equation** (throughput ∝ p^(−1/2)) vs **CUBIC** (∝ p^(−3/4)) — ~11× throughput difference at loss p = 10⁻⁴ — evaluated across loss rates because whether a 12 MB closure certifies can in principle turn on the choice. (The analytic sibling of dive 5's simulated CUBIC and dive 6's real CUBIC — the three-way transport story now has an analytic leg.)
- Sensitivity programs: EB-size sweeps under both models, 1-hop vs multi-hop closure fetch (including a catastrophic pre-diffusion-failure worst case and a maximum-feasible-closure calculation), the π₁ sweep, an extreme-tail **silent-adversary** case, and **Monte Carlo tail validation** of the analytic results.
- Companion derivations: `timing_derivation.md`, `pi1_derivation.md`, `conditional_certification_diffusion.md`; analysis driver in Python (`analysis.py`).

## 5. Assessment against the four catalog dimensions

- **Faithfulness.** Analytic models with unusually strong empirical grounding (mainnet apply/reapply timings, mainnet stake fit, measured π₁, mainnet-captured `block-edf.csv`) but honest-path only, no freshest-first delivery, no topology beyond blended random-graph hops; results are distributions over a *single* EB's diffusion, not sustained load (the load question is exactly what smol world calls "the model the ΔQ report could not supply").
- **Status.** Tool (8a): discontinued Feb 2025 (dead end — B. Bush). Linear Leios model + report (8b): complete (Jul 2026); improved report: complete and reviewed (Aug 2026). Together they are the current *analytic* justification for CIP-0164's (1, 4, 7) timing parameters.
- **Scope.** Δ_EB feasibility, certification probability, and parameter sensitivity — the security-side questions; plus the tool's general load-analysis capability, mostly unexercised for Leios.
- **Performance.** Seconds to evaluate; the cheapest what-if instrument in the catalog.

## 6. Follow-up questions

1. **Couple our mempool study to π₁**: the pipeline "measured alignment → π₁ distribution → certification probability" already exists in pieces (mempool-measurements → pi1_derivation → improved model); making it end-to-end with fresh testnet data (via Piranha, dive 7) would be a high-leverage, low-cost result.
2. Swap in the **mainnet path-length distribution** (implemented, unused) and re-run — a cheap realism check the report itself suggests.
3. Add **freshest-first delivery** interaction (the report's own top modeling gap) — likely needs the simulators rather than ΔQ.
4. The Kuhn tool's load-analysis extension was never applied to Linear Leios sustained load before the tool was discontinued — if an analytic egress-contention story is wanted, it would now need porting to the Haskell `deltaq` stack (or reviving the Rust tool); weigh that against just using smol world.

## Sources

- Read at `ouroboros-leios@11be715`: [`analysis/deltaq/linear-leios/docs/report.md`](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/deltaq/linear-leios/docs/report.md) (full), [`analysis/deltaq/improved-leios/report.md`](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/deltaq/improved-leios/report.md) (ToC + executive summary), `delta_q/README.md`, `delta_q/models.txt`, directory inventories
- Commit history via GitHub API (`commits?path=analysis/deltaq/improved-leios`): Yves Hauser, Aug 2026, PR #1051 review
- [ΔQSD paper — "Mind Your Outcomes"](https://doi.org/10.3390/computers11030045); [deltaq Haskell package](https://hackage.haskell.org/package/deltaq)
- Cross-links: [Dive 4](./04-aueb-network-modeling.md) (TR1 models in `models.txt`), [Dive 5](./05-smol-world.md) (improved-report citation; load gap), [Dive 6](./06-mininet-leiosfetch.md) (CUBIC triangle), [Dive 7](./07-piranha-net-rs.md) (π₁ measurement instrument)
- [Catalog entry 8](../leios-simulation-model-catalog.md#8-deltaq-models)
