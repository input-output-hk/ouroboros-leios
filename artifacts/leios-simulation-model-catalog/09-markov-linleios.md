# Deep Dive 9: The Markovian Model of Linear Leios (`linleios`)

**Created:** 2026-09-16
**Status:** Draft for review.
**Provenance:** 🤖 (LLM-generated from source reading, pending human review)
**Read at:** [`ouroboros-leios/analysis/markov/`](https://github.com/input-output-hk/ouroboros-leios/tree/main/analysis/markov) @ `11be715` — ~950 lines of Lean 4 (`Linleios/{Types,Evolve,Probability,Metrics,Util}.lean`, `Main.lean`, property tests) + `ReadMe.md`, experiments.
**Parent entry:** [catalog § Markovian model](../leios-simulation-model-catalog.md#9-markovian-model-of-linear-leios-linleios)

Brian W. Bush's exact-probability model of Linear Leios EB certification (Oct–Nov 2025): not a sampled simulation but a **forward evolution of the full state-probability distribution** of a small Markov chain, in Lean 4, answering "how many EBs certify per N ranking-block opportunities?" as an exact distribution rather than a run average.

---

## 1. Model

- **State** (5 components): clock (RB *opportunities*, the time unit — not slots), RBs forged, EBs certified, `hasRb` (RB forged this step), `canCertify` (certificate ready). The full joint distribution lives in a `HashMap State Probability`; states below a tolerance (default 10⁻⁸) are discarded, and the discarded mass is *reported* ("missing probability" on stderr) — the approximation is tracked, not silent.
- **Transition = four substeps per opportunity**: *forge RB* (honest with probability 1 − f_adv); *certify* (requires quorum-ready + RB spacing ≥ 3·L_hdr + L_vote + L_diff, with the spacing probability computed from the active-slot coefficient as (1−f)^(L−1)); *forge EB* (fails with p_late — the chance the producer hasn't validated the previous EB in time, discounted by committee membership n_comm/n_pools since voters already computed the ledger state); *vote* (per-pool Bernoulli successes over the stake distribution, expected committee 600 of 2,500 pools, quorum τ = 0.75 — the same sortition-quorum computation the ΔQ report later borrowed, dive 8).
- **Network and CPU are folded into three input probabilities**: p_rb (RB header arrives within L_hdr; default 0.95), p_eb (EB fully validated in time; 0.90), p_late (0.05). The **adversarial model is stake that abstains** — never forges RBs/EBs, never votes (f_adv) — a clean worst-case for liveness, with no equivocation or targeted-delay behavior.
- **Outputs**: RB/EB/payload efficiencies, the full distribution of certified-EB counts (JSON), and the missing probability. Example: at (1, 4, 5), τ = 0.8, f_adv = 0.1 → RB efficiency 0.90, EB efficiency 0.31.

## 2. Provenance, quality, experiments

Written Oct 2025 (#576), documented (#591) and **property-based tested** (#609, `LinleiosTest.lean`), cataloged in post-CIP findings (#619). Four recorded experiment sweeps with SVGs (`experiments/`): protocol parameters, non-ideal network, adversary under ideal conditions, committee-and-quorum — driven by `parameter-sweep.sh` and `experiments.ipynb`. Lean toolchain pinned; `docbuild/` for rendered docs. Complete and stable since Nov 2025.

## 3. Mempool and transaction caches (standing section)

**None — and instructively so.** Everything the mempool/TxCache machinery does is compressed into **p_eb** (was the EB validated in time? — which in reality includes fetching any missing transactions) and **p_late** (did the next producer have the ledger state?). Where the ΔQ model (dive 8) exposes mempool alignment as an explicit π₁ parameter feeding a fetch-time distribution, `linleios` absorbs it one level deeper into a single validation-success probability. A mempool-alignment study could therefore feed *both*: measured alignment → π₁ → (via ΔQ) a p_eb distribution → (via `linleios`) certified-EB distributions under adversarial abstention. The three models compose into a pipeline no one of them provides alone.

## 4. Assessment against the four catalog dimensions

- **Faithfulness.** Exact arithmetic over an intentionally tiny state space; the protocol timing rule (spacing, cadence) matches CIP-0164, and the sortition/quorum math is shared with the ΔQ analyses. All network/CPU realism is delegated to the three input probabilities — the model is as faithful as what is fed into it.
- **Status.** Complete, tested, documented; no changes since Dec 2025 formatting.
- **Scope.** EB-certification counting under parameter, network-quality, and abstaining-adversary variation. No diffusion, no topology, no transactions, no rival EBs (contrast dive 5's `simulateBattle`).
- **Performance.** Milliseconds-to-seconds per run; the cheapest adversarial-sweep instrument in the catalog.

## 5. Follow-up questions

1. Feed **empirically derived p_rb/p_eb/p_late** from the ΔQ CDFs (success-within-deadline values) or simulator measurements, replacing the round defaults — the composition in § 3.
2. The abstention adversary is the mildest adversarial model in the catalog; worth documenting explicitly *which* attacks it bounds (it does not cover equivocation or targeted withholding — those live in sim-rs behaviors and Piranha).
3. Lean 4 here is used as a programming language, not a proof assistant — no theorems are proved about the chain ❓ (nothing found beyond property tests). If the model becomes load-bearing for parameter choices, mechanizing its key monotonicity claims would be cheap insurance — and a natural fit for this repository's formal-methods bent.

## Sources

- Read at `ouroboros-leios@11be715`: `analysis/markov/ReadMe.md` (full), `src/Linleios/{Types,Evolve}.lean`, directory inventory; commit history via GitHub API (Bush, Oct–Nov 2025: #576, #591, #609, #614, #619)
- [post-cip/README.md — Markovian model section](https://github.com/input-output-hk/ouroboros-leios/blob/main/post-cip/README.md)
- Cross-links: [Dive 8](./08-deltaq-models.md) (shared quorum math; π₁ → p_eb composition), [Dive 5](./05-smol-world.md) (complementary battle/egress questions)
- [Catalog entry 9](../leios-simulation-model-catalog.md#9-markovian-model-of-linear-leios-linleios)
