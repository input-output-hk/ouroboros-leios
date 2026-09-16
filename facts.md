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

## Protocol Parameters

*(To be established: the parameter set, its symbols, its defaults, and where those defaults are defined upstream.)*

## Baselines

*(To be established: the Cardano Praos baseline figures that Leios claims are measured against, with their sources.)*

## Environment and Toolchain

*(To be established: what builds and runs locally, at which versions, and what it took. See the per-experiment `lessons-learned.md` files for the detail.)*
