# Journal — Phase 0 (Scope Discovery)

Reverse-chronological log. Newest date sections first; newest entries first within a date. See [AGENTS.md](../AGENTS.md) § Repository Blueprint for the format rules.

## 2026-09-16

### Adversarial fact-check of the simulation catalog 🤖

An Opus subagent adversarially verified the [simulation/model catalog](../artifacts/leios-simulation-model-catalog.md) against its sources (GitHub repos/PRs, Slack threads) without repeating the discovery sweep. It confirmed most entries verbatim (Mininet test bed, leios-peernet, formal spec, post-CIP, Piranha's Slack-sourced characterization) and found substantive errors, now corrected: sim-rs *does* model TCP (a congestion-window port of the Haskell `ModelTCP.hs`, on by default; only loss/retransmission/delayed-ACKs absent) — the original "no TCP dynamics" claim was wrong; "smol world" is a draft PR with zero review activity but models full Linear Leios EB diffusion and certification, the opposite of the catalog's guess; the "unlocated" Hauser DeltaQ work is the `analysis/deltaq/linear-leios` artifact itself; `leios-peernet` is private; the pseudo-mainnet is 2,685 nodes in the current v4 (10,000 was v1); two links pointed at wrong branches/repos. Lesson for [meta-lessons-learned.md](../meta-lessons-learned.md): summary-table cells silently dropped hedges that the detail sections carried.

### Cataloged Leios simulations and models 🤖

Created [the catalog of Leios simulations and models](../artifacts/leios-simulation-model-catalog.md), answering the [#team-leios question](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1789558993289409?thread_ts=1789558993.289409&cid=C074AHSKJF7) about available network simulators, their faithfulness, status, scope, and performance. Sources swept: GitHub (five Leios repos plus two open PRs), Slack (#team-leios, #formal-methods, #high-fives, DMs), Confluence (Innovation, IOE, NC spaces), and Google Drive (simulation-analysis decks, tutorial recording, SOW). Twelve primary artifacts cataloged — seven simulators/emulators, five model/verification families — plus supporting topologies, calibration data, and a cross-validation record. Five gaps recorded, the largest being that no unified same-topology/same-workload faithfulness comparison across simulators exists. Confirmed facts written to [facts.md](../facts.md). The AUEB simulator code (Spyros Voulgaris) and the private `leios-adversarial-tools` repository remain unobtained; several claims in the catalog carry ❓🤖 SCRUTINY markers accordingly.
