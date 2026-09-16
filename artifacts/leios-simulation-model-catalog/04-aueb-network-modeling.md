# Deep Dive 4: AUEB Network Modeling (Spyros Voulgaris et al.)

**Created:** 2026-09-16
**Status:** Draft for review.
**Provenance:** 🤖 (LLM-generated from report reading and meeting-record research, pending human review)
**Read:** TECHREP1 and TECHREP3 PDFs (Slack files `F0B3YR7BAR3`, `F0B45RA27RA`, extracted to text); Chief Scientist Meeting transcripts 2025-02-27, 2025-03-27, 2025-04-03 and Gemini notes 2026-04-23, 2026-06-18 (Google Drive); #arc-pubsub Slack channel search.
**Parent entry:** [catalog § AUEB in-house network simulator](../leios-simulation-model-catalog.md#4-aueb-in-house-network-simulator-spyros-voulgaris)

**The headline finding revises the catalog entry:** the "in-house built network simulator" behind the two technical reports shared into #team-leios in May 2026 is **PeerNet** — TECHREP1 says so explicitly — and TECHREP1 is dated **February 2021**. These are reports from the original IOHK–AUEB networking collaboration of the Praos era (authors **Evangelos Kolyvas and Spyros Voulgaris**), resurfaced by Marcin Szamotulski in 2026 because they bear on the Linear Leios "25% avalanche" question — not the product of a new 2026 simulator. The mystery of catalog entry 4 accordingly collapses, in large part, into catalog entry 3's toolchain.

---

## 1. The two reports

### TECHREP1 — "Efficient Network Overlays for Fast Data Dissemination" (Feb 2021)

Frames Cardano/Praos block dissemination (subscription-based push over chosen **upstream/downstream peers** — the exact vocabulary of `DisseminationBase` in leios-peernet, whose file header reads "Created on May 13, 2021 by Spyros Voulgaris") and proposes the **close/random (C/R) overlay policy**: each node links to some latency-closest peers and some uniformly random peers. Evaluated in **PeerNet** ("a fork of the popular PeerSim simulator… deterministic and reproducible simulation") on two topologies: a synthetic torus and the **King dataset** RTT matrix (the report's own citation for King is a broken `[?]`; the paper identification remains Szamotulski's conjecture). 1,000 nodes; valencies 6/10/20; edge cases C10 (all-close) vs R10 (all-random). Conclusion: pure-close is terrible, pure-random mediocre; a **balanced close/random mix performs near-optimally** — with the caveat, stated in the report itself, that the metric is comparative between neighbor-picking policies, "not a real Cardano metric."

### TECHREP3 — "Time-Budget Analysis through Network Simulation" (undated; same authors, same collaboration era)

Given Ouroboros's dissemination **time budget**, which combinations of (block size, per-hop validation time) complete network-wide dissemination in time? Sweeps both dimensions per node valency (8–20, always split C=R) and renders **heat maps** of budget satisfaction — the figure Szamotulski highlighted in 2026 (95%-of-nodes delivery time vs processing time × block size at C10R10). The transfer-time model is explicitly **TCP-as-chunk-round-trips**: total transfer ≈ latency × (number of ack-paced chunks), the same latency-multiples abstraction implemented in leios-peernet's `TransportLeios`/`TransportDeltaQ` (`extra_tcp_trips`). A TECHREP2 presumably exists between them — per Karl Knutsson, the AUEB deliverables included "a report, and a paper, for gossiping/peer sharing" (tornado/cyclone schemes), which is likely TECHREP2's subject ❓🤖 not located.

**Mempool and transaction caches: none.** Both reports are single-block-class, block-level dissemination studies; transactions appear only as block *weight* (size/complexity affecting transfer and validation time). This row contributes nothing to the mempool comparison except the reminder that per-hop validation delay — which the mempool's revalidation cost feeds in the real node — is one of TECHREP3's two axes.

## 2. What was actually used for Leios, and how

The reports entered the Leios record on 2026-05-15, when Marcin Szamotulski posted both PDFs into the [25%-avalanche thread](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1778845013475509?thread_ts=1778692854.742279&cid=C074AHSKJF7) as evidence about realistic topologies and hop-time distributions. They then fed Nick Frisby's `IDEA-NeighborhoodFarPeers.md` memo (dive 6's PR #880). Karl Knutsson's on-record caveats bound their authority: the deployed Cardano P2P **did not implement** the AUEB overlay proposals; AUEB's confirmed contribution to production was *validation* that Cardano's random-selection-plus-churn performed comparably to their engineered overlays (never published); and RTT-dependent peer-behavior assumptions do not describe the deployed network.

## 3. Where the code is

- **The simulator** is PeerNet — public, `PeerNet/PeerNet` on GitHub (last touched 2024), vendored as the submodule of `input-output-hk/leios-peernet` (dive 3).
- **The protocol/experiment code** for the TECHREPs (the C/R initializers, dissemination protocols, torus/King topology drivers) is not in any repository this effort can see. leios-peernet contains a 2021-vintage sibling of it (same base classes, same C/R config vocabulary, same TCP-trips transport, a `Cougar` protocol named for the AUEB model), adapted to Leios-rate experiments in 2024–25. The full original presumably lives in AUEB-side (or Spyros's personal, possibly private) repositories — as suspected. **One concrete recovery lead:** at the 2026-04-23 Chief Scientist Meeting, Spyros said "I'm going to send you the codes today" — addressed to the ARC side, with William Wolff coordinating in Slack. Whether that delivery covered the dissemination-study code or only pub/sub components is not visible in the records read; William Wolff is the person to ask, alongside Spyros himself (voulgaris@aueb.gr).

## 4. Spyros's presentations in the Chief Scientist Meeting record

For completeness of the "what has Spyros presented about simulation" question — with the caveat that **the pub/sub work is a separate research effort, not Leios**, though it involves substantial network simulation of its own:

| Date | Content |
|---|---|
| 2025-02-27 | Attended; the meeting covered Leios protocol evolution (Giorgos Panagiotakos: pipeline 7→4 stages, certificate-size reduction via deterministic committee / Fait Accompli ideas) — no Spyros presentation |
| 2025-03-27 | **Presented the pub/sub system**: three-layer architecture — SecureCyclone peer sampling (developed in earlier IOG collaboration, published at ICDCS), Vicinity-based navigation layer, BoulderCast-style in-topic ring+random dissemination — plus a decentralized key-value persistence layer with a retention period. Live demo of a Java simulator with a WebSocket/JavaScript front-end; experiments at 200 → 100,000 nodes ("needle in haystack": 10,000 nodes, 681 topics), WonderNetwork latency traces, self-healing after killing 50% of nodes. Cycle-based gossip — PeerNet-style simulation throughout |
| 2025-04-03 | Pub/sub wrap-up: security discussion; **the prototype was already delivered to IOHK**; Kiayias had shared it with Charles Hoskinson and Romain; storage incentives flagged open; Leios named as facing the analogous high-throughput storage question |
| 2026-04-23 | Pub/sub as communication substrate for SPOs (SecureCyclone core + client scalability); **"I'm going to send you the codes today"** |
| 2026-06-18 | Pub/sub ("Pop-up" in Gemini's rendering) architecture: Eclipse-attack hardening (in/out-degree flip; temporary explicit subscriber lists), "silent attacks" follow-up assigned to Spyros; technical report to be posted by William Wolff |

The pub/sub effort now lives publicly at [`input-output-hk/pubsub`](https://github.com/input-output-hk/pubsub) (public since 2026-07-28; CPS/CIP submitted to cardano-foundation/CIPs as [#1270](https://github.com/cardano-foundation/CIPs/pull/1270)/[#1271](https://github.com/cardano-foundation/CIPs/pull/1271), Sept 2026), with its own experiments program and formal analyses of SecureCyclon properties (Denis Firsov et al., #arc-pubsub). **Out of scope for this catalog** beyond this pointer, per the separation above — but if a future question needs a gossip/peer-sampling simulation substrate with active maintenance, that is where Spyros-lineage simulation is alive today.

## 5. Assessment against the four catalog dimensions

- **Faithfulness.** The reports model Praos-era block dissemination with a chunked-TCP latency-multiple transfer model and fixed per-hop validation delays over C/R overlays — comparative-policy fidelity, not absolute-number fidelity, and their own text says so. Nothing Leios-specific: no EBs, votes, or certificates; findings transfer to Leios only at the level of "overlay mixing policy" and "time-budget framing."
- **Status.** Historical (2021-era), closed deliverables; resurfaced May 2026 as design evidence. The AUEB simulation *capability* remains active — redirected to the (non-Leios) pub/sub effort.
- **Scope.** Overlay construction policy and block-size/processing-time budget analysis, 1,000-node scale, torus + King topologies.
- **Performance.** PeerNet SIM-mode runs at 1,000 nodes; not a constraint for their question.

## 6. Follow-up questions

1. Obtain **TECHREP2** (gossiping/peer sharing — the tornado/cyclone work Karl referenced) to complete the report series.
2. Ask William Wolff what "the codes" delivered after 2026-04-23 contained; ask Spyros whether the TECHREP experiment code (and the missing latency matrices from dive 3) can be shared into an IOG repo.
3. If the 25%-avalanche analysis is revisited, prefer re-running the *question* on current tooling (sim-rs partitions + smol world) over relying on the 2021 comparative results, per Karl's caveats.

## Sources

- TECHREP1 — Efficient Network Overlays for Fast Data Dissemination, E. Kolyvas & S. Voulgaris, AUEB, Feb 2021 (Slack file `F0B3YR7BAR3`, internal)
- TECHREP3 — Time-Budget Analysis through Network Simulation, E. Kolyvas & S. Voulgaris, AUEB, undated (Slack file `F0B45RA27RA`, internal)
- [25%-avalanche thread — #team-leios, 2026-05](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1778692854742279?thread_ts=1778692854.742279&cid=C074AHSKJF7) (Szamotulski posts, Knutsson caveats)
- Chief Scientist Meeting records (internal, Google Drive): [2025-02-27 transcript](https://docs.google.com/document/d/13GpoGhNIx9CJLQywc6xFd6OQCwfMSqhxI_qvblneMQA/edit), [2025-03-27 transcript](https://docs.google.com/document/d/1KhKzpt24M0lkQs9OAyLj4faI5dDSYs5QfOF23EllqaM/edit), [2025-04-03 transcript](https://docs.google.com/document/d/1PbYY-9aJHr6r_os-S-uIGANS508h2xdR4ECDWuwzj6Y/edit), [2026-04-23 notes](https://docs.google.com/document/d/1K31Jjkdf8OoMSrgSpwLSUL-rvQZYWppxXgBTqU6K0ZQ/edit), [2026-06-18 notes](https://docs.google.com/document/d/1UViK_x8fk9QvqmHs8a2q2ipWPlm9FEXsW87fpmNL7xw/edit)
- [#arc-pubsub channel (internal)](https://input-output-rnd.slack.com/archives/C0AK5MW3DJB) — pub/sub repo/CIP pointers; [input-output-hk/pubsub](https://github.com/input-output-hk/pubsub)
- [Dive 3 — leios-peernet](./03-leios-peernet.md) (code-lineage evidence)
