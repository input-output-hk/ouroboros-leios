# Catalog of Leios Simulations and Models

**Created:** 2026-09-16
**Status:** Draft for review. An adversarial LLM fact-check pass (Opus, 2026-09-16) verified the claims against sources; its corrections are applied below.
**Provenance:** 🤖 (LLM-generated, pending human review)

This catalog answers the question posed in [#team-leios on 2026-09-16](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1789558993289409?thread_ts=1789558993.289409&cid=C074AHSKJF7): *what network simulators do we currently have available for Leios, and what are their faithfulness to the implementation, status, scope, and performance?* No such summary previously existed (confirmed in that thread). It covers simulators in the strict sense, network-emulation test beds, and analytical/mathematical models — anything that predicts or reproduces Leios behavior short of the production `cardano-node` implementation itself — with emphasis on networking.

Ouroboros Leios ([CIP-0164](https://github.com/cardano-foundation/CIPs/pull/1078)) is a throughput-scaling extension of Ouroboros Praos in which block producers create larger **endorser blocks (EBs)** alongside Praos **ranking blocks (RBs)**; EBs are certified by a stake-weighted voting committee before ledger inclusion. Earlier protocol variants also had **input blocks (IBs)**, since dropped; several artifacts below predate that change, which is the single most important faithfulness caveat in this catalog. Two new node-to-node (N2N) mini-protocols carry Leios traffic: **LeiosNotify** (announcements) and **LeiosFetch** (data retrieval).

Each entry records the four dimensions from the motivating question. "Faithfulness" is assessed against the current protocol design (CIP-0164 Linear Leios) and, where relevant, against the prototype `cardano-node` implementation running on the Leios testnet. Statements are current as of 2026-09-16; repository descriptions were read at that date's `HEAD` of each default branch.

---

## Summary table

| # | Artifact | Kind | Language | Protocol scope | Network model | Status (2026-09-16) |
|---|----------|------|----------|----------------|---------------|---------------------|
| 1 | [sim-rs](#1-sim-rs--the-rust-leios-simulator) | Discrete-event / actor simulator | Rust | Full Linear Leios incl. txs, mempool, votes, attackers | Per-connection latency + bandwidth, per-mini-protocol sharing; TCP congestion-window model on by default (no loss/retransmission) | **Active**; the maintained reference simulator |
| 2 | [Haskell simulation (`ols`)](#2-haskell-simulation-ols) | Discrete-event simulator + visualization | Haskell | Praos + **Short Leios (outdated variant)** | Packet/TCP-level modeling, global-scale P2P | Dormant; Leios parts outdated, Praos/network viz still useful |
| 3 | [leios-peernet](#3-leios-peernet-java--peernet) | Round/event simulator | Java | Block diffusion only, single undifferentiated block type | Bandwidth, latency, processing, colocation delay; PeerNet SIM/EMU/NET modes | Dormant since ~Feb 2025 |
| 4 | [AUEB in-house network simulator](#4-aueb-in-house-network-simulator-spyros-voulgaris) | Network simulator (code not in hand) | ❓🤖 unknown | Overlay construction + large-payload dissemination policies | RTT matrices (King dataset), CxRy close/random overlay policies | Reports delivered May 2026; code location unknown |
| 5 | ["smol world"](#5-smol-world-ouroboros-network-pr-5424) | Discrete-event simulator | Haskell | Linear Leios EB diffusion and certification (announce → body → closure) | Realistic transport: loss + RTO, small-world topology, per-node egress contention | **Draft** PR (Aug 2026, no review activity); likely source of the Sept 2026 egress-stability analysis ❓🤖 |
| 6 | [Mininet LeiosFetch test bed](#6-mininet-leiosfetch-test-bed) | Network **emulation** test bed | C + Python + Mininet | LeiosFetch-style pull diffusion of 12 MB payloads | Real Linux kernel TCP, tc traffic shaping, per-link middleboxes | Open PR #880 (Apr 2026 checkpoint) |
| 7 | [Piranha node + cluster](#7-piranha-node--cluster-leios-adversarial-tools) | Lightweight live-network node (usable as simulator) | Rust | Real N2N Praos + Leios protocols, honest & adversarial behaviors | Real network (Leios testnet); no ledger | **Active** (red team); private repo |
| 8 | [DeltaQ tooling](#8-deltaq-models) | Analytical timeliness/load model | Rust (tool), Haskell (Linear Leios model) | EB diffusion timeliness, certification probability | Outcome-expression composition over CDFs | Tool general-purpose; Linear Leios model with report |
| 9 | [Markovian model of Linear Leios](#9-markovian-model-of-linear-leios-linleios) | Analytical stochastic model | Lean 4 | EB certification probability vs RB production; efficiencies | Network abstracted into parameters | Complete post-CIP finding |
| 10 | [Mempool & constraint models](#10-mempool-and-constraint-models-post-cip) | Simulation + analytical models | mixed | Mempool behavior, protocol constraint satisfaction | Abstracted | Post-CIP findings collection |
| 11 | [Formal specification + trace verifier](#11-formal-specification-and-trace-verifier) | Executable formal model + conformance checker | Agda (+ generated) | Linear Leios protocol envelope; safety & liveness proofs | Network-agnostic (trace-level) | **Active**; runs against live testnet nodes |
| 12 | [Testnet, devnets, Antithesis](#12-execution-environments-testnet-devnets-antithesis) | Real-implementation execution environments | — | Whole prototype node | Real network / containerized / deterministic hypervisor | **Active** |

Supporting assets — topology generators and checkers, empirical measurement corpora, cryptographic benchmarks — are cataloged in [Supporting models and inputs](#supporting-models-and-inputs).

---

## Simulators and emulators

### 1. sim-rs — the Rust Leios simulator

**Location:** [`input-output-hk/leios-tools/sim-rs`](https://github.com/input-output-hk/leios-tools/tree/main/sim-rs) (moved from [`ouroboros-leios/sim-rs`](https://github.com/input-output-hk/ouroboros-leios) with per-directory history preserved). Crates: `sim-core`, `sim-cli`, on shared `shared-rs` (consensus behavior-tree engine, `tcp-model`).

**Scope.** The most complete Leios simulator: transactions, mempool, IB/EB/vote/RB objects (tracking protocol evolution over time), sharding strategies, attacker behaviors, and the transaction lifecycle end to end. Emits JSONL or CBOR event traces consumed by the analysis notebooks, the web visualizer, and the trace verifier. Configured by shared YAML parameter files ([`data/simulation/config.default.yaml`](https://github.com/input-output-hk/leios-tools/blob/main/data/simulation/config.default.yaml) with JSON schema) and topology files up to the 10,000-node pseudo-mainnet.

**Network faithfulness.** Explicit point-to-point connections with independent per-direction latency and bandwidth; bandwidth on a connection is split equally among *active mini-protocols*, and messages within one mini-protocol serialize. Three transport regimes are dispatched per connection (documented in [`sim-rs/docs/tcp-modelling.md`](https://github.com/input-output-hk/leios-tools/blob/main/sim-rs/docs/tcp-modelling.md)): a **TCP congestion-window model** — a direct port of the Haskell simulator's `ModelTCP.hs`, with slow start (initial window 10 per RFC 6928, 1460-byte segments) and RFC 6298 idle reset — which is **on by default** (`tcp-congestion-control: true` in `config.default.yaml`); a simple latency + fair-bandwidth fallback (delay = size/bandwidth + latency) when that is disabled; and an analytic envelope from `shared-rs/tcp-model` (slow-start ramp, idle reset, and loss modeled as a one-RTO head-of-line stall with additive-increase/multiplicative-decrease recovery), mutually exclusive with the congestion-window model and unused under default configuration. What the default regime genuinely omits: packet loss, retransmission, and delayed ACKs. Mini-protocols are fire-and-forget, not state machines, so pipelining and head-of-line effects of the real N2N multiplexer are out of scope.

**Determinism.** Two engines: the default `actor` engine (tokio actors on a coordinated virtual clock; *not* deterministic; supports attackers) and a `sequential` discrete-event engine (strict timestamp order; deterministic; no attacker support). Both support sharding nodes into parallel groups with conservative message blocking based on minimum inter-shard latencies; configurable clock resolution trades temporal precision for parallelism.

**Status.** The actively maintained simulation (per the ouroboros-leios README and the 2026-09-16 thread). Originally built by Sundae Labs under the 2024 statement of work ("Rust-based simulation of the Leios protocols... web-browser interface to execute and visualize"); now IOG-maintained. Current work extends it for alternative vote-diffusion strategies (William Wolff, on Sebastian Nagel's request, Sept 2026).

**Performance.** Virtual-time execution "as fast as your machine allows," multithreaded; ran the pseudo-mainnet topology family — 10,000 nodes in v1, flagged by its own README as a first cut; the currently recommended `topology-v4-mainnet.yaml` is 2,685 nodes — and Linear Leios workloads up to 1000 transactions per second (TPS) in the 2025 experiment series ([Slack, 2025-07-25](https://input-output-rnd.slack.com/archives/C07C7JTPX1U/p1753475153116689) and the `analysis/sims` notebooks). Trace files grow huge quickly at scale.

**Faithfulness checks available.** Its traces are checked by the Agda-derived trace verifier (entry 11), and it was historically cross-validated against the Haskell simulator (IB-diffusion comparison experiments, 2025).

### 2. Haskell simulation (`ols`)

**Location:** [`ouroboros-leios/simulation/`](https://github.com/input-output-hk/ouroboros-leios/tree/main/simulation).

**Scope.** Praos block diffusion, basic TCP examples, a simple block-relay protocol, and a "Leios-like traffic pattern for input blocks over a global-scale P2P network." Built-in Gtk+ live visualization and PNG frame export; `ols viz` / `ols sim` entry points. Configuration is partly in code — experiments require editing source.

**Faithfulness.** Historically the *high-fidelity* simulator of the pair — its `ModelTCP.hs` is the origin of the TCP congestion-window model that sim-rs later ported, so that particular fidelity gap is now largely closed at sim-rs's current `HEAD` — and the reference in the Rust-vs-Haskell cross-checks and the IOE weekly reports ("Integrated Linear Leios into the Haskell simulator," July 2025). **However, [`simulation/README.md`](https://github.com/input-output-hk/ouroboros-leios/blob/main/simulation/README.md) now states it predates the move away from input blocks, implements Short Leios, and is no longer current with the protocol design.** The Praos and network visualizations remain useful.

**Status.** Dormant for Leios purposes; superseded by sim-rs.

**Performance.** Slower than sim-rs (single high-fidelity runs; the November 2025 simulation tutorial recorded the team preference for "the faster, multithreaded Rust simulator over the high-fidelity Haskell simulator"). Developed largely by Well-Typed (by commit count: Andrea Vezzosi, Wen Kokke, Duncan Coutts), with IOG's Nicolas Frisby contributing comparably to Coutts.

### 3. leios-peernet (Java / PeerNet)

**Location:** [`input-output-hk/leios-peernet`](https://github.com/input-output-hk/leios-peernet) — a **private** repository (accessible to this effort's token, unlike entry 7's) — with an `analysis/` ingestion pipeline alongside. PeerNet itself is vendored as a git submodule.

**Scope.** Block diffusion only — no mempool, no distinction among RB/IB/EB/vote (a single block type), no stochastic block production or sizes. Simulates bandwidth, latency, per-hop processing, and colocation ("spot") delay. Built on [PeerNet](https://github.com/PeerNet/PeerNet) (Spyros Voulgaris's framework), which offers three modes: SIM (event-driven simulation), EMU (protocol-per-thread emulation), NET (real network execution). Source classes include DeltaQ and Leios transport variants and single/multi-block Leios protocols.

**Faithfulness and performance (as assessed Feb 2025).** Brian W. Bush aligned its configuration with the 100-node reference topology and found: block-arrival latencies roughly 2× the Haskell simulator's; protocol breakdown between 5 and 10 blocks/s; topology parameterized in code rather than read from disk; fewer network/CPU parameters than Haskell/Rust; very poor scaling (hours per run at high block rates); JSON event logging had to be added for analysis. Conclusion at the time: not worth further investment given the Haskell/Rust simulators' RB/IB/EB/vote-level resolution ([assessment](https://input-output-rnd.slack.com/archives/D07TDP6GATF/p1740144145525689), [comparison request](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1740087047992029)). William Wolff's run plots are in a [Drive folder](https://drive.google.com/drive/folders/1FquVrKshA8btSYnmbllg4CvsB98XZTXH).

**Status.** Dormant; last repository update 2025-02-21.

### 4. AUEB in-house network simulator (Spyros Voulgaris)

**What it is.** A network simulator built by [Spyros Voulgaris](https://acropolis.aueb.gr/~spyros/)'s group at the Athens University of Economics and Business (AUEB), distinct from (or an evolution of) leios-peernet, used to produce two technical reports shared into #team-leios on 2026-05-15 by Marcin Szamotulski:

- **TECHREP1 — Efficient Network Overlays for Fast Data Dissemination** (Slack file `F0B3YR7BAR3`)
- **TECHREP3 — Time Budget Analysis** (Slack file `F0B45RA27RA`)

**Scope.** Overlay-construction policies mixing close and random peers (`CxRy`, e.g. `C10R10` = 10 close + 10 random), evaluated for large-payload dissemination: heat maps of time to reach 95% of nodes as a function of per-hop processing time and block size; RTT matrices from "the King dataset" — the report's own citation is a broken `[?]`, and the identification with the [King paper](https://www.gribble.org/papers/king.pdf) is Marcin Szamotulski's in-thread conjecture ("probably refers to") ❓ **SCRUTINY**. TECHREP3 concluded `C10R10` is near-optimal in its setting. These reports directly informed the "25% avalanche" analysis for Linear Leios and Nick Frisby's NeighborhoodFarPeers design memo (entry 6 and [PR #880 discussion](https://github.com/input-output-hk/ouroboros-leios/pull/880)).

**Faithfulness caveats.** Karl Knutsson's correction stands on the record: the deployed Cardano P2P peer-selection/sharing design did **not** implement the AUEB proposals (tornado/cyclone gossip schemes); the AUEB contribution to deployed Praos was validation that Cardano's random-selection-plus-churn design performed comparably to their engineered overlays (unpublished). RTT-dependent peer behavior assumptions in the reports do not describe the deployed network ([thread](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1779365130926229?thread_ts=1778692854.742279&cid=C074AHSKJF7)).

**Status.** ❓🤖 **SCRUTINY**: the simulator's code has not been shared with IOG as far as this catalog could determine (searches of GitHub, Slack, and Drive); the deliverables in hand are the two PDF reports (a TECHREP2 presumably exists but was not located). Where the numbering C/R policies overlap with `Cougar.java` in leios-peernet, the two codebases may be related. Contact for confirmation: Spyros Voulgaris (voulgaris@aueb.gr), Marcin Szamotulski, Giorgos Panagiotakos.

**Related historical work.** Spyros's earlier Leios block-diffusion simulations (2024, shared via Giorgos Panagiotakos, [#team-leios 2025-02-03](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1738594632123089)) became entry 3. The July 2026 IO R&D seminar on Leios included Spyros among invitees (Drive meeting notes, 2026-07-27).

### 5. "smol world" (ouroboros-network PR #5424)

**Location:** [IntersectMBO/ouroboros-network#5424](https://github.com/IntersectMBO/ouroboros-network/pull/5424), branch `mw/hello-smol-world` (Marcin Wójtowicz), opened 2026-08-31, open as of 2026-09-16.

**Scope.** In the author's words: "a discrete-event simulator with realistic transport (loss + RTO [retransmission timeout]) on a faithful small-world topology with per-node egress contention." This targets exactly the regime the other simulators miss: TCP loss/retransmission dynamics and shared egress bottlenecks at a node, over a topology that reproduces the deployed network's small-world structure. Contrary to first appearances it is not a bare payload-diffusion model: `SmallWorld/Diffusion.hs` implements store-and-forward **Linear Leios EB diffusion** — EB announce → EB body (transaction references, ≤512 kB) → EB closure pull — with committee seats and members, quorum cadence, and EB apply delay modeled. Haskell, ~10 modules.

**Status and use.** A **draft** PR with no reviews or comments and no commits since 2026-08-31 — not yet under review. Nonetheless apparently load-bearing: the Linear Leios stability analysis presented by Marcin Wójtowicz and Karl Knutsson (September 2026) drew on "network simulator results and a theoretical analysis grounded in published BitTorrent research," showing how system stability depends on egress throughput ([high-five](https://input-output-rnd.slack.com/archives/C011H74QZNF/p1788799962666299)). ❓🤖 **SCRUTINY**: that the presentation's simulator is this PR is inferred from authorship and timing, not stated outright; the presentation artifact itself (slides/recording) was not located in this pass. Sebastian Nagel also noted that Marcin W. "just built something similar" to sim-rs and might review it ([#team-leios, 2026-09-14](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1789410308296569?thread_ts=1789389089.010549&cid=C074AHSKJF7)).

**Performance/faithfulness.** Not yet characterized publicly. Its niche is transport realism (loss + RTO) combined with genuine Linear Leios diffusion logic.

### 6. Mininet LeiosFetch test bed

**Location:** [ouroboros-leios PR #880](https://github.com/input-output-hk/ouroboros-leios/pull/880) (`nfrisby/april2026-checkpoint`), directory `docs/targeted-design-investigations/mininet-LeiosFetch-test-bed/`. Author: Nicolas Frisby.

**Scope.** An **emulation** (not simulation): a pull-based P2P diffusion protocol for large payloads (up to 12 MB, ~1500 components — i.e., EB closures at Leios scale) runs in real processes over [Mininet](http://mininet.org/) with Linux `tc` traffic shaping and a per-link middlebox architecture, inside a privileged Docker container. A C node is driven by pluggable Python fetch schedulers spanning the policy space: `OnePeerScheduler` (minimal bandwidth, catastrophic tail), `FullHedgeScheduler` (request everything from everyone, cancel duplicates — ~2× bandwidth waste), and the primary subject `FetchScheduler` (bandwidth-delay-product-aware with pipeline-depth calibration, rebalancing, and threshold-based hedging). `ANALYSIS.md` has head-to-head numbers; `DESIGN.md` states the policy-parameterization argument.

**Faithfulness.** Highest transport realism in the catalog short of real deployment — actual kernel TCP — but the protocol logic is a stylized LeiosFetch, not the `cardano-node` implementation, and topologies are small (e.g., `topo-8-1`).

**Design memos attached.** `IDEA-NeighborhoodFarPeers.md` (with its Appendix's concrete far-peer policy and supporting arithmetic — the output of the "25% avalanche" thread and the AUEB reports) and `IDEA-EbClosureMinimumAge.md`.

**Status.** **Draft** PR, April 2026 checkpoint; discussion active through May 2026.

### 7. Piranha node + cluster (leios-adversarial-tools)

**Location:** `input-output-hk/leios-adversarial-tools` — **private**; not accessible to this catalog's author token ❓🤖 **SCRUTINY**: characterization below is assembled from Slack and from the public [`leios-tools`](https://github.com/input-output-hk/leios-tools) README, not from the repository itself. Contains `net-node`, `net-cluster`, `net-ui`, and behavior-tree definitions (`behaviours/*.toml`).

**Scope.** A lightweight Rust Cardano/Leios node ("Piranha") built on the public **net-rs** stack (below), deployed as a cluster (PIR0 plus red-team machines PIR1–PIR10; [Lotoski 2026-08-30](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1788082826261799?thread_ts=1788041943.086199&cid=C074AHSKJF7), [Paprocki 2026-09-10](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1789027355690649?thread_ts=1788741781.779759&cid=C074AHSKJF7)) on the **live Leios testnet** by the red team (Christopher Tilt, Krzysztof Paprocki, Dmitry Shtukenberg; infrastructure John Lotoski). It forges blocks, votes, and certifies, but has **no ledger** — it reads nonces, BLS keys, and committee positions from kleioscan/dbsync; mempool capacity 10,000 transactions ("at least in Piranha" — [Shtukenberg via Nagel, 2026-08-12](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1786523419991819?thread_ts=1786468624.278459&cid=C074AHSKJF7)). Behaviors (honest default, or attacks: withholding TX offers, not fetching EB bodies, crafting EBs directly with chosen transactions) are driven by the behavior-tree engine in `shared-rs` ([spec](https://github.com/input-output-hk/leios-tools/tree/main/specs/001-behavior-tree-engine)). Demonstrated the EB Trojan Horse attack against the testnet (Aug 2026).

**As a network simulator.** Dmitry Shtukenberg (2026-09-16): "It can be used as network simulator with light-weight nodes. It can make sense for some kinds of research" — i.e., many cheap protocol-faithful nodes on real networking, between sim-rs's abstractions and full `cardano-node` deployments.

**Faithfulness.** Real N2N wire protocols (it interoperates with prototype `cardano-node`s), real network; *not* faithful in ledger/validation behavior. That gap is partly the point — it is what the red team exploits and probes — but it has also produced *accidental* protocol violations on the testnet (an unintended EB forging and double spends acknowledged in the [Aug 2026 thread](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1787863719890129)), so treat Piranha-sourced traffic as protocol-shaped, not protocol-correct.

**Status.** Active; cluster state (Node/Piranha/Off) is tracked at the bottom of the internal IOG stake dashboard ([Lotoski 2026-08-30](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1788082826261799?thread_ts=1788041943.086199&cid=C074AHSKJF7)).

**Public substrate: net-rs.** [`leios-tools/net-rs`](https://github.com/input-output-hk/leios-tools/tree/main/net-rs) is the reusable, public part: a Rust implementation of the full Cardano N2N stack — all six Praos mini-protocols plus LeiosNotify (protocol 18) and LeiosFetch (protocol 19, bitmap-based selective TX addressing) — with a QoS multiplexer (Praos priority class, Leios weighted fair queuing; per-protocol egress queues with backpressure) and a multi-peer coordinator (offer dedup, RTT-based fetch peer selection). Positioned as "built for network prototyping, simulation, and as a reference design for node implementors."

---

## Analytical and formal models

### 8. DeltaQ models

Two related artifacts apply ΔQ systems development (ΔQSD) — algebraic composition of latency distributions (cumulative distribution functions, CDFs) — to Leios timeliness:

- **[`delta_q/`](https://github.com/input-output-hk/ouroboros-leios/tree/main/delta_q)** (Roland Kuhn): a general-purpose Rust + web-UI tool for ΔQSD modeling, extending the published theory with load analysis (resource-usage metrics attached to outcomes) and gossip-diffusion operators. Used in the 2024–2025 phase to model IB diffusion timeliness alongside the simulators.
- **[`analysis/deltaq/linear-leios/`](https://github.com/input-output-hk/ouroboros-leios/tree/main/analysis/deltaq/linear-leios)**: a Haskell library (on [DeltaQ-SD/deltaq](https://github.com/DeltaQ-SD/deltaq)) modeling **Linear Leios** specifically — EB diffusion statistics and certification probabilities, with parameter estimation from data and a written [report](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/deltaq/linear-leios/docs/report.md).

Faithfulness: analytical models over empirically estimated per-hop CDFs; no topology or adversary. Fast to evaluate; the natural tool for the "25% avalanche" failure-rate sketches (Frisby/Szamotulski thread, May 2026), where Sebastian Nagel cited Yves Hauser's and Marcin Wójtowicz's DeltaQ work as prior art — that work *is* the `analysis/deltaq/linear-leios/` artifact above (62 commits by Hauser, Jan–Jul 2026, with contributions by Wójtowicz). Nicolas Henin's related analysis, also cited there, remains unlocated.

### 9. Markovian model of Linear Leios (`linleios`)

[`analysis/markov/`](https://github.com/input-output-hk/ouroboros-leios/tree/main/analysis/markov), described in [`post-cip/README.md`](https://github.com/input-output-hk/ouroboros-leios/blob/main/post-cip/README.md). A stochastic state model — state = (RBs produced, EBs produced, honest-RB flag, certificate-ready flag), time in block-forging opportunities, substeps forge-RB / certify / forge-EB / vote — computing the probability distribution of certified EBs and the RB/EB/payload efficiencies, with network characteristics as command-line parameters. Complements the simulators with exact (finite-resolution) probabilities rather than sampled runs.

### 10. Mempool and constraint models (post-CIP)

[`post-cip/`](https://github.com/input-output-hk/ouroboros-leios/tree/main/post-cip) collects post-CIP modeling by Brian W. Bush (primary) and William Wolff: **mempool-model**, **mempool-sim-viz** and **mempool-sim-web** (mempool simulation with visualization, including a web variant), **constraint-model**, **empirical-distributions**, **peer-topology**, plus measurement corpora (block, transaction, mempool measurements; UTxO set-size and lifetime analysis; CPU costs of `Apply`/`Reapply` and Plutus ledger operations; bandwidth–latency studies; active-slot and weighted-fait-accompli analyses). These are the constraint- and workload-side models that feed simulator inputs and CIP parameter justifications.

### 11. Formal specification and trace verifier

- **[ouroboros-leios-formal-spec](https://github.com/input-output-hk/ouroboros-leios-formal-spec)**: machine-checked Agda specification of Linear Leios, with **safety and liveness proofs** (common prefix, honest chain growth, existential chain quality, conditional on Praos base-chain properties), built on the categorical-crypto composable-process library. [Rendered docs](https://leios.cardano-scaling.org/formal-spec/Leios.Linear.html).
- **[leios-trace-verifier](https://github.com/input-output-hk/ouroboros-leios/tree/main/leios-trace-verifier)** (with `leios-trace-hs`): a certified, decidable checker derived from the Agda spec (Andre Knispel, Yves Hauser) that verifies whether an execution trace stays within the protocol envelope — deliberately *not* a deterministic reference implementation, so differently-scheduled implementations both pass. Originally used to conformance-check the Rust and Haskell **simulators** against the spec; as of August 2026 it runs against **real testnet node logs**, including as a live network monitor on Ramsay Taylor's node (Ramsay Taylor, Yves Hauser, Javier Díaz; [Confluence blog](https://input-output.atlassian.net/wiki/spaces/NC/blog/2026/08/20/6219563009/Leios+Team+develops+safe+and+live+trace+verifier+for+protocol+conformance+testing)).

For this catalog's purposes the pair is the **faithfulness instrument**: it is how any simulator's protocol logic can be checked against the specification, and it spans spec → simulators → implementation.

### 12. Execution environments (testnet, devnets, Antithesis)

Not simulators, but the reference points faithfulness is measured against:

- **Leios testnet** — live since 2026-06-23 ([launch announcement](https://input-output-rnd.slack.com/archives/C0XL53C78/p1782225761886479), [team high-five](https://input-output-rnd.slack.com/archives/C011H74QZNF/p1782227825782329)), prototype `cardano-node`s; the environment Piranha attacks and the trace verifier monitors.
- **[`demo/`](https://github.com/input-output-hk/ouroboros-leios/tree/main/demo)** — patched-`cardano-node` networks: `burst` (Leios–Praos interference reproduction), `proto-devnet`, `dozen-devnet` (3 producers × 3 relays for throughput at realistic peer degree).
- **[`antithesis/`](https://github.com/input-output-hk/ouroboros-leios/tree/main/antithesis)** — Docker Compose stacks (proto-devnet; ImmDB mock) for [Antithesis](https://antithesis.com/) deterministic-hypervisor simulation testing of Leios consensus: real code, simulated/perturbed environment, deterministic replay.
- **[`network-mux` Leios demo](https://github.com/IntersectMBO/ouroboros-network/blob/main/network-mux/demo/mux-leios-demo.hs)** in ouroboros-network — a real-kernel multiplexer micro-testbed, not just a demo: a two-process client/server pair driving the production `Network.Mux` over real sockets, with companion scripts that build Linux network namespaces and `tc`-shape links (100 Mbit / 10 ms), contending ~12 MB Leios-class blocks against Praos-class blocks, with eventlog capture. Closer in kind to entry 6 than to a footnote.

---

## Supporting models and inputs

- **Topologies:** [`ouroboros-leios/data/simulation/`](https://github.com/input-output-hk/ouroboros-leios/tree/main/data/simulation) — shared by sim-rs and the Haskell sim: the 100-node reference (`topo-default-100.yaml`), mini-mainnet, and the **pseudo-mainnet** family (v1 at 10,000 nodes, the current v4 at 2,685; realistic stake distribution and pool count, two relays per producer, RIPE-Atlas-consistent latencies, Cardano-Foundation-consistent connectivity and geography). [`leios-tools`](https://github.com/input-output-hk/leios-tools) mirrors only `pseudo-mainnet/` and the config/schema. [`topology-checker/`](https://github.com/input-output-hk/ouroboros-leios/tree/main/topology-checker) and `topology-viewer/` validate and render them.
- **Empirical calibration data:** Cardano mainnet block/header propagation measurements, inter-datacenter bandwidth measurements, transaction statistics from epoch 350 onward, and the post-CIP measurement corpora — the basis for "simulation realism" sections of [Tech Report 2](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/technical-report-2.md).
- **Cryptographic timing:** [`crypto-benchmarks.rs/`](https://github.com/input-output-hk/ouroboros-leios/tree/main/crypto-benchmarks.rs) — BLS vote/certificate reference implementation and benchmarks; source of CPU-cost parameters used by the simulators.
- **Visualization:** the [web visualizer `ui/`](https://github.com/input-output-hk/ouroboros-leios/tree/main/ui) consumes traces from either simulator and supports live streaming via Loki; a hosted instance existed at `leios-simulation.cardano-scaling.org` (2024) ❓🤖 current availability unverified. Cost model at [leios.cardano-scaling.org/cost-estimator](https://leios.cardano-scaling.org/cost-estimator).
- **Experiment record:** [`analysis/sims/`](https://github.com/input-output-hk/ouroboros-leios/tree/main/analysis/sims) weekly notebooks (`2025wNN`) with matching "Simulation analysis leios-2025wNN" slide decks on Drive; a [simulation tutorial recording](https://drive.google.com/file/d/1Sn3W2-_CXVpYi787esuwjkjVutKyOHuZ/view) (Nov 2025).
- **Analytic threads (not yet artifacts):** the Karl Knutsson / Marcin Wójtowicz BitTorrent-grounded egress-stability analysis (Sept 2026); Giorgos Panagiotakos's probabilistic inter-continental diffusion arguments (May 2026 thread); the 25%-avalanche formulation (Nick Frisby). Documented so far only in Slack and PR #880 memos.

## Cross-simulator validation record

- Rust vs Haskell IB-diffusion comparisons on pseudo-mainnet and mini-mainnet (2025 weekly experiments, `analysis/sims/2025w23`–`w24`).
- Trace-verifier conformance of both simulators against the Agda spec (2025–2026), then of real nodes (Aug 2026).
- Haskell vs leios-peernet alignment attempt (Feb 2025): ~2× latency discrepancy, early bottleneck in the Java model; documented in Slack, not in a repo.
- ❓🤖 **SCRUTINY**: no cross-validation of "smol world," the Mininet test bed, or Piranha-as-simulator against sim-rs exists yet, as far as this pass found — a natural gap for this exploration effort to fill.

## Gaps and open questions

1. **AUEB simulator provenance** — obtain the code (or at least TECHREP2 and a methods description) from Spyros Voulgaris; establish its relationship to leios-peernet.
2. **No unified faithfulness assessment** — this catalog records claims; a systematic comparison (same topology, same workload, across sim-rs / smol world / Mininet test bed / testnet measurement) has not been done and is the obvious next experiment.
3. **Private repository access** — `leios-adversarial-tools` needs access granted before Piranha can be characterized first-hand.
4. **Unmerged artifacts** — PR #880 (Mininet test bed) and PR #5424 (smol world) are both **draft** PRs on branches, #5424 with no review activity at all; if abandoned, this catalog's links rot and the work risks being lost.
5. **Unlocated referenced work** — Nicolas Henin's analysis, the TECHREP2 report, and the Sept 2026 Linear Leios stability presentation slides.

## Sources

### Slack (internal, input-output-rnd workspace)

- [Motivating thread — "what network simulators do we have?" — #team-leios, 2026-09-16](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1789558993289409?thread_ts=1789558993.289409&cid=C074AHSKJF7) (Brian W. Bush, Sebastian Nagel, Dmitry Shtukenberg)
- [25% avalanche / AUEB reports thread — #team-leios, 2026-05-13..22](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1778692854742279?thread_ts=1778692854.742279&cid=C074AHSKJF7) (Frisby, Szamotulski, Panagiotakos, Wójtowicz, Knutsson, Nagel; TECHREP PDFs `F0B3YR7BAR3`, `F0B45RA27RA`)
- [Java simulator description — #team-leios, 2025-02-05](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1738764185839979) (William Wolff)
- [Java simulator assessment — DM, 2025-02-21 (internal)](https://input-output-rnd.slack.com/archives/D07TDP6GATF/p1740144145525689) (Brian W. Bush)
- [Linear Leios egress-stability high-five — #high-fives, 2026-09-07](https://input-output-rnd.slack.com/archives/C011H74QZNF/p1788799962666299) (Marcin Szamotulski re Wójtowicz & Knutsson)
- [Trace verifier on live nodes — #formal-methods, 2026-08-20](https://input-output-rnd.slack.com/archives/C4WQQKUU9/p1787228866642259) (James Chapman)
- [EB Trojan Horse / Piranha — #team-leios, 2026-08-27](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1787863719890129) (Christopher Tilt; also Nagel replies 2026-08-12, 08-28)
- [Nagel on "built something similar" to sim-rs — #team-leios, 2026-09-14](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1789410308296569?thread_ts=1789389089.010549&cid=C074AHSKJF7)
- [Leios testnet launch — #announcements, 2026-06-23](https://input-output-rnd.slack.com/archives/C0XL53C78/p1782225761886479)

### GitHub

- [ouroboros-leios — README and directories](https://github.com/input-output-hk/ouroboros-leios) — simulation/, delta_q/, analysis/, post-cip/, demo/, antithesis/, leios-trace-verifier/, crypto-benchmarks.rs/, topology-checker/
- [leios-tools — README, sim-rs (README, IMPLEMENTATION.md, docs/tcp-modelling.md), net-rs, shared-rs, specs/](https://github.com/input-output-hk/leios-tools)
- [leios-peernet](https://github.com/input-output-hk/leios-peernet) and [PeerNet](https://github.com/PeerNet/PeerNet)
- [ouroboros-leios-formal-spec](https://github.com/input-output-hk/ouroboros-leios-formal-spec)
- [PR #880 — Mininet LeiosFetch test bed](https://github.com/input-output-hk/ouroboros-leios/pull/880) (README.md, DESIGN.md, IDEA memos on branch `nfrisby/april2026-checkpoint`)
- [IntersectMBO/ouroboros-network#5424 — "smol world"](https://github.com/IntersectMBO/ouroboros-network/pull/5424)
- [CIP-0164](https://github.com/cardano-foundation/CIPs/pull/1078)

### Confluence (internal, input-output.atlassian.net)

- [Leios Team develops safe and live trace verifier — NC blog, 2026-08-20](https://input-output.atlassian.net/wiki/spaces/NC/blog/2026/08/20/6219563009/Leios+Team+develops+safe+and+live+trace+verifier+for+protocol+conformance+testing)
- [Experience report on Jolteon, Peras, and Leios](https://input-output.atlassian.net/wiki/spaces/Innovation/pages/5234327587/Experience+report+on+Jolteon+Peras+and+Leios)
- [arc-leios — Analyze and model Linear Leios](https://input-output.atlassian.net/wiki/spaces/Innovation/pages/5350621236/arc-leios-Analyze+and+model+Linear+Leios)
- [Leios Protocol weekly reports (IOE space), e.g. 2025.07.24](https://input-output.atlassian.net/wiki/spaces/IOE/pages/5183733761/Leios+Protocol+-+2025.07.24)

### Google Drive (internal)

- [Simulation analysis slide decks, leios-2025w16..w29 (Brian W. Bush)](https://docs.google.com/presentation/d/1WjoRs-6t6fFsSjC1BiuYW7qaI5Y5ponU9EH6X6ZvQdM/edit) (w24 shown; series in same folder)
- [Leios simulation tutorial — recording + notes, 2025-11-04](https://docs.google.com/document/d/1Va7x1BkBQEieE4QiswAP0TU8Ca6jM5l7Y7yTk84KMSg/edit)
- [Java (PeerNet) simulation plots folder (William Wolff)](https://drive.google.com/drive/folders/1FquVrKshA8btSYnmbllg4CvsB98XZTXH)
- [SundaeSwap SOW for Rust simulation, 2024-08 (internal)](https://drive.google.com/file/d/1whT52mHpWpU2MBShZdvtb7iiVcSuKk1N/view)

### External

- [King RTT dataset paper](https://www.gribble.org/papers/king.pdf)
- [ΔQSD paper](https://www.preprints.org/manuscript/202112.0132/v3)
- [Leios research paper — High-Throughput Blockchain Consensus under Realistic Network Assumptions](https://iohk.io/en/research/library/papers/high-throughput-blockchain-consensus-under-realistic-network-assumptions/)
- [Spyros Voulgaris — AUEB page](https://acropolis.aueb.gr/~spyros/)
