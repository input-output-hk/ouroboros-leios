# Deep Dive 6: Mininet LeiosFetch Test Bed (PR #880)

**Created:** 2026-09-16
**Status:** Draft for review.
**Provenance:** 🤖 (LLM-generated from source and document reading, pending human review)
**Read at:** [`ouroboros-leios` PR #880](https://github.com/input-output-hk/ouroboros-leios/pull/880), branch `nfrisby/april2026-checkpoint`, directory `docs/targeted-design-investigations/mininet-LeiosFetch-test-bed/` (~9,700 lines: C node + Python schedulers + Mininet runner + seven design/analysis documents).
**Parent entry:** [catalog § Mininet LeiosFetch test bed](../leios-simulation-model-catalog.md#6-mininet-leiosfetch-test-bed)

Nicolas Frisby's **network emulation** (real Linux kernel TCP, not simulated transport) of LeiosFetch-style large-payload pull diffusion, built to design and evaluate **fetch-scheduling policy** — what to request from whom, and when — for 12 MB EB closures. Distinct in kind from every simulator in the catalog: the transport is real; the *policy* is the model.

---

## 1. Architecture

- **Network** (`mininet_topo.py`, `topo_config.py`): each topology edge is materialized as a **middlebox host** between the endpoints (`A — veth — middlebox — veth — B`); the middlebox owns the bottleneck, shaping egress with **fq_codel AQM**, while propagation delay sits on the host-side legs. Nodes carry identity IPs (`10.0.0.<id>/32` on loopback) routed via the right middlebox. Runs inside a privileged Docker container (`Dockerfile.mininet`). `NOTES.md` documents why this middlebox split is necessary and a set of hard-won kernel-TCP facts (initcwnd 14 kB vs tuned 300 kB transfer-time predictions; receive-buffer tuning; **ssthresh carryover across transfers on persistent connections** — the same phenomenon smol world models as its warm-idle lever).
- **Node** (`node.c` + `diffusion.c`, C, epoll event loop): a **two-phase pull protocol** — Phase 1 diffuses a content-addressed *manifest* atomically (OFFER/REQUEST/RESPONSE_MANIFEST); Phase 2 diffuses the payload at *component* level with **sparse bitmap requests** and **chunk cancellation** (`MSG_CANCEL_CHUNK`/`CANCELED_RESPONSE`), both phases sharing a `NEXT_OFFER` pipelining-credit pool; everything keyed by the SHA-256 of the manifest. This is a LeiosFetch-*shaped* design study (bitmap addressing, pull-based, offer/fetch split), not the CIP wire protocol.
- **Policy brain** (`FetchScheduler.py` and siblings): the scheduler is a **pure state machine** `(state, event) → (state, [actions])` — no I/O — embedded in the C node via CPython. `PLAN.md` is explicit that the Python file is simultaneously the **reference specification** and the executable prototype, testable with synthetic traces and property-based tests, iterable against real network behavior without touching C. (An architecture worth stealing for any policy work we do.)

## 2. The scheduling result (`DESIGN.md`, `ANALYSIS.md`)

Peer lifecycle: **Probationary** (2 chunks) → **Probing** (a 2 MB burst to drive the peer's TCP past slow start while a C-side estimator watches arrival rate until it plateaus → `BdpEstimated`) → **Normal**, with **Snubbing** (exponential backoff) on stall (no delivery within 5× expected chunk time). With per-peer bandwidth-delay-product (BDP) estimates, pipeline depth is calibrated per peer, rebalancing has a throughput signal, and hedging is *thresholded* — duplicated only for the cheap final chunks.

Head-to-head on `topo-8-1` (8 heterogeneous sources co-injecting two 12 MB payloads into one sink):

| | OnePeer | FullHedge | **Fetch** |
|---|---|---|---|
| Payload latency | ~10.1 s | ~3.1 s | **~2.0–2.3 s** |
| Total wire MB | **52.7** (floor) | 96.9 | 59.9 |

Fetch beats FullHedge on *both* axes and pays ~14% over the bandwidth floor for a 5× latency win over OnePeer. **Load-bearing caveat, stated in `ANALYSIS.md`:** the BDP estimator in these runs is **stubbed with an oracle** reading the topology config; `bdp_demo/` demonstrates why real receiver-side BDP measurement on a bursty stream is non-trivial. The numbers are the best case "given you can estimate BDP."

**Adversarial (tarpit) analysis** is explicit: OnePeer fails catastrophically (stranded on a tarpit first-offerer), FullHedge is immune by construction, Fetch is bounded — ~one BDP of wasted work plus one snub-reassign cycle (~hundreds of ms) per tarpit, compounding with colluding tarpits; the stall threshold is the resilience-vs-tolerance knob. Content integrity is out of scope for scheduling (manifest hashes catch lies on first bytes).

## 3. Supporting documents

- **`PRIOR_ART.md`** frames the problem abstractly (online scheduling of granular jobs over ~25 heterogeneous, unreliable, partially adversarial, churning workers whose capacity is shared with unobservable other schedulers) and surveys: Dean & Barroso hedged/tied requests, multi-armed bandits with TCP_INFO side information, power-of-two-choices, and **BitTorrent piece selection** (incl. a paper showing 2–3× faster-than-BitTorrent tail completion) — the same literature family grounding the Wójtowicz/Knutsson egress-stability theory (entry 5), suggesting shared intellectual lineage.
- **`loss-model-memo.md`**: a decomposition of wired-backbone loss (AQM background drops ~10⁻⁵–10⁻⁴ uniform dominate; microbursts, BGP repathing, PHY ≈ 0) concluding uniform low-p loss is the right emulation model, and noting single-flow CUBIC steady-state throughput is set by RTT and loss, not link capacity — the calibration argument behind both this bed's link parameters and, plausibly, smol world's Gilbert–Elliott settings ❓🤖.
- **`IDEA-NeighborhoodFarPeers.md`** (with its policy Appendix) and **`IDEA-EbClosureMinimumAge.md`** — the Linear Leios design memos that grew out of the 25%-avalanche thread and the AUEB reports (entry 4).
- **Inputs**: alongside the star topologies, three **`topo-small-world*.json`** variants (with/without loss and jitter) — so small-world experiments exist here too, converging with entry 5's topology philosophy.

## 4. Mempool and transaction caches

**No mempool, no transactions.** Payloads are opaque component sets injected by schedule files. Per-node caches: the received-component store (content-addressed by manifest hash; serves later requesters for the run's duration — whole-run residence, no aging) and the kernel's own socket buffers — which are *real*, and whose unrecoverable committed bytes are precisely what FullHedge's cancellation cannot claw back. The relevance to our mempool study is indirect but sharp: this bed measures the **fetch side of EB-closure write-back** (what smol world's `plantClosure` abstracts as instantaneous planting) with real transport.

## 5. Assessment against the four catalog dimensions

- **Faithfulness.** Transport: perfect by construction (real kernel TCP/CUBIC through real qdiscs). Protocol: LeiosFetch-shaped but bespoke; topologies small (8–12 nodes); payload injection scripted. The oracle-stubbed BDP estimator is the main internal-validity caveat.
- **Status.** Draft PR, April-2026 checkpoint, discussion through May 2026; no commits since. The IDEA memos remain live design references.
- **Scope.** Fetch-policy design space for large-payload pull diffusion, with quantified latency/bandwidth/adversarial trade-offs.
- **Performance.** Real-time emulation (a 50 s scenario takes 50 s), so scale is bounded by kernel/namespace capacity — policy evaluation, not network-wide sweeps.

## 6. Follow-up questions

1. **Replace the BDP oracle** with the probe-based estimator and re-run — the single result most needed before Fetch's numbers inform the real LeiosFetch design.
2. Run the **small-world input topologies** (present but unreported in `ANALYSIS.md` ❓🤖 — no results found in the tree) and compare against smol world on matched parameters: the natural transport-calibration experiment (real CUBIC vs modeled CUBIC vs sim-rs envelope).
3. Relation to production: does the `net-rs` LeiosFetch implementation (entry 7) adopt any of Fetch's policy (probation/probing/snubbing)? net-rs's "RTT-based fetch peer selection" suggests a simpler policy today.
4. Whether Frisby's checkpoint gets merged or the memos extracted — link rot risk flagged in the catalog gaps.

## Sources

- Read at PR #880 (`nfrisby/april2026-checkpoint`): `README.md`, `DESIGN.md`, `ANALYSIS.md`, `PLAN.md`, `PRIOR_ART.md`, `NOTES.md`, `loss-model-memo.md`, `input.json.md`, `IDEA-*.md`, `node.c`, `diffusion.c`, `FetchScheduler.py`, `FullHedgeScheduler.py`, `OnePeerScheduler.py`, `scheduler_bridge.c`, `mininet_topo.py`, `bdp_demo/`, `inputfiles/`
- [Catalog entry 6](../leios-simulation-model-catalog.md#6-mininet-leiosfetch-test-bed); [Dive 4 (AUEB)](./04-aueb-network-modeling.md) and [Dive 5 (smol world)](./05-smol-world.md) for the cross-links
