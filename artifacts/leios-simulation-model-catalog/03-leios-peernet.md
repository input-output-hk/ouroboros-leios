# Deep Dive 3: leios-peernet (Java / PeerNet)

**Created:** 2026-09-16
**Status:** Draft for review.
**Provenance:** 🤖 (LLM-generated from source-code reading, pending human review)
**Read at:** [`input-output-hk/leios-peernet`](https://github.com/input-output-hk/leios-peernet) (private) commit `972fa8410d1b9711f3e816ce31f6a414f1db6632`; [PeerNet framework](https://github.com/PeerNet/PeerNet) cloned separately (the submodule pin uses an SSH URL).
**Parent entry:** [catalog § leios-peernet](../leios-simulation-model-catalog.md#3-leios-peernet-java--peernet)

Spyros Voulgaris's (AUEB) event-driven Java simulator of Leios-style block dissemination over close/random (C/R) overlays, built on his PeerNet framework. ~2,800 lines of Java over PeerNet's engine. Dormant since 2025-02-21. Historically important for two reasons: it is the direct code ancestor of the AUEB technical-report vocabulary (`CxRy` policies, "Cougar" overlays — see catalog entry 4), and its freshest-first, one-upload-at-a-time bandwidth discipline anticipates diffusion policies the main simulators later took up.

---

## 1. What it simulates

A single undifferentiated **block** type (no RB/IB/EB/vote distinction, no transactions), disseminated header-first over a static overlay:

- **Generation** (`BlockGeneration`): every `MINING_PERIOD` (default 0.1 s, i.e. 10 blk/s) a uniformly random node with ≥2 downstream peers "mines" the next block, from a fixed-seed RNG (deterministic miner sequence across runs). A Bitcoin-rate exponential variant exists (`BlockGenerationBitcoinRate`). No stake, no lottery, no forks — block IDs are a global counter.
- **Dissemination** (`DisseminationBase` and subclasses): header → validate (`TH`, default 0 ms) → body request → body → validate (`TB`, default 45 ms) → forward. A `header_only` mode ships header+body together. `body_requests` (default 4) requests the body from up to N upstream announcers.
  - **`LeiosMulti`** (the configured default): adds upload-bandwidth serialization — a node uploads **one body at a time** (`uploadThrottledTill = now + block_size/bandwidth`), queues further requests, and serves the queue **freshest-first among peers not currently busy downloading**; receivers likewise download one body at a time (a shared `BusyDownloading` table — a global-knowledge simplification no real node has). Request **cancellation** on late arrivals is half-implemented: handled on receipt, but the sending of cancel messages is commented out.
  - **`LeiosSingle`**: single body request, no bandwidth queueing.
  - **`Cougar`**: dissemination over a static overlay, "no scoring, no calibration rounds — the basic Cougar model" — the code-level tie to the AUEB overlay research lineage.
- **Overlay** (`InitializerCR`): each node gets `C` close + `R` random links (default C0R4, undirected), the exact `CxRy` vocabulary of the AUEB TECHREPs; alternatives in config (commented): a static topology file, a `crsDegrees` wiring with push/subscription edge orientations.

## 2. Network model

Two transports, both **latency-multiple** models — there is no explicit per-link bandwidth/serialization on the wire (bandwidth appears only as `LeiosMulti`'s upload throttle):

- **`TransportLeios`** / **`TransportDeltaQ`**: body transfer time = one-way latency × (1 + 2·`extra_tcp_trips`) — TCP round trips approximated as extra latency multiples. `TransportDeltaQ` carries a **ΔQ-derived lookup table** (transfer times for 5 KB–2000 KB bodies at 150 ms latency: 0.150 s → 5.253 s) — a hard cap at 2 MB bodies — though the scale-by-size application is commented out in both transports at this commit ❓🤖 (so as committed, body size affects only the upload throttle, not wire time).
- **Latency**: uniform (`LATENCY` = 10 ms; `SPOT_LATENCY` = 2 ms same-location) via PeerNet's `UniformRandomTransport`, or a real RTT matrix via `MatrixParser` — the config references WonderNetwork one-way latencies (2022-02-08) and an `iohk_testbed_latencies.dat`, but **no latency data files are present in the repository**; the active configuration uses the uniform transport.
- PeerNet engine modes: SIM (event-driven), EMU (thread-per-protocol), NET (real sockets), COORDINATOR — only SIM is exercised here (`engine.mode sim`; the transports assert SIM).

## 3. Mempool and transaction caches

**No transactions, no mempool.** The per-node caches are three unbounded `HashSet<Integer>`s — `receivedHeaders`, `receivedBodies`, `validatedBodies` — plus a `bodiesRequested` count map and the transient `bodySendQueue`. **Residence: the entire run** (nothing is ever evicted; runs are short — 500 blocks default — so this is a non-issue at design scale but part of why high block rates blow up). The header set doubles as announcement dedup, as in sim-rs's `txs` store.

## 4. Outputs and analysis pipeline

Progress and results go to stdout as JSON events — `{"event":"generate",...}` / `{"event":"receive", block, time, node, hops}` — the logging added in Feb 2025 to make cross-simulator comparison possible (the original logs were insufficient). `analysis/` holds a MongoDB ingestion script (`ingest.js`) that reshapes these into a `rawIbs`/trace-like schema (hardcoded 100 KB size literal), an `exploration.ipynb`, and config snapshots (`original.cfg`, `default.cfg`); `plotall.sh`/`plots.gpi` drive gnuplot. Delivery-latency percentiles and hop counts are the headline metrics (`Stats`).

## 5. Faithfulness, status, performance

- **Faithfulness.** Coarsest protocol model in the catalog: one block class, no stochastic production/sizes, no Praos, no votes, no adversary, header/body validation as fixed delays, global busy-state knowledge, and (as committed) wire time insensitive to body size. Its value was never protocol fidelity but **overlay-policy comparison** (C/R mixes, freshest-first upload discipline) — the same questions the AUEB reports answer with their newer in-house simulator.
- **Status.** Dormant since 2025-02-21; superseded for IOG purposes per the Feb-2025 assessment (block latencies ~2× the Haskell sim under aligned configs; breakdown between 5–10 blk/s; hours per run at high rates). The Feb-2025 note "topology … not readable from disk" is *almost* right: a static-topology initializer exists in the config but is commented out and its data file absent ❓ untested.
- **Performance.** Single-threaded Java event loop; fine at 1,000 nodes × 10 blk/s × small blocks, scales poorly beyond (quadratic-or-worse observed).

## 6. Follow-up questions

1. The commented-out ΔQ size-scaling (`l * scale / 0.150`) suggests an abandoned experiment in table-driven ΔQ transports — worth asking Spyros whether the in-house simulator (catalog entry 4) is this design completed, which would settle the entry-3/entry-4 lineage question.
2. The missing latency matrices (`wondernetwork_…`, `iohk_testbed_latencies.dat`) presumably exist on AUEB machines; recovering them would make any historical reproduction possible.
3. If we ever want PeerNet's EMU/NET modes (thread-per-protocol / real sockets) for small live experiments, this is the only artifact in the catalog that has them — but nothing here has ever exercised them.

## Sources

- Source read at `leios-peernet@972fa84`: `Leios/src/prot/{DisseminationBase, LeiosMulti, LeiosSingle, Cougar, InitializerCR}.java`, `Leios/src/base/{BlockGeneration, BlockGenerationBitcoinRate, TransportLeios, TransportDeltaQ, TransportBody, Stats}.java`, `Leios/leios.cfg`, `Makefile`, `simulate.sh`, `analysis/{ingest.js, exploration.ipynb}`
- [PeerNet framework](https://github.com/PeerNet/PeerNet) (Spyros Voulgaris, 2012–) — `Engine` modes
- [Feb-2025 description (W. Wolff) and assessment (B. Bush) — Slack, cited in the catalog entry](../leios-simulation-model-catalog.md#3-leios-peernet-java--peernet)
- [Catalog entry 4 — AUEB reports](../leios-simulation-model-catalog.md#4-aueb-in-house-network-simulator-spyros-voulgaris) (CxRy / Cougar vocabulary continuity)
