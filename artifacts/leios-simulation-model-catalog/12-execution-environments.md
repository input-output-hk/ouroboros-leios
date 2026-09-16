# Deep Dive 12: Execution Environments (Testnet, Devnets, Antithesis)

**Created:** 2026-09-16
**Status:** Draft for review.
**Provenance:** 🤖 (LLM-generated from source and document reading, pending human review)
**Read at:** [`ouroboros-leios`](https://github.com/input-output-hk/ouroboros-leios) @ `11be715` — `testnet/`, `demo/{burst,proto-devnet,dozen-devnet}/`, `antithesis/`; `network-mux/demo/` at `IntersectMBO/ouroboros-network` main (read in the verification pass).
**Parent entry:** [catalog § Execution environments](../leios-simulation-model-catalog.md#12-execution-environments-testnet-devnets-antithesis)

Not simulators but the reference points faithfulness is measured against — real Leios-patched `cardano-node`s in five packagings, from a one-command testnet relay to a deterministic-hypervisor test rig. The dive's key finding for our purposes: **the devnets already ship the mempool-alignment instrumentation** our study needs.

---

## 1. The environments

- **`testnet/` — public testnet relay**: a one-command (`nix run …#leios-testnet-relay`) non-block-producing relay joining `leios-node.play.dev.cardano.org`. Its README states the use cases exactly: smoke-testing locally built nodes against live traffic (ChainSync/BlockFetch/LeiosNotify/LeiosFetch interactions), reproducing testnet reports (db-analyser snapshots, log replay), and querying a live-chain follower. The lowest-friction way to put real Leios traffic in front of anything we build.
- **`demo/burst/` — protocol-burst interference scenario**: a mocked upstream (patched `immdb-server` speaking partial LeiosNotify/LeiosFetch — EBs and closures only) releases prepared Praos blocks on their slot schedule and **ten 12.5 MB EBs just before a Praos block's slot** — "akin to a (relatively minor) ATK-LeiosProtocolBurst attack" — so patched nodes diffuse Praos under maximal Leios load. The controlled-experiment form of the Leios-interferes-with-Praos question; deliberately networking-focused (minimal txs per EB to suppress CPU/heap effects).
- **`demo/proto-devnet/`** — three block-producing pools, full mesh, loaded by `tx-firehose`, with the **x-ray observability stack**: Grafana dashboards including `cardano-leios-diffusion` (see § 2), and two tx generators that **color their transactions** so mempool provenance is visible per node.
- **`demo/dozen-devnet/`** — 3 block producers × 3 private relays each, the nine relays fully meshed, one **network namespace per node with `tc` traffic shaping**. The README's topology rationale is itself a finding: *"node-to-node tx-submission is bounded per peer by the tx-submission credit window, so the number of upstream peers is a first-order term in how fast a node can take in transactions"* — three meshed nodes cannot show that; nine can. Every inter-pool tx/block crosses ≥ 2 relay hops. Includes `mempool-panes.sh` observers on producers and relays.
- **`antithesis/`** — the proto-devnet and an ImmDB mock (upstream/node0/downstream) as Docker Compose stacks for [Antithesis](https://antithesis.com/) deterministic-hypervisor testing — real node code, perturbed environment, deterministic replay — with an observability overlay, plus **Moog-compatible stacks** (Cardano Foundation's submission service; pre-built GHCR images, randomized tx-firehose) for actual Antithesis runs.
- **`network-mux` Leios demo** (ouroboros-network): the real-kernel mux micro-testbed — two processes driving production `Network.Mux` over sockets, netns + `tc` at 100 Mbit/10 ms, ~12 MB Leios-class vs Praos-class block contention, eventlog capture (characterized in the fact-check pass).

## 2. Mempool and transaction caches (standing section)

The mempool here is the **real `cardano-node` mempool** — bounded, ledger-revalidated on chain updates, fed by pull-based TxSubmission with per-peer credit windows (the dozen-devnet rationale above is the operational statement of that backpressure). What the dive adds is that **the observability for mempool-alignment questions already exists**:

- The `cardano-leios-diffusion` Grafana dashboard tracks the **LeiosTxCache funnel** — per EB: `txsInEb ≥ tracked ≥ acquired ≥ validated` — with the panel documentation noting these are *not* expected to approach 100% because "most of an EB's transactions are already in the node's mempool by the time the body arrives; the cache path only ever accounts for the remainder," and that the three lines sitting on top of each other (no attrition) is the healthy reading.
- A companion panel splits **where an EB's txs were found on body arrival**: mempool hit vs missed-both (never seen at all), with hit rate = (txsInEb − missedBoth)/txsInEb — noting the two questions ("needed full validation" vs "never seen") differ by about an order of magnitude. Backing metrics like `leios_logmetrics_diffusion_body_mempool_hits_total` come from the node's own telemetry.
- Colored tx generators + `mempool-panes.sh` make per-node mempool contents and provenance directly observable in the devnets.

**This is the real-world measurement of exactly the quantities our study's models predict**: the ΔQ π₁ (≈ missed-both rate), smol world's `overlapBytes` (≈ mempool-hit share, byte-weighted), and the hypergeometric overlap (dive 10). The prototype node also evidently implements the CIP **LeiosTxCache** (tracked/acquired/validated stages) — the production realization of the write-back mechanism that dives 5, 7, and 10 model in three different ways.

## 3. Assessment against the four catalog dimensions

- **Faithfulness.** Definitionally the reference — with the caveat that all five run *prototype* Leios patches, small topologies (3–12 nodes; the testnet somewhat larger), and synthetic workloads (`tx-firehose`); mainnet-scale topology and organic workload remain unrepresented anywhere.
- **Status.** All active; burst/dozen-devnet were 2025-10→2026 additions; Antithesis-via-Moog is the newest path.
- **Scope.** Praos-interference bursts, throughput at realistic peer degree, deterministic fault exploration, live-testnet smoke testing.
- **Performance.** Real time; scale bounded by machine (local netns stacks) or by the Antithesis/Moog service.

## 4. Follow-up questions

1. **Use the existing telemetry first**: before building anything, pull the LeiosTxCache-funnel and mempool-hit metrics from the *testnet* (not just devnets) — if those metrics are exported there, the first mempool-alignment dataset costs a Grafana query. Check with the P&T/testnet operators which nodes export `leios_logmetrics_*`.
2. The dozen-devnet is the right rig for **tx-submission credit-window experiments** (its README says so in as many words); a matched sim-rs/shared-consensus run against it would validate the simulated mempool intake path.
3. `demo/burst`'s ATK-LeiosProtocolBurst framing implies an attack taxonomy (cf. the ATK-002 document found on Drive); locate the taxonomy and map which ATKs have execution-environment reproductions vs only paper analyses ❓.
4. Whether Antithesis runs have produced findings yet (none found in this pass ❓) — worth asking before proposing new deterministic-testing work.

## Sources

- Read at `ouroboros-leios@11be715`: `testnet/README.md`, `demo/README.md`, `demo/burst/README.md`, `demo/proto-devnet/README.md` + `run.sh` + `config/dashboards/cardano-leios-diffusion.json` (panel documentation), `demo/dozen-devnet/README.md`, `antithesis/README.md`
- `network-mux/demo/mux-leios-demo.{hs,sh}` at IntersectMBO/ouroboros-network `main` (verification pass)
- Cross-links: [Dive 5](./05-smol-world.md), [Dive 7](./07-piranha-net-rs.md), [Dive 8](./08-deltaq-models.md), [Dive 10](./10-postcip-mempool-models.md) — the models whose quantities § 2's telemetry measures
- [Catalog entry 12](../leios-simulation-model-catalog.md#12-execution-environments-testnet-devnets-antithesis)
