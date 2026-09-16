# Deep Dive 1: sim-rs — the Rust Leios Simulator

**Created:** 2026-09-16
**Status:** Draft for review.
**Provenance:** 🤖 (LLM-generated from source-code reading, pending human review)
**Read at:** [`input-output-hk/leios-tools`](https://github.com/input-output-hk/leios-tools) commit `7b08aaad8aaf270e191fa4fa3759bc9196ede8ec`; results context from [`input-output-hk/ouroboros-leios`](https://github.com/input-output-hk/ouroboros-leios) commit `11be71594ef1d71db7917ced11ccd54795335c07`.
**Parent entry:** [catalog § sim-rs](../leios-simulation-model-catalog.md#1-sim-rs--the-rust-leios-simulator)

The actively maintained reference simulator for Ouroboros Leios: a virtual-time, actor-based discrete-event simulation of the full protocol — transactions, mempool, ranking blocks (RBs), endorser blocks (EBs), input blocks (IBs, for legacy variants), votes, and certificates — over an explicit network topology, emitting a typed event trace for downstream analysis, visualization, and conformance checking.

---

## 1. Identification

| | |
|---|---|
| Location | `leios-tools/sim-rs` (extracted 2026 from `ouroboros-leios/sim-rs` with history) |
| Crates | `sim-core` (engine + protocol logic), `sim-cli` (wrapper, stats, `gen-test-data`) |
| Shared deps | `shared-rs/consensus` (behavior-tree engine + shared consensus state machines), `shared-rs/tcp-model` (analytic TCP envelope), `shared-rs/bls` |
| Size | ~23,500 lines of Rust in `sim-rs` alone (largest: `config.rs` 2.4 k, `shared_consensus.rs` 2.3 k, `linear_leios.rs` 2.2 k, `leios.rs` 1.9 k) |
| Origin | Sundae Labs under a 2024 statement of work; IOG-maintained since |
| License / CI | GitHub Actions workflow `sim-rs.yaml` (build + test on Ubuntu) |

## 2. Architecture

**Actor system on a virtual clock.** Nodes (stake pools and relays), the network, and a global `TransactionProducer` are actors exchanging messages. A clock coordinator advances virtual time only when every actor is parked in `wait_until`/`wait_forever`, so no actor ever runs ahead; timestamp resolution is configurable (`timestamp-resolution-ms`, default 1 ns) — coarser resolution batches events into simultaneous groups and increases parallelism.

**Two execution engines** (`engine` parameter):

| Engine | Mechanism | Deterministic | Attacker support |
|---|---|---|---|
| `actor` (default) | Tokio multithreaded actors, virtual-clock barrier | No (ties resolved by scheduling) | Yes |
| `sequential` | Strict timestamp-ordered discrete-event loop; rayon parallelism *within* a timestep | Yes | No |

**Sharding** (both engines): nodes partition into groups simulated in parallel, synchronized by conservative message blocking derived from minimum inter-shard latencies. Five assignment strategies: `round-robin`, `zero-latency-clusters` (recommended), `geographic` (k-means), `min-latency-clusters` (agglomerative), `min-cut` (recursive bisection + Kernighan–Lin). The `turbo.yaml` preset (sequential, 6 shards, zero-latency clusters) is quoted at ~5× the default engine.

**Determinism beyond the engine.** Randomness is *stateless and context-derived*: every draw is a pure function of `(global_seed, context)`, deliberately mirroring Cardano's VRF (`vrf_output = f(key, nonce ‖ slot)`). There is no evolving per-node RNG state, so timing drift cannot desynchronize random decisions — non-determinism in the actor engine is confined to event *ordering*, not lottery outcomes. A "byte-equivalent event-stream determinism check" is a stated goal of the in-flight shared-consensus migration (W2.5 in `merge-shared-consensus-plan.md`).

**CPU model.** Nodes have configurable vCPU counts (topology `cpu-core-count`); protocol operations are modeled as CPU tasks with subtasks scheduled onto cores, with per-operation cost parameters (~30 `*-cpu-time-ms*` knobs: generation/validation/apply costs for TX/RB/IB/EB/votes/certs, constant + per-byte + per-tx terms). `CpuTaskScheduled`/`CpuTaskFinished` events expose queueing.

**Event stream.** 36 typed events (`sim-core/src/events.rs`): lifecycle triples (lottery-won / generated / sent / received) for each object class, TX loss and backlog events, CPU events, partition start/heal, per-slot markers. `sim-cli` post-processes into aggregate stats and a liveness view.

## 3. Protocol scope

**Seven variants** behind one `leios-variant` enum, sharing infrastructure but implemented in four modules:

| Variant | Module | Blocks | Notes |
|---|---|---|---|
| `short`, `full`, `full-without-ibs`, `full-with-tx-references` | `leios.rs` | IB/EB/RB/votes | Historical designs (config default is still `short`) |
| — Stracciatella | `stracciatella.rs` | EB/RB (EBs reference TXs and EBs) | Intermediate design, 2025 |
| `linear`, `linear-with-tx-references` | `linear_leios.rs` | RB-coupled EBs, votes, certs | **CIP-0164 track** |
| `shared-consensus` | `shared_consensus.rs` | (in migration) | Only the TX path is wired so far |

**Linear Leios detail** (`implementations/LINEAR_LEIOS.md` + code): every RB producer may mint an EB referenced by the RB header; a certificate for the parent RB's EB is embedded in the RB body once `3·Δ_hdr + L_vote + L_diff` has elapsed; RB headers diffuse separately from bodies; equivocation detection by waiting `3·Δ_hdr` before voting; a VRF lottery assigns per-node vote multiplicities; committee selection implements **wFA^LS** (`committee-selection-algorithm: wfa-ls`, stake-fraction threshold 0.95) with distinct persistent/non-persistent voter classes (separate generation/validation costs and bundle sizes); quorum by `vote-threshold` / `quorum-weight-fraction`. Three **EB propagation criteria** (`eb-received`, `txs-received`, `fully-valid`) let experiments move EB relaying earlier or later in validation — the knob behind the 2026 diffusion-vs-validation questions. Praos fallback is modeled (`praos-fallback-enabled`, `praos-chain-quality: 40`).

**Transactions and mempool.** Exponential inter-arrival and log-normal size distributions (configurable), per-TX shard assignment, an `input_id` for conflict modeling (`tx-conflict-fraction`), and overcollateralization factors. The mempool is characterized in depth in § 4; the migration plan's own description of the current one — "~600-line broken mempool with unbounded backlogs" — is a known-fidelity caveat.

**Diffusion abstraction.** All object classes use an announce → request → deliver pattern (approximating pull-based mini-protocols without state machines); IB headers/bodies split. Per-class diffusion strategies (`freshest-first` for IBs; `peer-order` for EBs/votes), windowed request caps, `relay-strategy` = request-from-first (default) or request-from-all, `multiplex-mini-protocols` toggle, EB max-age and relay-age limits, late-IB inclusion.

## 4. Mempool and transaction caches

The likely focus of upcoming study, so characterized in depth: the mempool proper (§ 4.1–4.3), then every other place TX bodies are cached and how long they stay (§ 4.5). Three generations of mempool coexist in the codebase; which one runs depends on `leios-variant`.

### 4.1 `linear`/`linear-with-tx-references` — `Mempool` in `linear_leios.rs`

**Data structure.** A `BTreeMap<u64, Arc<Transaction>>` keyed by a monotonic insertion counter (so iteration order = admission order), plus a `HashSet` of occupied `input_id`s (the one-input conflict model), a `HashSet` of member TX ids, and **two FIFO backlogs** (`VecDeque`): one for locally generated TXs, one for peer-received TXs. Capacity is a *byte* cap on the main pool (`leios-mempool-size-bytes`, **default `null` = unbounded**) and optional *count* caps on each backlog (`tx-generated-backlog-max-size`, `tx-peer-backlog-max-size`, **both default `null` = unbounded**) — the configuration shape behind the maintainers' own "unbounded backlogs" complaint.

**Network face (admission path).** TX diffusion is announce → request → deliver per peer, with per-TX state (`Pending`/`Received`) deduplicating requests; under `request-from-first` (default) a TX is requested from only the first announcer, under `request-from-all` from every announcer until delivery. A received body is charged a CPU validation task (`tx-validation-cpu-time-ms` + per-byte term) *before* admission; locally generated TXs skip network but not the backlog check. After admission the node re-announces the TX to all its consumers, and TX bodies arriving via **EB-body fetch** (`RequestEBTxs`/`EBTxs`, bitmap-addressed as in LeiosFetch) are fed through the *same* validation-and-admission pipeline, then re-announced — EB fetching backfills the mempool.

**Admission rules** (in order, `try_add_tx_to_mempool`):
1. *On-chain conflict:* the node lazily resolves a **ledger spent-input set** by walking the chain back from its current tip (cached per tip block, accumulated incrementally), including TXs in RB bodies and in *received* on-chain-endorsed EBs. A TX whose `input_id` is already spent is rejected outright.
2. *Capacity:* if the byte cap would be exceeded, the TX goes to the local or peer backlog (FIFO); a full peer backlog **drops** the TX (`TXLost`/`PeerBacklogFull` event). Local generation stops when the local backlog is full (`TXLost`/`GeneratedBacklogFull`).
3. *Mempool conflict:* a TX whose `input_id` collides with a pool member is returned as "backlogged" but in fact **silently dropped** — it is inserted into neither the pool nor a backlog. (A misnomer worth knowing when reading `InsertResult`.)

**Drainage.**
- *Into RBs:* only on the Praos-fallback path (no certificate available): `sample_from_mempool(max_block_size, remove=true)` — TXs leave the pool at inclusion time, optimistically.
- *Into EBs:* `sample_from_mempool(max_eb_size, remove=false)` — EB inclusion does **not** remove TXs; they remain until the EB (or a competing RB) lands on-chain.
- *On-chain observation:* when RB/certified-EB TXs are seen, `remove_conflicting_txs` removes by **input id** — the included TX *and* everything conflicting with it — from the pool and both backlogs.
- *Promotion:* every removal triggers FIFO promotion from backlogs (local first, then peer), skipping now-conflicting entries; each promoted TX is announced to peers.
- *Safety rule:* a producer that has on-chain EBs it has not fully received produces an **empty block** rather than risk including conflicting TXs.
- *Aging:* `linear-tx-max-age-slots` prunes old TX *bodies* from the node's TX store only once they are no longer in the mempool (pool members are always retrievable).

**Selection policy** (`leios-mempool-sampling-strategy`): `ordered-by-id` (default) fills oldest-first (FIFO); `random` shuffles candidates with a context-derived deterministic shuffle keyed by (node, slot, call). The fill loop **breaks at the first TX that does not fit** — a large TX at the head blocks the remainder (no skip-and-continue), so head-of-line blocking by size is a modeled (perhaps unintended) behavior. There are **no fees and no priority ordering, no replacement policy**.

**What "re-validation" means here.** There is no ledger re-execution: validity ≡ input-conflict-freedom against (a) the spent-input set of the node's current chain view and (b) current pool members. Chain switches re-resolve the spent-set from scratch for the new tip (previous resolutions cached per block id). CPU is charged once at reception, not on re-checks.

### 4.2 Classic variants (`short`/`full`/…, `leios.rs`) and Stracciatella

**Two parallel mempools per node** — `praos.mempool` and `leios.mempool`, both plain `BTreeMap<TransactionId, Arc<Transaction>>` (no byte cap, no backlogs, no conflict sets). Praos block production drains `praos.mempool` FIFO; IB/EB production samples the Leios pool; an endorsement removes endorsed TXs from both. `leios-mempool-aggressive-pruning` (used only by these modules) additionally prunes on earlier evidence. These are the mempools behind all 2025 experiment results.

### 4.3 Target design — `shared-rs/consensus::MempoolState` (sans-IO)

The migration target (and what net-rs/Piranha already drive): **two compartments under one roof** — `txs`, a FIFO free pool in arrival order, drained for the next RB body and advertised via TxSubmission; and `eb_pinned`, bodies that left the free pool by being drained into an EB but stay retrievable while the EB is unsettled, with a slot-window retention (default 100 slots) pruned on every EB observation. Count-capacity bound with **oldest-evicted-on-overflow** (telemetry event carries the evicted id). **Per-peer advertised sets** (lazily seeded, pruned with the pool) prevent re-announcing a TX to the same peer — a real TxSubmission mechanism absent from 4.1. Validation crosses the crate boundary as an effect/response pair (`ValidateTx` → `on_tx_validated`/`on_tx_validation_failed` → `TxRejected`), with locally generated TXs admitted directly. Serves the LeiosFetch `BlockTxs` server and the CIP-0164 `MissingTX` voting predicate via lookups spanning both compartments. Behavior hooks (`TxWithholdingPolicy`) integrate adversarial TX handling. As of this reading, sim-rs's `shared-consensus` variant exercises exactly this mempool end-to-end (TX path only).

### 4.4 TX caches beyond the mempool, and residence times

TX bodies are `Arc`-shared within a node, so the "caches" below hold pointers into one allocation per TX; a body is freed only when *every* cache below has released it. Residence times, `linear*` variants:

| Cache | Contents | Serves | Residence / eviction |
|---|---|---|---|
| `txs` store (`BTreeMap<TxId, TransactionView>`) | Every TX ever seen: `Pending` (announced, awaiting body — this doubles as the announcement-dedup cache) or `Received` (full body + first-seen slot) | `RequestTx` server, mempool lookups, EB completion | **Forever by default** (`linear-tx-max-age-slots: null`). When set, pruned once `current_slot − seen_slot > max_age` *and* the TX is no longer in the mempool. Experiment overlays bound it tightly: `linear.yaml` 23 slots, `memory-limit.yaml` 24 slots |
| Mempool pool + backlogs | § 4.1 | RB/EB fill | Until on-chain-conflict removal, inclusion (RB), or backlog promotion/drop; byte/count caps default **unbounded** (`mainnet.yaml` keeps the pool unbounded; `memory-limit.yaml` caps backlogs at 10 local / 10,000 peer) |
| `eb.txs` inside each received EB | Full body list per EB, in EB order | `RequestEBTxs` (bitmap-addressed LeiosFetch analog), vote `MissingTX` predicate | Until the EB is pruned: only when a **strictly newer EB has been endorsed on-chain**, and the EB is neither mid-CPU-validation nor an incomplete on-chain EB. If no newer EB certifies, old EBs (and their TX lists) live forever |
| `missing_txs` reverse index | TxId → EBs awaiting that body | EB completion gating | Until the body arrives or the EB is pruned |
| `ledger_state` spent-input set | `input_id` of every on-chain TX from the start of the run | Admission rule 1, § 4.1 | **Grows monotonically for the whole run** (one cached tip at a time; recomputation walks the full chain on reorg) |
| Vote store (`votes_by_eb`, `votes`) | Vote bundles per EB | Quorum counting | Same supersession rule as EBs; `pruned_ebs` tombstone ids grow forever |

Two cross-simulator caveats surfaced here: (a) **`cleanup-policies` is a no-op in sim-rs** — the key ships in `config.default.yaml` and the schema (`["cleanup-expired-vote"]`, and `sim-cli/configs/mainnet.yaml` sets it) but is referenced nowhere in the Rust source; it is presumably honored only by the Haskell simulator (verify in the row-2 dive). (b) Under the **default** config every TX-body cache is unbounded — memory is bounded only by run length; the periodic memory report (§ 4.5) exists precisely because of this.

In the shared-consensus target (§ 4.3) the cache story tightens: the free pool is count-capped with FIFO eviction, EB-pinned bodies carry an explicit **100-slot retention window** pruned on every EB observation, and per-peer advertised sets are pruned alongside the pool.

### 4.5 Mempool observability

Events: `TXGenerated/Sent/Received/Lost` (with loss reasons), `TXLocalBacklogMax`/`TXPeerBacklogMax` high-water marks; a periodic memory report prints pool entries/bytes and backlog fill against caps. The Aug 2026 telemetry work (#69, #80, #85) extended mempool-related aggregation.

## 5. Network model

Three per-link transport regimes, dispatched by `ConnectionKind::from_config` (fully documented in [`docs/tcp-modelling.md`](https://github.com/input-output-hk/leios-tools/blob/main/sim-rs/docs/tcp-modelling.md), added July 2026):

1. **TCP congestion-window model** — *the effective default* (`tcp-congestion-control: true` in the shipped config): a direct port of the Haskell `ModelTCP.hs`; slow start with initial window 10 × 1460-byte segments (RFC 6928), receiver window auto-sized to `max(2·BDP, 10·MSS)`, RFC 6298 idle reset. **No loss, retransmission, or delayed ACKs.** Caveat: a link with unspecified bandwidth silently gets a ~8 Mbit/s default cap under this regime, but is *uncapped* under the Simple regime — an asymmetry worth remembering when editing topologies.
2. **Simple** — latency + fair bandwidth sharing across active mini-protocols; the fallback when TCP is off.
3. **Analytic envelope** (`shared-rs/tcp-model`) — cold-start ramp, idle reset, and loss-as-one-RTO-stall with AIMD-style recovery, layered *onto* Simple; mutually exclusive with regime 1; **no shipped config exercises it** (unit tests only). It is the only regime that models loss at all.

**Network partitions** (2026 feature): time-windowed scenario overlays cut and heal sets of directed edges (`set-to-set` with direction control, `isolate`), kept in separate overlay files so a config runs with/without the partition; `scripts/gen-partition.py` generates continent-scale cuts from topology country metadata. Emits `PartitionStarted`/`PartitionHealed`.

## 6. Adversarial capabilities

Three layers, all actor-engine-only:

1. **Built-in attack configs** — `late-eb-attack` and `late-tx-attack` blocks (attacker `NodeSelection`, attack probability, propagation delay); a dedicated `EBWithholdingAttacker` actor coordinates delayed EB dissemination across colluding nodes (`linear_leios/attackers.rs`). Shipped example: `parameters/late-eb-attack.yaml`, `lazy-20pct.yaml`.
2. **Per-node `adversarial` / `behaviours` flags** in the topology.
3. **Behavior trees** (`consensus-behaviours`): per-node TOML behavior-tree configs interpreted by `shared-rs/consensus` — the same engine and action vocabulary Piranha uses (announce equivocation/flooding/size-lies/slot-skew, fake EBs and announcements, cert suppression, deep reorg, drop-inbound, echo-to-source, lazy voter, EB burst, TX flood, RB equivocation, …). The TOML files are generated from the private `leios-adversarial-tools` repo and not committed here. This is the concrete mechanism by which simulator attacks and live-testnet attacks share one definition — a notable faithfulness asset.

## 7. Inputs, outputs, calibration

- **Inputs:** topology YAML (with `*.meta.json` country sidecars) + layered parameter YAMLs (figment merge onto `config.default.yaml`; ~130 keys validated against `config.schema.json`). Topology generators in `sim-cli` (`gen-test-data`: globe, organic, random-graph, simplified strategies); shipped test topologies from tiny to `thousand.yaml`; pseudo-mainnet family in `data/simulation/` (v1 10,000 nodes → v4 2,685 nodes).
- **Outputs:** JSONL or CBOR event trace; aggregate/liveness summaries; `txn_diffusion.sh` exports diffusion CDFs as ΔQ expressions for the `delta_q` tool — a working sim→analytical-model bridge.
- **Calibration:** CPU cost defaults trace to the BLS `crypto-benchmarks.rs` measurements and ledger-operation timings (catalog § supporting); default vote/cert sizes and costs distinguish persistent vs non-persistent voters, matching the CIP certificate scheme.
- **Conformance:** traces are checkable by the Agda-derived `leios-trace-verifier` (catalog entry 11).

## 8. Status and trajectory (2026-09)

Active development, now driven by the testnet/red-team group rather than the original prototyping team: telemetry and aggregated-reporting reworks (Shtukenberg, Aug 2026), mempool extension (Aug 2026), vote wire-format and election re-keying (Clark, Jul 2026), network partitioning (Paprocki, Jul 2026), vote-diffusion strategy evaluation (Wolff, PR #93, Sep 2026). The big structural item is the **shared-consensus migration** (`merge-shared-consensus-plan.md`, framed internally as "a major rewrite, and we can be bold"): lift CIP-0164 logic into `shared-rs/consensus` so that sim-rs, net-rs, and Piranha drive the *same* sans-IO consensus state machines (`LeiosState`/`PraosState`/`MempoolState`), retiring `linear_leios.rs`. As of this reading the `shared-consensus` variant wires only TX propagation (no RBs/EBs/votes yet); cross-variant byte-equivalent trace comparison is the acceptance test.

## 9. Assessment against the four catalog dimensions

- **Faithfulness.** Protocol logic: strong for Linear Leios (CIP-0164 timing rules, wFA^LS committee, certificate embedding) and conformance-checkable against the formal spec; the announce/request/deliver abstraction and absence of mini-protocol state machines are the main structural departures from the real node, along with the known-broken default mempool. Network: TCP slow-start/BDP modeled by default (port of the Haskell model); loss/retransmission absent from the default regime and effectively unexercised in the envelope regime. Direction of travel (shared consensus core with net-rs/Piranha) will tighten protocol faithfulness further.
- **Status.** The maintained reference simulator; mid-refactor toward shared-consensus.
- **Scope.** Broadest of any artifact in the catalog: 7 protocol variants, transactions to certificates, attacks, partitions, CPU, and topology generation.
- **Performance.** Virtual-time, multithreaded, shardable (~5× turbo preset); 10,000-node topologies and 1000 TPS workloads demonstrated in the 2025 experiment series; sequential engine trades speed for determinism; trace volume is the practical bottleneck at scale.

## 10. Gaps and follow-up questions

1. **Loss is modeled nowhere by default.** The only loss model (envelope) is mutually exclusive with the default TCP regime and unused by any shipped config — exactly the gap "smol world" (entry 5) targets. Worth an experiment: envelope-with-loss vs smol-world on a common topology.
2. **Unspecified-bandwidth asymmetry** (uncapped vs ~8 Mbit/s depending on regime) is a silent footgun for topology authors; check whether pseudo-mainnet topologies specify bandwidth everywhere.
3. **Mempool realism** is flagged by the maintainers themselves (§ 4): unbounded-by-default pool and backlogs, silent drop of conflicting TXs, no fees/priority/replacement, head-of-line blocking by size in the fill loop, and no per-peer advertised sets until the shared-consensus mempool lands. Results sensitive to mempool backpressure should be treated cautiously — and this is the natural first place for our own study.
4. **`shared-consensus` variant is incomplete** — do not use it for protocol results yet; watch W2-series milestones.
5. **Default config still `leios-variant: short`** — an outdated variant as the out-of-the-box default; experiments must override it (the `linear*.yaml` overlays do).
6. Whether the sequential engine's determinism has been exploited for regression baselines (`analysis/sims/regression/` exists — check what it pins).

## Sources

- [sim-rs README](https://github.com/input-output-hk/leios-tools/blob/main/sim-rs/README.md), [IMPLEMENTATION.md](https://github.com/input-output-hk/leios-tools/blob/main/sim-rs/IMPLEMENTATION.md), [docs/tcp-modelling.md](https://github.com/input-output-hk/leios-tools/blob/main/sim-rs/docs/tcp-modelling.md), [implementations/LINEAR_LEIOS.md](https://github.com/input-output-hk/leios-tools/blob/main/sim-rs/implementations/LINEAR_LEIOS.md) — leios-tools @ `7b08aaa`
- Source files read: `sim-core/src/{config.rs, events.rs, rng.rs, tcp.rs}`, `sim-core/src/network/{connection.rs, tcp_connection.rs, partition.rs}`, `sim-core/src/sim/{leios.rs, linear_leios.rs (incl. `Mempool`, ledger-state, fill paths), linear_leios/attackers.rs, stracciatella.rs, shared_consensus.rs, sequential.rs, cpu.rs, tx.rs}`, `shared-rs/consensus/src/mempool.rs`, `sim-core/src/sharding/*`, `parameters/config.default.yaml`, `merge-shared-consensus-plan.md`
- [ouroboros-leios `analysis/sims/ReadMe.md`](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/ReadMe.md) — study index and tooling (@ `11be715`)
- Commit history via GitHub API (`repos/input-output-hk/leios-tools/commits?path=sim-rs`, 2026-07 → 2026-08)
- [Catalog entry and its sources](../leios-simulation-model-catalog.md#1-sim-rs--the-rust-leios-simulator)
