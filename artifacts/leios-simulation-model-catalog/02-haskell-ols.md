# Deep Dive 2: The Haskell Simulation (`ols`)

**Created:** 2026-09-16
**Status:** Draft for review.
**Provenance:** 🤖 (LLM-generated from source-code reading, pending human review)
**Read at:** [`input-output-hk/ouroboros-leios`](https://github.com/input-output-hk/ouroboros-leios) commit `11be71594ef1d71db7917ced11ccd54795335c07`, directory [`simulation/`](https://github.com/input-output-hk/ouroboros-leios/tree/main/simulation) (with the shared schema crate [`leios-trace-hs/`](https://github.com/input-output-hk/ouroboros-leios/tree/main/leios-trace-hs)).
**Parent entry:** [catalog § Haskell simulation](../leios-simulation-model-catalog.md#2-haskell-simulation-ols)

The original high-fidelity Leios simulator: a Haskell discrete-event simulation built on the *same foundations as the real node* — `io-sim`/`io-classes` for the simulation monad and `Network.TypedProtocol` for genuine mini-protocol state machines — with built-in Gtk visualization. Dormant since late 2025; its structural fidelity remains unmatched, but its protocol content stops at mid-2025 Linear Leios and it models **no transactions and no mempool**.

---

## 1. Identification

| | |
|---|---|
| Location | `ouroboros-leios/simulation/` — 64 modules, ~20,800 lines of Haskell; executable `ols` |
| Foundations | `io-sim` + `io-classes` (the real node's simulation/testing monad), `Network.TypedProtocol` (the real node's protocol framework) |
| Shared schema | `leios-trace-hs` — config parsing (`LeiosConfig.hs`), trace event schema (`LeiosEvents.hs`), topology (`LeiosTopology.hs`), shared with the trace verifier and (by construction) with sim-rs's config format |
| Authors | Well-Typed (Andrea Vezzosi, Wen Kokke, Duncan Coutts) with IOG (Nicolas Frisby, Yves Hauser, others) |
| Docs | `README.md`, `PRAOS.md`, `ROADMAP.md` (early-phase, now historical), `docs/`, `gnuplot/` |

## 2. Architecture

Three layers, composed bottom-up, each with standalone example visualizations:

1. **Transport** (`ModelTCP.hs`, `Chan/`): the TCP *forecast* model — given connection properties (one-way latency, sender serialization bandwidth, receiver window) and a congestion window evolving by slow start with idle reset, `forecastTcpMsgSend` computes each message's arrival schedule analytically. **No packet loss, no retransmission** (nothing in the module even mentions them); receiver window caps effective bandwidth if under 2×BDP (bandwidth-delay product). This is the model sim-rs later ported as its default TCP regime, so at the transport layer the two simulators are by construction equivalent. `Chan/Mux.hs` multiplexes message bundles over one shared TCP bearer — modeling the real node's mux (the thing `network-mux`'s Leios demo exercises on a real kernel).
2. **Mini-protocols** (`PraosProtocol/`, `LeiosProtocol/Relay.hs`): **real typed-protocol state machines** — ChainSync, BlockFetch (client and server sides), and a generalized Relay protocol used for IB/EB/vote diffusion, written against `Network.TypedProtocol` exactly as in `ouroboros-network`. This is the deepest structural-faithfulness asset in the whole catalog: protocol pipelining, agency, and message ordering are modeled by the same machinery the production node uses, where sim-rs approximates with fire-and-forget announce/request/deliver.
3. **Nodes** (`PraosProtocol/PraosNode.hs`, `LeiosProtocol/Short/Node.hs` — 1,534 lines): a Praos node (block production, chain selection, diffusion) and a Leios node layering IB/EB/vote relay pipelines on top, with a bounded CPU task queue (`TaskMultiQueue`, `processing-queue-bound`) drained by `processing-cores` workers; every validation/generation step is a named `CPUTask` with a configurable delay (`delays.*` in the shared config).

**Topology tooling** is unexpectedly rich: `ols` subcommands convert benchmark-cluster topologies, lay out clusters into coordinates, generate topologies from a world shape and expected link count, and — notably — `report-data` emits diffusion CSVs *either from simulation output or from idealized graph diffusion*, a built-in analytic baseline.

**Visualization:** the `viz` subcommand renders live Gtk animations or PNG frame sequences for each layer (`tcp-1..3`, `relay-*`, `praos-*`, Leios P2P views); `Sample.hs`/`DataSimP2P.hs` produce headless data runs.

## 3. Protocol scope

`data LeiosVariant = Short | Full | Linear` (in `leios-trace-hs`, i.e. the shared config schema — narrower than sim-rs's seven). Everything lives under the `LeiosProtocol.Short.*` namespace regardless of variant:

- **Short/Full Leios**: the full IB/EB/vote pipeline machinery — pipelines, stages (`Propose`/`Endorse`/vote ranges), EBs referencing IBs and (Full) earlier-pipeline EBs, votes, certificates in RBs, ledger-state computation threads, freshest-first delivery.
- **Linear Leios**: integrated July–August 2025 **by reusing the IB machinery** — `convertLinearId :: InputBlockId -> EndorseBlockId` maps Linear EBs onto IB identifiers, pipelines degenerate (`Linear -> 0` stage offsets), and ledger-state threads are skipped for Linear. It is a genuine Linear implementation but a *retrofit*, predating CIP-0164 details that sim-rs later acquired (no `linear-eb-propagation-criteria` staging, no wFA^LS committee distinction found, no equivocation-wait rule ❓🤖 — absence inferred from grep, not exhaustive reading).
- **Praos alone** is a first-class simulation target (`praos-*` visualizations, `PRAOS.md`) — still useful as a network-behavior reference independent of Leios.

**What it does not model:** transactions. Block payloads are byte *sizes* (`txsPayload = cfg.leios.sizes.…AvgSize`, RB legacy payload from config averages) — there are no TX objects, no TX diffusion, and **no mempool of any kind**. This confirms the 2025 experiment record ("Haskell does not model transactions") from the code itself. Consequently sharding, conflicts, fees, and the entire TX lifecycle are out of scope. It also has no adversarial behaviors (no attack configs found) and no network partitions.

## 4. Mempool and transaction caches

**Mempool: none** (the word occurs once, in a comment). The TX-cache question therefore becomes: *which object caches exist, and what bounds their residence?* — and here the Haskell sim is actually more disciplined than sim-rs's `linear*` default, because residence is tied to protocol stage structure via **`cleanup-policies`** (the config key that is a **no-op in sim-rs** — it is honored *here*, resolving the row-1 question):

| Cache | Structure | Residence / eviction (when the policy is enabled) |
|---|---|---|
| Relay buffers (IBs, EBs, votes) | `RelayBuffer`: FingerTree of ticketed entries + `Map key Ticket` index — models the real relay window (consumers track tickets, exactly like TxSubmission window semantics) | `CleanupExpiredIb`: IB relay state for pipeline *p* pruned at the slot after `lastEndorse(p)` — i.e., once no EB can reference it |
| `iBsForEBsAndVotesVar` (IBs held for EB validation/voting) | `Map` by pipeline | Pruned after `lastVoteSend(p)` (+2 pipelines under `late-ib-inclusion`) |
| Uncertified EBs | per-pipeline store | `CleanupExpiredUncertifiedEb`: pruned once their pipeline's voting cannot succeed |
| Certified-but-unadopted EBs (+ their votes) | EB store + `votesForEBVar` | `CleanupExpiredUnadoptedEb`: pruned `maxEndorseBlockAgeSlots` after the pipeline's Endorse end, if not adopted by an on-chain RB — **disabled for Full** (a fresh Full EB may reference back to genesis; the code notes the smarter policy as TODO) |
| Votes | vote store | `CleanupExpiredVote`: separate Linear and non-Linear pruning threads |

Each policy is an independent pruning *thread* keyed to pipeline numbers, waking at the slot where the object class expires. With policies disabled, caches grow for the whole run — same default posture as sim-rs, but here the bound, when enabled, is **protocol-structural** (stage arithmetic) rather than a wall-clock age. Residence times in slots therefore vary with stage-length parameters rather than being fixed constants. Shipped default enables only `cleanup-expired-vote`.

## 5. Status, activity, performance

- **Dormant**: last substantive changes Aug–Sep 2025 (Linear Leios CI fixes, Linear trace-verifier support); 2026 commits are documentation link updates only. The repository README directs Leios work to sim-rs and calls the Leios-specific parts outdated.
- **Performance**: single-threaded per run (io-sim); the team's stated reason for preferring sim-rs. No sharding, no parallel engines. Fine for 100-node topologies and protocol-behavior studies; the 10k-node pseudo-mainnet runs of 2025 were done on it but slowly.
- **Faithfulness checks**: it was one leg of the Rust-vs-Haskell cross-validation (IB diffusion, 2025) and its traces pass the Agda trace verifier — including Linear (Sep 2025). Its `ModelTCP` is the reference implementation for sim-rs's default transport.

## 6. Assessment against the four catalog dimensions

- **Faithfulness.** Structurally the highest of any simulator here (real typed protocols, real mux model, io-sim); *content*-wise frozen at mid-2025 Linear (retrofit via IB machinery) with no TXs, no mempool, no attacks, no partitions.
- **Status.** Dormant; useful as (a) the transport-model reference, (b) a Praos network baseline, (c) the pattern-book for protocol-faithful simulation (typed protocols + relay buffers + cleanup threads), and (d) the second leg of cross-validation when sim-rs changes need checking.
- **Scope.** Praos + Short/Full/Linear Leios diffusion and certification; block-level only.
- **Performance.** Single-threaded; adequate at 100–1,000 nodes, painful at mainnet scale.

## 7. Gaps and follow-up questions

1. **Is the Linear retrofit still protocol-accurate against CIP-0164?** The mapping of EBs onto IB machinery predates several CIP details; a diff of its Linear timing rules against the CIP (and against sim-rs's `linear_leios.rs`) would say whether cross-validation against it is still meaningful for Linear.
2. **The RelayBuffer/ticket machinery is the best available model of relay-window semantics** — if our mempool study needs window/backpressure realism that sim-rs lacks, porting `RelayBuffer` + typed TxSubmission into a TX-carrying sim (or resurrecting this one with a TX layer) is a concrete option; the shared-consensus migration (dive 1 § 8) is the competing path.
3. **Cleanup-policy semantics differ across simulators silently** — same config key, honored here, ignored in sim-rs. Any cross-simulator comparison config should either disable them or note the asymmetry (add to the cross-validation checklist).
4. Whether `report-data`'s *idealized graph diffusion* baseline matches the ΔQ model's predictions would be a cheap three-way consistency check (Haskell idealized vs ΔQ vs sim-rs).

## Sources

- Source read at `ouroboros-leios@11be715`: `simulation/src/{ModelTCP.hs, Chan/*, P2P.hs, Main.hs, RelayProtocol.hs}`, `simulation/src/PraosProtocol/{ChainSync.hs, BlockFetch.hs, PraosNode.hs}`, `simulation/src/LeiosProtocol/{Short.hs, Config.hs, Relay.hs, RelayBuffer.hs, Short/Node.hs, Short/Generate.hs}`, `simulation/{README.md, ROADMAP.md}`; `leios-trace-hs/src/LeiosConfig.hs`
- [simulation/README.md](https://github.com/input-output-hk/ouroboros-leios/blob/main/simulation/README.md) (outdated-variant notice), [analysis/sims/ReadMe.md](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/ReadMe.md) (single-threaded/speed note)
- Commit history via GitHub API (`commits?path=simulation`, 2025-08 → 2026-06)
- [Dive 1: sim-rs](./01-sim-rs.md) — TCP-model port lineage, `cleanup-policies` no-op finding
- [Catalog entry 2 and its sources](../leios-simulation-model-catalog.md#2-haskell-simulation-ols)
