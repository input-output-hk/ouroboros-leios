# Deep Dive 7: Piranha / net-rs

**Created:** 2026-09-16
**Status:** Draft for review.
**Provenance:** 🤖 (LLM-generated; the public half from source reading, the private half necessarily from Slack — marked throughout)
**Read at:** [`input-output-hk/leios-tools`](https://github.com/input-output-hk/leios-tools) commit `7b08aaad` — `net-rs/` (~28,300 lines of Rust), `shared-rs/consensus` (state machines + behavior-tree engine), `specs/001-behavior-tree-engine/`. The private `input-output-hk/leios-adversarial-tools` (`net-node`, `net-cluster`, `net-ui`, `behaviours/`) remains **inaccessible to this effort's token**; everything about it is sourced from #team-leios.
**Parent entry:** [catalog § Piranha](../leios-simulation-model-catalog.md#7-piranha-node--cluster-leios-adversarial-tools)

The live-network end of the tooling spectrum: **net-rs** is a production-quality Rust implementation of the Cardano node-to-node (N2N) wire protocols including the Leios extensions, and **Piranha** (`net-node`, private) is the lightweight, ledger-free node built on it that the red team runs — honestly or adversarially — against the real Leios testnet. Dmitry Shtukenberg's framing in the motivating thread stands: it doubles as "a network simulator with light-weight nodes" for research that needs real transport and real protocol behavior without `cardano-node`'s weight.

---

## 1. net-rs architecture (public, read directly)

Layered bottom-up: **bearer** (TCP, plus an in-memory bearer for tests) → **multiplexer** (Cardano wire format; two-class scheduler with Praos priority + Leios weighted-fair-queuing, per-protocol egress queues with backpressure, non-blocking demux) → **eight mini-protocols as real state machines with CBOR codecs, client and server sides** (Handshake, ChainSync, BlockFetch, TxSubmission, KeepAlive, PeerSharing, LeiosNotify = 18, LeiosFetch = 19) → **per-peer tasks** (initiator, duplex, server handlers — 2.5 kloc) → **multi-peer coordinator** (4.2 kloc: tip dedup, pending-fetch routing, RTT measurement with poisoned-measurement skip for artificially delayed inbound peers, `BroadcastN`/`LowestRttFirst` candidate ranking, quorum-triggered vote/EB-tx fetch bursts) → **stores**.

Faithfulness markers worth recording: TxSubmission implements the spec's actual constants (pull-based, `MAX_UNACKED = 10` flow-control window, per-state size limits and timeouts, ingress buffer cap 721,424 B); tx ids and bodies are era-wrapped exactly as `cardano-node`'s HFC expects (Byron=0 … Conway=6, **Dijkstra=7**; a wrong index makes cardano-node drop the connection — the comment records the failure mode); codec test vectors are **captured from live Cardano mainnet**; the library is hardened (allocation bounds on wire lengths, timeouts on all remote waits, no panics). CIP-0164 subtleties are modeled distinctly — e.g. `BlockAnnouncement` (the header's EB commitment, deliberately *not* deduplicated so a producer can enqueue two for an equivocation) vs `BlockOffer` (body availability, with mandatory `eb_size`). Docs compare against the Haskell and Pallas implementations.

## 2. Consensus and mempool: the shared sans-IO core

net-rs drives the same `shared-rs/consensus` state machines that sim-rs is migrating toward (dive 1 § 4.3): `LeiosState`, `PraosState`, and **`MempoolState`** — here fed by the *real* TxSubmission protocol rather than simulated messages. The `LeiosStore` exposes a `TxBodyResolver` hook so that when a peer LeiosFetches an EB's transactions and only the manifest is cached, **the host's mempool answers** — the live-network realization of EB-closure serving. This is the strongest structural convergence in the whole catalog: one mempool implementation (FIFO free pool with count-cap/oldest-evict, `eb_pinned` compartment, per-peer advertised sets, effect/response validation) exercised by the simulator, the test node, and — in Piranha — the real network.

## 3. Caches and residence times (standing section)

| Cache | Contents | Residence / eviction |
|---|---|---|
| `MempoolState` free pool | pending TXs (FIFO, arrival order) | count-capped, **oldest evicted on overflow**; drained by RB forging; Piranha configures capacity 10,000 TXs (Slack ❓) |
| `MempoolState.eb_pinned` | TX bodies drained into unsettled EBs | **100-slot** retention window, pruned on every EB observation |
| `LeiosStore` | EBs, votes, manifests, keyed `(slot, hash)`; notification queue | **slot-window retention, default 100 slots**, evicted on every version bump; explicitly sized because "each EB carries ~600 votes; without slot eviction" memory grows unboundedly. Votes carry no wire slot, so each is stamped with the tip slot at injection as its retention key |
| `LeiosTracker` offer-dedup | seen offers | **1,000-slot** dedup window (deliberately larger than the store's 100) |
| `ChainStore` | headers/blocks of the followed chain | chain-structured (not slot-window) — Praos owns chain selection |
| Per-peer advertised sets (mempool) | TxSubmission re-announce suppression | pruned alongside the pool |

Contrast with sim-rs `linear*` (dive 1 § 4.4): where the simulator's default caches are unbounded, **every net-rs cache is bounded by design** — the difference between code that must survive a live network and code that must survive a run.

## 4. Piranha and the cluster (private; Slack-sourced ❓)

- **`net-node` ("Piranha")**: a forging block producer that votes and certifies, with **no ledger** — nonces, BLS keys, and committee seats read from kleioscan/dbsync. Default behavior honest; attacks configured per node. Demonstrated the **EB Trojan Horse** (2026-08-27: an EB crafted directly with a chosen transaction, bypassing TX diffusion so victims must LeiosFetch it — testnet block #80676), and also produced *accidental* protocol violations (unintended EB forging, double spends) precisely because it lacks a ledger — Sebastian Nagel's on-record argument for a relay-proxy design instead of a forging node.
- **`net-cluster` + `net-ui`**: coordinator and web UI for a federation of Piranhas — machines PIR0–PIR10 on the live testnet (red team: Christopher Tilt, Krzysztof Paprocki, Dmitry Shtukenberg; infra John Lotoski), state tracked on the internal IOG stake dashboard. Per the behavior-tree spec, the coordinator distributes and mutates configs over a REST API.
- **Behavior trees** (`specs/001-behavior-tree-engine`, 2026-06-15, + `shared-rs/consensus/behaviour/`): TOML-defined trees ticked on the node's slot updates (Selector/Sequence/Parallel composites, condition leaves, Rust action leaves), with metadata + reproducibility seed and env-parameter blocks; a planned fuzzer mutates env parameters and reproduces failures. The engine is generic over context/effect and **strictly deterministic** (seeded RNG, never clock or OS entropy — so sim-rs can replay the same trees). The action vocabulary (~20 leaves: announce equivocation/flood/size-lie/slot-skew, fake EB/announce, cert suppression, deep reorg, lazy voter, EB burst, TX flood/withholding, RB equivocation, echo-to-source, drop-inbound, "t22"…) is shared verbatim with sim-rs — one attack definition runs in simulation and on the testnet.

## 5. As a "network simulator with lightweight nodes"

What Piranha offers that nothing else in the catalog does: **many protocol-faithful nodes at low cost on a real network** — real TCP, real mux QoS, real mini-protocol timing — without ledger validation cost. Fit for: diffusion and topology research needing real transport; protocol-timing measurements; adversarial-behavior studies; load generation against testnets. Not fit for: anything requiring semantic tx validity (no ledger — traffic is protocol-shaped, not protocol-correct), closed-loop protocol experiments needing determinism (use sim-rs's engines), or mainnet-scale node counts on one machine ❓🤖 (per-node footprint unmeasured in this pass).

## 6. Assessment against the four catalog dimensions

- **Faithfulness.** Wire/protocol level: highest in the catalog — it interoperates with real `cardano-node`s and its codecs are mainnet-vector-tested. Semantic level: deliberately absent (no ledger). Fetch policy is production-shaped but simpler than dive 6's Fetch scheduler (RTT-ranked selection; no BDP probing or snubbing found in the coordinator ❓🤖 — worth confirming before citing).
- **Status.** Active on both halves (public net-rs commits through Aug 2026; cluster operations through Sept 2026).
- **Scope.** Full Praos + Leios N2N; honest and adversarial node behavior; live-network operation.
- **Performance.** Real-time by nature; light-weight per node; cluster scale ~a dozen nodes to date.

## 7. Follow-up questions

1. **Get read access to `leios-adversarial-tools`** — until then, everything in § 4 is second-hand; the mempool-capacity 10,000 figure and PIR-cluster details need first-hand confirmation.
2. Does the coordinator's fetch policy incorporate any of PR #880's Fetch design (probing/snubbing), or is that a pending convergence? (Also flagged from the other side in dive 6.)
3. For our mempool study: Piranha is the natural instrument for **measuring real mempool-alignment** on the testnet (per-node `MempoolState` contents are observable), complementing smol world's model (dive 5) — worth a design sketch.
4. The `TxBodyResolver` path (mempool answers LeiosFetch) is exactly the EB-closure write-back seam; instrumenting it would measure how often closures are served from mempool vs. manifest cache.

## Sources

- Source read at `leios-tools@7b08aaad`: `net-rs/README.md` + `net-rs/docs/*`, `net-core/src/{multi_peer/coordinator.rs, multi_peer/mod.rs, store/leios_store.rs, store/chain_store.rs, protocols/txsubmission/mod.rs, protocols/leios_fetch/*, protocols/leios_notify/*, mux/mod.rs, peer/*}`, `shared-rs/consensus/src/{mempool.rs, behaviour/README.md, behaviour/actions/*}`, `specs/001-behavior-tree-engine/spec.md`
- Slack (internal): [Piranha thread 2026-08-27](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1787863719890129) and replies (Nagel 08-12/08-28); [Lotoski 2026-08-30](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1788082826261799?thread_ts=1788041943.086199&cid=C074AHSKJF7); [Shtukenberg 2026-09-16](https://input-output-rnd.slack.com/archives/C074AHSKJF7/p1789569700319979?thread_ts=1789558993.289409&cid=C074AHSKJF7)
- [Dive 1 § 4.3](./01-sim-rs.md) (shared MempoolState), [Dive 6 § 6](./06-mininet-leiosfetch.md) (fetch-policy question)
- [Catalog entry 7](../leios-simulation-model-catalog.md#7-piranha-node--cluster-leios-adversarial-tools)
