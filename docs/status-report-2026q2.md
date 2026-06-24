---
title: Leios development status report — 2026 Q2
status: Draft
date: 2026-06-24
author:
  - Sebastian Nagel <sebastian.nagel@iohk.io>
---

# Leios development status report — 2026 Q2

> [!IMPORTANT]
>
> This report is a snapshot of the Leios implementation as of 2026 Q2. The
> observations and status assessments recorded here are provisional and will be
> superseded as the design and implementation mature. The authoritative,
> living references are [CIP-164][cip-164] (the protocol specification) and the
> [Leios technical design document](./leios-design/README.md) (the
> implementation design); where this report and those documents disagree, they
> take precedence.

## Table of contents

- [Executive summary](#executive-summary)
- [Introduction](#introduction)
  - [Purpose](#purpose)
  - [Scope](#scope)
  - [Context](#context)
  - [Audience](#audience)
- [How to read this report](#how-to-read-this-report)
- [Component status](#component-status)
  - [Praos-over-Leios prioritization](#praos-over-leios-prioritization)
  - [High-throughput transaction submission](#high-throughput-transaction-submission)
  - [High-throughput mempool](#high-throughput-mempool)
  - [Block production](#block-production)
  - [Endorser block diffusion and storage](#endorser-block-diffusion-and-storage)
  - [Transaction cache](#transaction-cache)
  - [Voting and certification](#voting-and-certification)
  - [Committee selection](#committee-selection)
  - [Key registration and rotation](#key-registration-and-rotation)
  - [Cryptographic primitives](#cryptographic-primitives)
  - [Block validation and adoption](#block-validation-and-adoption)
  - [Catching up](#catching-up)
  - [Serialization](#serialization)
  - [New protocol parameters](#new-protocol-parameters)
  - [Node API and configuration](#node-api-and-configuration)
- [Conclusion](#conclusion)
- [Other resources](#other-resources)

## Executive summary

> _Draft. Intended content: one paragraph stating that this period achieved
> prototype and design coverage across the full CIP-164 pipeline — committee
> selection, block production, endorser-block creation and diffusion, vote
> management, certificate generation, and block validation — that the public
> [Musashi testnet][musashi] (network ID 164) was bootstrapped across three
> independent node implementations including a deliberate red team, and that the
> BLS12-381 cryptographic primitives have been independently audited. Closes by
> naming the work that remains before a release candidate (transaction
> submission, mempool performance, efficient network catch-up) and noting that
> the high-confidence stage is deliberately last._

## Introduction

### Purpose

This report is a status overview of the Leios implementation: the key
components, the workflows that connect them, and the notable highlights and open
questions across the design landscape as of 2026 Q2. It is intentionally
anecdotal rather than exhaustive — a snapshot of where things stand and what was
learned, not a specification. The specification role belongs to [CIP-164][cip-164]
and the node-level [`leios-design`](./leios-design/README.md) document, which
this report points to throughout. It is provided in support of milestone MS4.6.

### Scope

The report spans the components and workflows of `cardano-node` touched by
CIP-164, ordered roughly by the protocol flow: resource prioritization and
transaction flow first, then block and endorser-block production and diffusion,
voting and certification, and finally the supporting ledger and node-API
changes. Each
topic states its status and highlights rather than its full design, and the
selection deliberately does not mirror the [technical design
document](./leios-design/README.md#technical-design) section-for-section.

### Context

> _Draft. Orient the reader to the two authoritative documents — [CIP-164][cip-164]
> as the protocol specification and the
> [technical design document](./leios-design/README.md) as the living
> implementation design — and state that this report is the time-stamped status
> view over them. Note that the changes target the `Dijkstra` ledger era._

### Audience

> _Draft. Technical audience: node developers, researchers, SPOs, and milestone
> assurance reviewers._

## How to read this report

Each component carries a soft status line along a five-stage ladder —
**requirements captured** (in CIP-164), **prototype available**, **design
settled**, **implemented**, **high confidence** (the mainnet bar: independent
audit, conformance, performance) — stopping at the stage reached. Stages not yet
reached are left off rather than marked; open questions are discussed in prose,
not tabulated. The high-confidence stage is implicit throughout and addressed in
the [Conclusion](#conclusion). Each component links to its design-document
section as the primary reference.

## Component status

### Praos-over-Leios prioritization

**Status** — requirements captured; design maturing; implementation early.

> _Draft. The node must prioritize Praos over all Leios traffic and computation,
> and younger EBs over older ones (Praos > fresh Leios > stale Leios). Candidate
> mechanisms: a multiplexer bias (`NEW-LeiosPraosMuxBias`) to keep Praos traffic
> ahead, and TCP bearer management (e.g. `TCP_NOTSENT_LOWAT`, though not portable)
> to avoid head-of-line blocking that would slow apparent Praos block
> propagation. The harder questions — GC pressure and disk-bandwidth contention
> during a worst-case protocol burst — are judgeable only by prototype, not by
> the simulations that drove the first CIP._
>
> Primary sources: [design doc §Resource management](./leios-design/README.md#resource-management), [§Traffic prioritization](./leios-design/README.md#traffic-prioritization), [§Message latencies](./leios-design/README.md#message-latencies).
> Pointers to fold in: whether the existing fair multiplexer already suffices; prototype/measurement results on the contention risks.

### High-throughput transaction submission

**Status** — implementation maturing (delivered via `ouroboros-network` v2, off the CIP track).

> _Draft. Leios raises the target consensus data rate well above Praos, so the
> transaction-submission layer between mempools must sustain a rate exceeding it
> or endorser blocks starve. The "v2 undecision" variant shows the highest
> sustained data rates and is the candidate that best fits this requirement._
>
> Primary source: [design doc §High-throughput transaction submission](./leios-design/README.md#high-throughput-transaction-submission).
> Pointers to fold in: latest v2 throughput figures ([ouroboros-network#5336][on-5336], [#5337][on-5337]).

### High-throughput mempool

**Status** — requirements maturing; prototype maturing; design maturing; implementation early.

> _Draft. Re-applying thousands of transactions can block transaction submission
> and forging; the design decouples transaction diffusion from mempool syncing
> and keeps a block-producer view of transactions for forging. A DAG-style
> mempool is a mid-term direction. Originally out of scope, now identified as
> essential._
>
> Primary source: [design doc §High-throughput mempool](./leios-design/README.md#high-throughput-mempool).
> Pointers to fold in: the `reapplyTx`-cost problem statement; monthly review or Slack thread on the mempool redesign.

### Block production

**Status** — requirements captured; prototype available; design maturing.

> _Draft. The block-production thread is extended to forge an EB alongside each
> RB (unless empty), with a new EB capacity measure; a later version
> pre-computes the EB transaction chunk to avoid delaying a CertRB._
>
> Primary source: [design doc §Block production](./leios-design/README.md#block-production).

### Endorser block diffusion and storage

**Status** — requirements captured; prototype available; design maturing.

Acquiring endorser blocks has been the central design effort of recent months:
the prototype's fetch logic is adequate for demos but has poor worst-case
resource bounds, and CIP-164's message-delay limits were derived from an
over-abstracted network stack. The aim of the current design is timely,
verifiable EB availability with bounded resource usage and bounded tail latency,
robust to message bursts and protocol storms. Freshest-first fetching is the
burst-robust baseline; the refinements below make delivery predictable enough to
keep certified EBs within the protocol's diffusion budget.

Two ideas carry the fetching design, set out in an [EB-availability
analysis][eb-avail]. First, each node keeps a small stake-sampled
set of big-ledger peers (currently three); once an EB's voting window closes, it
fetches the full certified EB from whichever of those peers advertise it. Because
certification implies that a large share of stake has already seen the EB, this
places certified EBs within roughly two hops of almost all honest nodes. Second,
everything else is fetched fine-grained: the producer splits the EB into
Merkle-tree parts and a node requests different parts from different peers, each
validated by its inclusion proof. Spreading requests across all peers is what
bounds tail latency — no single slow or adversarial peer can hold up delivery —
while keeping worst-case waste to a small multiple of one EB. Equivocation is
contained by fetching only one body per block-production opportunity, the first
header seen.

Protocol storms — many honest EBs produced close together, or an adversary
releasing withheld EBs at the worst moment — are handled by reversing the
download order to oldest-first within the critical diffusion window, so a storm
becomes observable before voting, then returning to freshest-first afterwards; a
voting rule abstains during a detected storm, and late-released EBs are
deprioritized. Together these bound the higher-priority traffic that can compete
with a certified EB during its window. This is closely intertwined with the
network-delay analysis: the header-, voting-, and diffusion-window budgets the
design relies on are being put on a mainnet-realistic footing through improved
DeltaQ analysis and new topology simulations, since the worst cases are hard to
exercise any other way.

For storage, a node retains EB closures up to the immutable tip and indefinitely
once the immutable chain certifies them — closures are large and long-lived
because of possible deep Praos forks. A baseline redesign bounds memory, CPU, and
disk by managing a fixed budget of work-in-progress EBs on disk, tracking
in-flight requests within hard limits, and reusing the
[transaction cache](#transaction-cache); whether to keep this bespoke or delegate
to an embedded store such as SQLite is still being assessed by microbenchmark.

Open question: the storage-backend choice, and — more fundamentally — whether
realistic-topology behavior matches the simulated behavior the CIP parameters
assume.

Primary sources: [design doc §Endorser block diffusion](./leios-design/README.md#endorser-block-diffusion), [§Endorser block storage](./leios-design/README.md#endorser-block-storage).
Supporting: [baseline LeiosFetch design][fetchlogic]; [EB-availability analysis][eb-avail]; [fetch-logic design issue][ol-853]; [improved DeltaQ analysis][ol-889].

### Transaction cache

**Status** — requirements captured; design maturing.

> _Draft. A unidimensional LRU cache of recently-seen transactions (EB closures
> plus mempool), sized to roughly an hour of traffic, designed to avoid GC
> pressure under adversarial load (~131k tx/h)._
>
> Primary source: [design doc §Transaction cache](./leios-design/README.md#transaction-cache).
> Pointers to fold in: the decision on a Haskell vs Rust/FFI implementation.

### Voting and certification

**Status** — requirements captured; prototype available; design settled (shared with Peras); certificate aggregation implemented (peer-reviewed).

A dedicated Leios voting thread wakes when an EB closure becomes available and,
if the voting rules require this pool to vote, validates the EB and issues its
vote on time. A vote-state component tracks valid votes and, once the threshold
is met, aggregates them into a certificate and holds it for inclusion in the
next RB the pool issues. The workflow is well established — the design document
carries a C4 diagram of the voting components — and Leios and Peras have
independently arrived at the same design, which is reassuring and lets the two
share code once integrated into the same node codebase.

The prototype ([ouroboros-leios#790][ol-790]) bears this out: the initial
assumptions behind the voting thread hold up well in practice, and certificate
aggregation and verification are prototyped against CIP-164 (see
[Cryptographic primitives](#cryptographic-primitives)).

The principal unknown is the voting mini-protocol's behavior at scale.
[Network simulations][sims-2026w18] on 750- and 1,500-node topologies —
including an "everyone votes" mode that maximizes committee size — found
throughput and EB certification essentially unaffected by committee size at the
tested loads, which substantially reduces but does not eliminate the concern.
These topologies are still smaller than mainnet's ~3,000 SPOs, so high
confidence is reachable only through large-scale load testing. Should the
dedicated mini-protocol prove inadequate, Peras' `ObjectDiffusion` is a less
efficient but workable fallback. The reassuring corollary is that this is a
throughput concern, not a safety one: an underperforming voting protocol can
only limit throughput, never compromise chain safety.

Primary source: [design doc §Voting and certification](./leios-design/README.md#voting-and-certification).
Supporting: [ouroboros-leios#790][ol-790]; [cardano-base#670][base-670]; [ouroboros-consensus#2068][oc-2068]; [network simulations (2026w18)][sims-2026w18].

### Committee selection

**Status** — requirements captured; prototype available (interim all-vote); design settled (simplified, stake-based truncation).

The voting committee is now chosen by a stake-based truncation scheme that
replaces the earlier wFA^LS (weighted Fait Accompli with Local Sortition)
design, merged into CIP-164 as [CIPs#1196][cip-1196]. At each epoch boundary
pools are ordered by stake and taken until a configured cumulative-stake target
is met; every member then votes on every EB in the epoch, with no per-EB
elections, non-persistent voters, or sortition proofs. The certificate collapses
to a bitfield over the known committee plus one aggregated BLS signature, and
quorum becomes a minimum fraction of total active stake rather than a head-count.
BLS12-381, the 75% quorum, certificate timing, the mini-protocols, and the
threat model are all unchanged.

The motivation is certificate size and verification cost on the critical path,
which wFA^LS dominated through non-persistent voters' eligibility proofs.
Benchmarked against mainnet stake with [leios-wfa-ls-demo][wfa-ls-demo] at
coverage equivalent to the wFA^LS reference (a ~916-voter, 99%-cumulative-stake
committee at epoch 612), the certificate shrinks from ~6.8 kB to a few hundred
bytes — over a 30× reduction — and worst-case verification from ~10 ms to ~2 ms;
the coverage threshold is stable and gently decreasing across recent epochs.
These figures are being firmed up with measured values from the demo.

The prototype ([ouroboros-consensus#2068][oc-2068]) performs certificate
aggregation and validation per CIP-164 but still selects committees with an
interim "all-vote" scheme rather than the final stake-based truncation.

Open question: where the selected committee state lives in the codebase —
materialized in the ledger state versus computed on demand at the epoch boundary.

Primary source: [design doc §Committee selection](./leios-design/README.md#committee-selection).
Supporting: [CIPs#1196][cip-1196]; [leios-wfa-ls-demo][wfa-ls-demo]; [ouroboros-consensus#2068][oc-2068].

### Key registration and rotation

**Status** — requirements maturing; prototype maturing; design maturing; CLI implementation early.

> _Draft. SPOs register and rotate BLS voting keys; the key-generation commands
> already exist ([cardano-cli#1355][cli-1355], [#1356][cli-1356]), ahead of the
> written design._
>
> Primary source: [design doc §Key registration and rotation](./leios-design/README.md#key-registration-and-rotation).
> Pointers to fold in: the assumed registration mechanism (PoolReg cert / dedicated cert / in-header via KES).

### Cryptographic primitives

**Status** — requirements captured; prototype available; design settled; implemented; primitives audited, certificate layer peer-reviewed.

This section covers the low-level signature primitives; the cryptographically
relevant higher-level work lives in [Key registration and rotation](#key-registration-and-rotation)
and [Voting and certification](#voting-and-certification).

Leios derives the safety of its votes and certificates from the pairing-based
BLS12-381 scheme, whose key- and signature-aggregation lets a committee express
approval as one compact artifact. The bindings extend the BLS12-381 utilities
CIP-0381 added to `cardano-base`: variant-agnostic sign/verify (small-public-key
and small-signature behind one abstraction), proof-of-possession against
rogue-key attacks, aggregation, batch verification, and deterministic
canonically-compressed serialization. The certificate operations (aggregate and
verify over a committee) layer on top in a dedicated `cardano-crypto-leios`
package, with proof-of-possession checked at the certificate level. Conformance
vectors from the [Rust reference][crypto-rs] pin cross-implementation
compatibility and give a performance baseline.

Implementation has landed in [cardano-base#670][base-670]. The BLS12-381
primitives are independently audited; the certificate aggregation/verification
layer is peer-reviewed and awaits independent audit before production use.

Open question: whether BLST's combined-pairing fast path for many-message
verification is worth adopting — with Linear Leios it may never be needed.

Primary source: [design doc §Cryptography](./leios-design/README.md#cryptography).
Supporting: [cardano-base#670][base-670]; [Rust reference][crypto-rs].

### Block validation and adoption

**Status** — requirements captured; prototype available; design maturing.

> _Draft. How a certified ranking block is verified and adopted, as one flow: a
> CertRB is buffered in a staging area until its closure arrives (the volatile DB
> only holds RBs ready for chain selection); its certificate is verified against
> the voting committee held in the ledger state during block-body (BBODY)
> validation; the certified EB's transactions are applied via a new third
> validation level (`notValidateTx`, cheaper than today's `reapplyTx`, itself
> ~10× cheaper than `applyTx`); transactions are not inlined into the block for
> the ledger but resolved and passed to it separately._
>
> Primary sources: [design doc §Chain selection](./leios-design/README.md#chain-selection), [§Block validation](./leios-design/README.md#block-validation), [§Certificate verification](./leios-design/README.md#certificate-verification), [§Transaction validation levels](./leios-design/README.md#transaction-validation-levels).
> Pointers to fold in: staging-area vs enhanced chain selection; BBODY-rule update status ([cardano-ledger#5872][ledger-5872]).

### Catching up

**Status** — requirements captured; design early.

> _Draft. A catch-up path more efficient than the staging-area / out-of-order
> chain-selection route, possibly a dedicated mini-protocol. The least-developed
> area; originally out of scope, now identified as essential._
>
> Primary source: [design doc §Catching up](./leios-design/README.md#catching-up).
> Pointers to fold in: any catch-up design notes, even rough.

### Serialization

**Status** — requirements captured; design maturing; implementation maturing.

> _Draft. Deterministic CBOR de/serialization for the RB body, EB structure, and
> vote structure; the `LeiosCert` is added to `Dijkstra` blocks._
>
> Primary source: [design doc §Serialization](./leios-design/README.md#serialization).
> Pointers to fold in: whether vote serialization is owned by the ledger or consensus. Supporting: [cardano-ledger#5872][ledger-5872].

### New protocol parameters

**Status** — requirements captured; design maturing; implementation maturing.

> _Draft. New governance-updatable parameters added to the `Dijkstra`
> `PParams`/`PParamsUpdate`._
>
> Primary source: [design doc §New protocol parameters](./leios-design/README.md#new-protocol-parameters).
> Pointers to fold in: the parameter list; whether any are fixed globals.

### Node API and configuration

**Status** — design maturing; implementation early.

> _Draft. Changes to the node's external interfaces: new LocalStateQuery queries
> for the registered BLS keys and the voting committee; node-to-client changes
> (Mithril uses `LocalChainSync` without hash-consistency checks and stays
> compatible); and feature flags for development phases plus new operator
> configuration._
>
> Primary sources: [design doc §LocalStateQuery additions](./leios-design/README.md#localstatequery-additions), [§Node-to-client](./leios-design/README.md#node-to-client), [§Feature flags and configuration](./leios-design/README.md#feature-flags-and-configuration).
> Pointers to fold in: the new query list; the dev-phase feature-flag list.

## Conclusion

> _Draft. Two beats merged into one closing section:_
>
> _Deployment — the public [Musashi testnet][musashi] (network ID 164) is live,
> running simultaneously on three independent node implementations including a
> deliberately adversarial red team, giving real-world exposure to the current
> Leios design and to its expected impact on SPOs and dApps._
>
> _Outstanding work toward a release candidate — transaction submission, mempool
> performance, and efficient network catch-up were outside the original scope but
> are now identified as essential. The high-confidence stage (independent audit,
> conformance vectors, and performance validation) is the mainnet gate and is
> deliberately the last stage reached; today only the BLS12-381 primitives have
> cleared it._

## Other resources

- [First technical report](./technical-report-1.md)
- [Second technical report](./technical-report-2.md)
- [Threat model](./threat-model.md)
- [Leios technical design document](./leios-design/README.md)
- [CIP-164][cip-164]
- [Public protocol status page][status-page]
- [Monthly reviews][monthly-reviews]
- [Musashi testnet][musashi]

[cip-164]: https://github.com/cardano-foundation/CIPs/pull/1078
[status-page]: https://leios.cardano-scaling.org/docs/development/status
[monthly-reviews]: https://leios.cardano-scaling.org/docs/development/monthly-reviews
[musashi]: https://musashi.network
[base-670]: https://github.com/IntersectMBO/cardano-base/pull/670
[ledger-5872]: https://github.com/IntersectMBO/cardano-ledger/pull/5872
[cli-1355]: https://github.com/IntersectMBO/cardano-cli/pull/1355
[cli-1356]: https://github.com/IntersectMBO/cardano-cli/pull/1356
[on-5336]: https://github.com/IntersectMBO/ouroboros-network/issues/5336
[on-5337]: https://github.com/IntersectMBO/ouroboros-network/issues/5337
[wfa-ls-demo]: https://github.com/cardano-scaling/leios-wfa-ls-demo
[crypto-rs]: https://github.com/input-output-hk/ouroboros-leios/tree/main/crypto-benchmarks.rs
[cip-1196]: https://github.com/cardano-foundation/CIPs/pull/1196
[oc-2068]: https://github.com/IntersectMBO/ouroboros-consensus/pull/2068
[ol-790]: https://github.com/input-output-hk/ouroboros-leios/issues/790
[sims-2026w18]: https://github.com/input-output-hk/ouroboros-leios/tree/main/analysis/sims/2026w18
[fetchlogic]: https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/targeted-design-investigations/a-baseline-LeiosFetch-design/LeiosFetchLogic.md
[ol-853]: https://github.com/input-output-hk/ouroboros-leios/issues/853
[ol-889]: https://github.com/input-output-hk/ouroboros-leios/pull/889
[eb-avail]: https://docs.google.com/document/d/1L2sWKqk96XfHToWXBcz82Tey69lFnsdGBlvEDNLw0HM/edit
