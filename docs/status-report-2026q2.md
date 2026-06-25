---
title: Leios development status report — 2026 Q2
status: Draft
date: 2026-06-24
author:
  - Sebastian Nagel <sebastian.nagel@iohk.io>
---

# Leios implementation status report — 2026 Q2

> [!IMPORTANT]
>
> This report is a snapshot of the Leios implementation as of 2026 Q2. The
> observations and status assessments recorded here are provisional and will be
> superseded as the design and implementation mature. The authoritative,
> living references are [CIP-164][cip-164] (the protocol specification) and the
> [Leios technical design document](./leios-design/README.md) (the
> implementation design); where this report and those documents disagree, they
> take precedence.

<details>
  <summary><h2>Table of contents</h2></summary>

- [Introduction](#introduction)
  - [Scope](#scope)
  - [Audience](#audience)
- [Component status](#component-status)
  - [Praos-over-Leios prioritization](#praos-over-leios-prioritization)
  - [High-throughput transaction submission](#high-throughput-transaction-submission)
  - [High-throughput mempool](#high-throughput-mempool)
  - [Block production](#block-production)
  - [Endorser block diffusion and storage](#endorser-block-diffusion-and-storage)
  - [Transaction cache](#transaction-cache)
  - [Voting and certification](#voting-and-certification)
  - [Block validation and adoption](#block-validation-and-adoption)
  - [Catching up](#catching-up)
  - [Committee selection](#committee-selection)
  - [Key registration and rotation](#key-registration-and-rotation)
  - [Cryptographic primitives](#cryptographic-primitives)
  - [Serialization](#serialization)
  - [New protocol parameters](#new-protocol-parameters)
  - [Node API and configuration](#node-api-and-configuration)
- [Conclusion](#conclusion)
- [Other resources](#other-resources)

</details>

## Introduction

Leios is specified in [CIP-164][cip-164] as a linear, high-throughput extension
of Ouroboros Praos, and is being implemented in `cardano-node` against the
still-draft `Dijkstra` ledger era and exercised on an early public testnet. This
report is a status overview of that implementation: the key components, the
workflows that connect them, and the notable highlights and open questions across
the design landscape as of 2026 Q2. It is intentionally anecdotal rather than
exhaustive — a snapshot of where things stand and what was learned, not a
specification.

Two documents remain authoritative and living and own the specification role:
[CIP-164][cip-164] for the protocol, and the node-level
[`leios-design`](./leios-design/README.md) document for the implementation
design. This report points to these documents, and other notable materials,
throughout. It is provided in support of a project milestone.

### Scope

The report spans the components and workflows of `cardano-node` touched by
CIP-164, ordered roughly by the protocol flow: resource prioritization and
transaction flow first; then block and endorser-block production, diffusion, and
the transaction cache; then voting, certification, and the validation and
adoption of certified blocks; catching up; the voting and cryptographic
components that support them — committee selection, key registration, and
cryptographic primitives; and finally serialization, protocol parameters, and the
node API.

Each topic states its status and highlights rather than its full design, and the
selection deliberately does not mirror the [technical design
document](./leios-design/README.md#technical-design) section-for-section. Each
opens with a short status line along a rough ladder — from requirements captured,
through prototype, settled design, and implementation, to high confidence (the
mainnet bar of audit, conformance, and performance). The ladder is
a loose guideline only: the stages are not strictly sequential, one component
often sits at different points for different aspects (a settled design alongside
an early implementation, say), and the line conveys roughly how far the work has
come rather than a precise grade. Because requirements are captured for everything, the status lines normally omit
that baseline and begin from what is actually built or settled; the exception is a
component whose requirements the original CIP did not capture well, where
re-establishing them during implementation is itself a step worth noting. The
high-confidence stage is deliberately last and is taken up in the
[Conclusion](#conclusion).

### Audience

The report is written for a technical reader: node developers and researchers
working on or alongside Leios, stake pool operators preparing to run it, and
project milestone reviewers. It assumes familiarity with Ouroboros Praos
and the broad shape of Leios and does not reintroduce them.

## Component status

### Praos-over-Leios prioritization

**Status:** prototype available; design maturing.

Keeping Praos ahead of Leios was the immediate focus at the project's start and
the first thing to spark network-level investigation, since Leios may only use
the resources Praos leaves idle — the requirement is Praos > fresh Leios > stale
Leios. Turning the opening question (does EB traffic actually disrupt Praos?)
into an [experiment][oc-1701] — a small prototype relaying a Praos block while a
large EB crosses the same link — first pointed at buffer bloat, a multi-megabyte
EB delaying the small Praos block stuck behind it in an over-full buffer. That
proved something of a red herring: it depends on misconfigured, consumer-grade
equipment rather than the well-provisioned hosts most stake runs on, and the
isolation mechanisms below contain it. More striking was the opposite result —
over a single hop, heavy Leios traffic has been observed to _reduce_ Praos block
latency, because the steady stream holds the TCP congestion window open and
spares the connection the slow-start an idle link would otherwise suffer.

The current understanding is that two mechanisms together give sufficient
isolation between the Praos and Leios mini-protocols. The node's multiplexer is
already intentionally fair across mini-protocols, and because Praos and Leios
ride different ones, that fairness alone may keep Praos timely (a [mux
demo][on-5261] and [egress-fairness work][on-5271] are sharpening it); separately,
bounding the kernel-level send buffer — for example via `TCP_NOTSENT_LOWAT` —
stops a large Leios write from queueing ahead of a Praos message. Explicitly
weighing Praos over Leios with a multiplexer bias remains an option for a
stronger guarantee, but it carries risks — over-biasing wastes the idle capacity
Leios exists to use — and may be unnecessary, so prototypes should measure first.
The harder contention risks, GC pressure and disk bandwidth under a worst-case
burst, resisted the simulations behind the CIP and remain judgeable only by
prototype.

Open question: how much explicit prioritization, if any, is needed beyond a fair
multiplexer and bounded kernel buffers — with the minor wrinkle that the
send-buffer socket option (`TCP_NOTSENT_LOWAT`) is not universally portable;
freshest-first delivery (younger EBs before older) is harder still and likely
needs server-side request reordering.

Primary sources: [design doc §Resource management](./leios-design/README.md#resource-management), [§Traffic prioritization](./leios-design/README.md#traffic-prioritization), [§Message latencies](./leios-design/README.md#message-latencies).
Monthly reviews: the networking investigation ran through the autumn — [October 2025][mr-2025-10] demoed the first prototype measuring EB-traffic impact on Praos, and [November 2025][mr-2025-11] dug into the EB-versus-Praos latency interaction (the Toxiproxy-to-Linux-traffic-control switch and the buffer-bloat analysis). The measurements matured past that early noise in spring: [April 2026][mr-2026-04] ran a proper Linux-traffic-control test bed (netem/fq_codel) probing single-hop TCP behaviour, and [May 2026][mr-2026-05] reported the corrected DeltaQ congestion-control analysis — Cubic meeting the latency target across high-latency links where the conservative Reno falls short.

### High-throughput transaction submission

**Status:** implementation maturing; delivered via `ouroboros-network` v2, off the CIP track.

Leios raises the target consensus data rate well above Praos, and the available
transaction volume always exceeds what consensus can include, so the
transaction-submission layer that replicates mempools between nodes must sustain
a rate exceeding the target Leios rate — otherwise the
[high-throughput mempool](#high-throughput-mempool) starves and EBs never fill.
This is a Praos-era component pushed well past its original operating point
rather than a new Leios protocol.

Today's node uses the legacy protocol, which fetches every offered transaction
from every peer that announces it. That is simple and robust but duplicates a
great deal of traffic, and the wasted CPU, memory, and bandwidth is exactly the
headroom Leios needs. A [version-2 protocol][on-5336] is being rolled out to cut
that waste; of its variants, the ["undecision" variant][on-5337] — which makes
per-peer fetch decisions through shared STM state rather than routing everything
through a central coordination thread — sustains the highest data rates across
realistic peer valencies and is the candidate that best fits the requirement.
Because the savings help Praos too, none of this is Leios-specific.

The headline measurement is stark. Replicating a 900 kB backlog of 500
transactions over a bandwidth-shaped link, the legacy protocol took around nine
seconds with only about a tenth of the bytes on the wire useful (the rest
duplicate fetches); the undecision variant completed the same transfer in
roughly 1.6 seconds with about three-quarters of the bytes useful — nearly six
times faster. Widening the in-flight window helped only when paired with the
per-peer decision logic: the central-coordination variant got faster but stayed
just as wasteful.

Open question: whether the chosen variant sustains the required rate across
realistic peer valencies and geographies — separate stress testing has already
shown throughput falling short in high-latency regions, though there the
bottleneck pointed at the mempool rather than at submission.

Primary source: [design doc §High-throughput transaction submission](./leios-design/README.md#high-throughput-transaction-submission).
Monthly reviews: [April 2026][mr-2026-04] presented the v2 margin simulations (legacy ~9 s at ~9% efficiency versus the undecision variant ~1.6 s at ~78%); [May 2026][mr-2026-05] stress-tested submission and the mempool over a realistic, less-connected topology, where high-latency regions could not saturate despite spare CPU.

### High-throughput mempool

**Status:** need confirmed; design ideas only, no prototype yet.

The mempool is the component under the most revalidation pressure in Leios, and
it is the least settled: the need is clear, but there is no prototype yet — only
competing design ideas. Two things make it hard. First, today's mempool
revalidates its whole contents against the currently selected ledger state
whenever chain selection changes, and in the current node everything else —
transaction diffusion, block forging, adding transactions — waits while it does;
at Leios load (a mempool measured in tens of megabytes against a sustained
high-transaction-rate stream) a single resync can take on the order of tens of
seconds. Second, Leios adds a double-ledger-state problem: certifying an EB
induces a new ledger state, so a transaction valid against the base state may be
invalid once the EB is applied, and a mempool built on the base state can be
largely irrelevant to the very block that certifies an EB.

The need itself is not in doubt — it surfaced in stress testing, where
high-latency regions could not saturate their mempools despite ample spare CPU,
and it was discussed with other implementers at the node-diversity workshop. The
response splits into two tiers. An immediate, fairly well-understood improvement
keeps the existing mempool but decouples transaction diffusion from
revalidation (so diffusion no longer stalls during a resync) and enlarges the
mempool to at least twice an EB's capacity so a certificate-bearing RB can still
carry a full fresh EB. Beyond that, a mid- to long-term redesign toward a DAG-based
ledger and mempool — potentially maintaining two mempool views, one per ledger
state — could handle the throughput far more cleanly, but it is a deeper,
higher-risk and higher-reward change whose shape is still open.

Open question: whether the incremental improvement suffices for the testnet and
early mainnet, or whether the DAG-based redesign proves necessary — and which of
the redesign ideas survive contact with a prototype.

Primary sources: [design doc §High-throughput mempool](./leios-design/README.md#high-throughput-mempool), [§Block production](./leios-design/README.md#block-production).
Monthly review: [May 2026][mr-2026-05] laid out the mempool redesign problem — the revalidation overhead, the double-ledger-state complication, and the two-mempool / DAG-ledger ideas — alongside a stress test showing high-latency regions unable to saturate the mempool despite spare CPU.

### Block production

**Status:** well understood; basic operation in the prototype; EB announcement and pre-application still to cover.

The forge thread now issues an EB alongside each RB unless the EB would be empty;
because the EB hash sits in the RB header, the RB payload, the EB, and the RB
header are decided together in one thread. Basic operation is demonstrated in the
[prototype][ol-690] — EBs are forged and diffused — and the mempool must hold at
least twice an EB so a certificate-bearing RB can still carry a full fresh EB.

Two things are deliberately short-cut for now. The prototype either certifies an
EB or announces a new one in a given opportunity, not both, forgoing roughly half
the block opportunities; [pre-application][ol-838] closes this by rebasing the
mempool onto the ledger state induced by the certified EB before selecting the
next EB's transactions, at the cost of a heavier forge loop. EB announcement is
the part with the most design choice still open ([prototype issue][ol-772]): two
block structures are on the table — an enhanced Praos header carrying the
KES-signed EB hash (CIP-164's approach), or dedicated EB headers if that proves
simpler — while the surrounding rules are settled (forward one announcement plus
one equivocation proof per block opportunity, and drop announcements older than
3·L_hdr). Announcement is where EB equivocation detection lives, and since that
defeats most stake-based threats it makes a natural early red-team/blue-team
exercise on the testnet.

Open question: which block structure carries EB announcements (enhanced Praos
header vs dedicated EB headers) — the report has no dedicated section for it and
it needs more coverage — and whether pre-application closes the CertRB forge-time
gap within the slot.

Primary source: [design doc §Block production](./leios-design/README.md#block-production).
Monthly reviews: [February][mr-2026-02] and [March 2026][mr-2026-03] demoed EB production and inclusion (with announcement still in the block body), and [April 2026][mr-2026-04] moved announcements into the header per the SIP.

### Endorser block diffusion and storage

**Status:** prototype available; design maturing.

Acquiring endorser blocks has been the central design effort of recent months:
the prototype's fetch logic is adequate for demos but has poor worst-case
resource bounds, and CIP-164's message-delay limits were derived from an
over-abstracted network stack. The [fetch-logic redesign][ol-853] therefore aims
for timely, verifiable EB availability with bounded resource usage and bounded
tail latency, robust to bursts and storms. A [baseline LeiosFetch
design][fetchlogic] keeps freshest-first fetching as the starting point; the
refinements below make delivery predictable enough to keep certified EBs within
the protocol's diffusion budget.

Two ideas carry the fetching design, set out in an [EB-availability
analysis][eb-avail]. First, each node keeps a small stake-sampled
set of big-ledger peers; once an EB's voting window closes, it
fetches the full certified EB from whichever of those peers advertise it. Because
certification implies that a large share of stake has already seen the EB, this
places certified EBs within a small number of hops of almost all honest nodes. Second,
everything else is fetched fine-grained: the producer splits the EB into
Merkle-tree parts and a node requests different parts from different peers, each
validated by its inclusion proof. Spreading requests across all peers is what
bounds tail latency — no single slow or adversarial peer can hold up delivery —
while keeping worst-case waste to a small multiple of one EB. Equivocation is
contained by fetching only one body per block-production opportunity, the first
header seen.

Two distinct threats motivate the storm-handling rules: a protocol storm is a
by-chance clustering of honest block-production opportunities, while a protocol
burst is an adversary withholding EBs and releasing them together at the worst
moment. Both are countered by reversing the download order to oldest-first
within the critical diffusion window, so the clustering becomes observable before
voting, then returning to freshest-first afterwards — paired with a voting rule
that abstains when too many headers appear in a short window (the chance storm)
and a rule that deprioritizes EBs whose headers arrive suspiciously late (the
adversarial burst). Together these bound the higher-priority traffic that can
compete with a certified EB during its window. The work is closely intertwined
with the network-delay analysis: the header-, voting-, and diffusion-window
budgets it relies on are being put on a mainnet-realistic footing through
[improved DeltaQ analysis][ol-889] and new topology simulations, since the worst
cases are hard to exercise any other way.

For storage, a node retains EB closures up to the immutable tip and indefinitely
once the immutable chain certifies them — closures are large and long-lived
because of possible deep Praos forks. The defining challenge is the sheer count:
in the worst case a node must hold on the order of ten thousand work-in-progress
EB closures at once, bounded by the densest run of Praos elections still inside
the immutable window. A baseline redesign therefore bounds memory, CPU, and disk
with a fixed on-disk budget for these work-in-progress EBs, hard limits on
in-flight requests, and reuse of the [transaction cache](#transaction-cache);
whether to keep this bespoke or delegate to an embedded store such as SQLite is
still being assessed by microbenchmark.

Open question: the storage-backend choice, and — more fundamentally — whether
realistic-topology behavior matches the simulation and DeltaQ modeling the CIP
parameters rest on.

Primary sources: [design doc §Endorser block diffusion](./leios-design/README.md#endorser-block-diffusion), [§Endorser block storage](./leios-design/README.md#endorser-block-storage).
Monthly reviews: Nick Frisby presented EB fetching across three consecutive sessions — [February][mr-2026-02] (prototype demo, plus retention and transaction-cache sizing), [March][mr-2026-03] (SQLite benchmarks, bounded-resource fetch, and the first protocol-storm realization), and [April][mr-2026-04] (the fetch decision logic — tail-latency prior art and a TCP/BBR test bed); Yves Hauser's DeltaQ EB-diffusion model also featured in [March][mr-2026-03].

### Transaction cache

**Status:** design understood; not yet in the prototype (a known gap).

In Leios as designed in CIP-164, EBs reference transactions by hash rather than
carrying them, so a transaction is transmitted once — as it diffuses between
mempools — and not again inside every EB that references it. Avoiding that
re-transmission is essential to high throughput: re-sending transactions would
consume the very bandwidth the protocol needs to raise its data rate. The
transaction cache is what makes the by-hash scheme work in practice, and it also
conserves the validation work: it retains transactions seen via EB diffusion or
through the mempool, so an EB referencing a fee-paying transaction the node has
already transferred and validated costs neither a re-fetch nor a re-validation,
even once the transaction has left the mempool. This matters most under load, as
mempools start to fragment — nodes drifting toward different transaction sets —
and a node can no longer assume an EB's transactions are still to hand. It is also
what keeps a skipped EB useful: an EB not certified in its round is not lost,
since its cached closure can be re-endorsed and certified later rather than
reassembled from scratch. The cache thus underpins the diffusion timeliness the
protocol's safety argument relies on, yet it is absent from the prototype — an
inconvenient gap given that role.

Sizing is settled. A "perfect" 36-hour cache would index ~165 million
transactions (several GB) and is excessive; a Markov-model analysis shows EBs are
still certified at a high rate even at modest hit rates, so a 15-minute retention
window suffices — bounding the cache to roughly 100 EBs, about 1.5 million
transaction names, near 200 MB of RAM. Unlike the mempool (small, multidimensional capacity,
block-production-driven eviction), the cache is a large single-dimension store
with simple LRU eviction, best held off the GHC heap (fixed-size bytearrays
backed by an mmapped file) to avoid GC pressure under adversarial load.

Open question: closing the implementation gap, and confirming the 15-minute /
~200 MB sizing holds against realistic fragmentation rather than the modelled
worst case.

Primary source: [design doc §Transaction cache](./leios-design/README.md#transaction-cache).
Monthly review: [February 2026][mr-2026-02] presented the sizing — rejecting the 36-hour cache and deriving the ~1.5 M-name, ~200 MB bound from the mempool-fragmentation/Markov analysis.

### Voting and certification

**Status:** prototype available; design settled (shared with Peras); certificate aggregation implemented (peer-reviewed).

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
[Network simulations][sims-2026w18] on large topologies —
including an "everyone votes" mode that maximizes committee size — found
throughput and EB certification essentially unaffected by committee size at the
tested loads, which substantially reduces but does not eliminate the concern.
These topologies are still smaller than mainnet, so high
confidence is reachable only through large-scale load testing. Should the
dedicated mini-protocol prove inadequate, Peras' `ObjectDiffusion` is a less
efficient but workable fallback. The reassuring corollary is that this is a
throughput concern, not a safety one: an underperforming voting protocol can
only limit throughput, never compromise chain safety.

Primary source: [design doc §Voting and certification](./leios-design/README.md#voting-and-certification).
Supporting: [ouroboros-leios#790][ol-790]; [cardano-base#670][base-670]; [ouroboros-consensus#2068][oc-2068]; [network simulations (2026w18)][sims-2026w18].

### Block validation and adoption

**Status:** prototype available; design maturing.

Adopting a certified block means resolving its EB and applying that EB's
transactions to the ledger ([#774][ol-774]). The prototype first inlined those
transactions before handing them to the ledger; the current design follows the
ledger's own path more faithfully — verify the certificate (against the voting
committee held in the ledger state, during block-body validation), resolve the EB
closure and read the disk-backed (UTxO-HD) state, re-apply the already-validated
transactions, then apply the full block. Applying an EB's transactions without
re-validating them — they were validated as they diffused — is what keeps
adoption affordable, and that path already exists in the ledger; what is missing
is performance benchmarking, especially against a disk-backed ledger state. Early
ledger benchmarks put the no-validation speed-up at roughly 5× for value
transactions and 50× for script transactions.

A certified RB cannot be adopted until the certified EB's closure is available,
and that gap must be detected rather than silently stalling. A first "staging
area" design ([#890][ol-890]) held such a block aside until its closure arrived;
it is being refined into a more holistic chain-selection extension
([#2076][oc-2076]) that treats a missing EB closure like a missing or
out-of-order block body — filtering those candidates, fetching the closure, and
re-triggering selection. Beyond these two threads, the work is largely an
internal reshuffle of responsibilities across the consensus/ledger API, including
the block-body rule update that carries certificate verification
([cardano-ledger#5872][ledger-5872]).

Open question: completing validation benchmarking on a disk-backed ledger, and
finalizing the chain-selection treatment of missing EB closures.

Primary sources: [design doc §Chain selection](./leios-design/README.md#chain-selection), [§Block validation](./leios-design/README.md#block-validation).
Monthly reviews: [April 2026][mr-2026-04] presented the ledger validation benchmarks; [May 2026][mr-2026-05] demoed the late-joiner fix, replacing the staging area with chain-selection filtering for missing EB closures.

### Catching up

**Status:** baseline syncing in the prototype; efficient design maturing.

A node that has fallen behind must fetch and replay historical EBs and their
closures to rebuild ledger state. The prototype already syncs by way of the
out-of-order chain selection built to handle missing EB closures (the mechanism
described under block validation and adoption); that is the current baseline.

A more efficient catch-up path is certainly wanted, and its shape has been clear
since the CIP was drafted last summer: mirror BlockFetch's range requests into
LeiosFetch, so a catching-up node can request spans of historical EBs the way it
already requests spans of blocks. The mini-protocol structure was refined
recently in the CIP following Builder Fest discussions ([CIPs#1167][cip-1167]),
with the underlying information-flow model unchanged. None of this raises a large
open question.

Open question: whether LeiosFetch should carry catch-up directly — competing with
serving already-synced peers — or whether a dedicated protocol keeps the concerns
cleaner.

Primary source: [design doc §Catching up](./leios-design/README.md#catching-up).
Monthly review: [May 2026][mr-2026-05] demoed the late-joiner path that the baseline syncing rests on.

### Committee selection

**Status:** prototype available (interim all-vote); design settled (simplified, stake-based truncation).

The voting committee is now chosen by a stake-based truncation scheme that
replaces the earlier wFA^LS (weighted Fait Accompli with Local Sortition)
design, merged into CIP-164 as [CIPs#1196][cip-1196]. At each epoch boundary
pools are ordered by stake and taken until a configured cumulative-stake target
is met; every member then votes on every EB in the epoch, with no per-EB
elections, non-persistent voters, or sortition proofs. The certificate collapses
to a bitfield over the known committee plus one aggregated BLS signature, and
quorum becomes a minimum fraction of total active stake rather than a head-count.
BLS12-381, the quorum threshold, certificate timing, the mini-protocols, and the
threat model are all unchanged.

The motivation is certificate size and verification cost on the critical path,
which wFA^LS dominated through non-persistent voters' eligibility proofs.
Benchmarked against mainnet stake with [leios-wfa-ls-demo][wfa-ls-demo] at
coverage equivalent to the wFA^LS reference, the certificate shrinks by more
than an order of magnitude and worst-case verification falls severalfold, while
the committee still covers nearly all active stake; the coverage threshold is
stable and gently decreasing across recent epochs. The exact figures live in the
demo and the CIP.

The prototype ([ouroboros-consensus#2068][oc-2068]) performs certificate
aggregation and validation per CIP-164 but still selects committees with an
interim "all-vote" scheme rather than the final stake-based truncation.

Open question: where the selected committee state lives in the codebase —
materialized in the ledger state versus computed on demand at the epoch boundary.

Primary source: [design doc §Committee selection](./leios-design/README.md#committee-selection).
Supporting: [CIPs#1196][cip-1196]; [leios-wfa-ls-demo][wfa-ls-demo]; [ouroboros-consensus#2068][oc-2068].

### Key registration and rotation

**Status:** key-generation tooling implemented; registration design maturing.

To take part in Leios voting, an SPO registers a BLS key alongside its existing
VRF and KES keys; the committee is drawn from the registered keys. `cardano-cli`
can already generate a BLS key, hash it, and issue its proof of possession
([#1355][cli-1355], [#1356][cli-1356]), which guards against rogue-key attacks —
but that is the extent of it: only generation exists today, with no registration
or rotation yet. The prototype has moved to the Dijkstra era so the on-chain
registration path can be built, and the concrete design for how to register BLS
keys in Cardano is being written up now, with the [ARC voting-crypto
review][arc-voting] as the key reference.

The baseline — the least the protocol needs — follows the VRF precedent: carry
the BLS key and its proof of possession in the pool parameters via the
pool-registration certificate (existing pools re-register with the new fields, no
second deposit), pending Dijkstra ledger support. The need for rotation arose
when committee selection was refined, where adaptive security wants the voting
key rotated rather than fixed for a pool's lifetime. A more desirable mechanism
is being sketched: registering and rotating BLS keys via produced blocks,
analogous to the KES operational certificate — it needs no transaction sent to
the network and allows more frequent rotation.

Open question: which rotation mechanism to adopt (pool-certificate re-registration
versus a block-carried, opcert-style key) and the cadence the crypto review calls
for.

Primary sources: [roadmap issue][ol-776], [design doc §Key registration and rotation](./leios-design/README.md#key-registration-and-rotation).
Monthly reviews: [April 2026][mr-2026-04] demoed BLS key generation and proof of possession in `cardano-cli`; [May 2026][mr-2026-05] moved the prototype to the Dijkstra era to unblock on-chain registration.

### Cryptographic primitives

**Status:** prototype available; design settled; implemented; primitives audited, certificate layer peer-reviewed.

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

### Serialization

**Status:** design settled; implementation maturing.

The prototype was first built on the Conway era — a stable, well-established
foundation — and has recently moved to the still-draft Dijkstra era. Dijkstra is
a faster-moving target to integrate against and to run a testnet on, but it is
where Leios's on-chain changes will actually land, so tracking it lets the team
mature key pieces from prototype toward a production-grade implementation rather
than redoing Conway work later.

The serialization changes themselves hold no real unknowns; the demand is driven
by other features. The central one is the ledger change extending the block body
to carry the certificate and EB reference ([cardano-ledger#5872][ledger-5872]);
EB announcement in block headers, and key registration via transactions or
headers, will likewise require encoding changes. Getting these encodings into
Dijkstra is the minimum needed for Leios support in a hard fork — the block
format can be present while ledger validation is withheld until a later intra-era
hard fork enables it (see the design doc's [era and hard-fork
coordination](./leios-design/README.md#era-and-hard-fork-coordination)).

Open question: none specific to the encodings; the open items sit with the
features that drive them — the EB-announcement block structure and the
key-registration mechanism.

Primary source: [design doc §Era and hard-fork coordination](./leios-design/README.md#era-and-hard-fork-coordination).
Supporting: [cardano-ledger#5872][ledger-5872].
Monthly review: [May 2026][mr-2026-05] reported the prototype's move to the Dijkstra era.

### New protocol parameters

**Status:** placement well understood; parameter set being finalized; not implemented yet.

Adding Leios's parameters to the ledger's updatable protocol-parameter set is
well-understood practice; the only real question is which parameters. The CIP
already carries a good set, and the open discussion is whether to future-proof
it — in particular, whether to allow higher per-transaction Plutus limits inside
EBs than a Praos block permits ([ongoing CIP discussion][cip-1213]).

The prototype currently hard-codes its parameters — configuration overrides and
governance-updatable parameters are not implemented yet. That work belongs to the
parameter-exploration phase of the testnet, and the governance-updatable
parameters will also need guard rails added to the Cardano constitution to bound
their permitted values.

Open question: the future-proofing decision on per-transaction Plutus limits in
EBs, and which parameters should be governance-updatable from the outset versus
set through configuration overrides during testnet exploration.

Primary source: [design doc §New protocol parameters](./leios-design/README.md#new-protocol-parameters).
Supporting: [ongoing CIP discussion][cip-1213].

### Node API and configuration

**Status:** client-facing prototype validated on the testnet; new queries still to add.

Leios features will be gated behind feature flags — a mechanism already
bootstrapped by Peras ([cardano-peras#96][peras-96]) — once the first
production-grade components are ready; that lets them ship incrementally in the
11.x node releases ahead of activation.

On the local-state-query side there is nothing ground-breaking: the existing
queries mainly need wiring up for the new Dijkstra era (done in part for the
testnet), and a few new queries remain to be created for the new ledger state —
for instance the selected voting committee.

The significant change is the node-to-client chainsync API. By presenting a
certified block and its EB closure to clients as a single larger "inlined" block
([prototype][ol-898]), most downstream infrastructure keeps working unchanged
despite the bigger blocks, which sharply limits the blast radius of Leios across
the ecosystem. This is being validated on the early testnet; updating `db-sync`
proved straightforward and already backs a Leios block explorer
([kleioscan][kleioscan]).

Open question: the remaining new ledger-state queries, and confirming the inlined
chainsync presentation holds across the breadth of existing clients.

Primary sources: [design doc §Node-to-client](./leios-design/README.md#node-to-client), [§Feature flags and configuration](./leios-design/README.md#feature-flags-and-configuration).
Supporting: [cardano-peras#96][peras-96]; [chainsync prototype][ol-898]; [kleioscan explorer][kleioscan].

## Conclusion

The defining event of the period is that Leios left the drawing board for a live
network. The public [Musashi testnet][musashi] (network ID 164) is bootstrapped,
already hosting three independent (prototypical) node implementations alongside a
deliberately adversarial red team. On it, the prototype produces, diffuses, votes
on, certifies, and adopts endorser blocks end to end; downstream tooling such as
`db-sync` and a block explorer already follows along. The prototype is
progressing well and the design is converging.

Real work remains. The central open problem is acquiring endorser blocks with
bounded worst-case resource use and low tail latency, robust to bursts and
storms; bound up with it is the transaction cache, essential to conserve transfer
and validation work yet still missing from the prototype, and a high-throughput
mempool that today exists only as competing design ideas. Even so, these are not
leaps in the dark: the designs are compelling, and independent experiments
suggest they are feasible even in adversarial settings. Beyond closing these
gaps, the bar for mainnet — the deliberately-last "high confidence" stage — is
the most demanding of all: independent audit of the certificate layer,
conformance across implementations, performance benchmarking against a
disk-backed ledger, and empirical validation of the security assumptions under
adversarial, realistic-topology load. None of that is quick.

Even so, the shape of the effort is encouraging. The changes a node actually
needs are comparatively few and contained — many are Praos-era components pushed
past their old operating points rather than new subsystems, the serialization
required to enable Leios in a hard fork is minimal, and the node-to-client
"inlined block" lets most of the ecosystem keep working unchanged. Much of this work has precedent and prior art to build
on, and Leios's overlap with Peras — in key registration, voting,
certificate verification, and shared BLS cryptography — opens real synergies (see the design doc's
[synergies with Peras](./leios-design/README.md#synergies-with-peras)). Building
production-grade components is demanding but feasible, the more so at the modest
parameter targets mainnet will naturally start from. And the quarter's progress
on threat modeling, simulation, analytical (DeltaQ) modeling, and adversarial
testing is exactly the shared evidence base from which the Cardano community can
collectively establish high confidence — in the protocol and in a diversity of
independent node implementations.

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
[ol-774]: https://github.com/input-output-hk/ouroboros-leios/issues/774
[ol-890]: https://github.com/input-output-hk/ouroboros-leios/issues/890
[oc-2076]: https://github.com/IntersectMBO/ouroboros-consensus/pull/2076
[cli-1355]: https://github.com/IntersectMBO/cardano-cli/pull/1355
[cli-1356]: https://github.com/IntersectMBO/cardano-cli/pull/1356
[ol-776]: https://github.com/input-output-hk/ouroboros-leios/issues/776
[arc-voting]: https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/arc-voting-crypto-review.pdf
[on-5336]: https://github.com/IntersectMBO/ouroboros-network/issues/5336
[on-5337]: https://github.com/IntersectMBO/ouroboros-network/issues/5337
[wfa-ls-demo]: https://github.com/cardano-scaling/leios-wfa-ls-demo
[crypto-rs]: https://github.com/input-output-hk/ouroboros-leios/tree/main/crypto-benchmarks.rs
[cip-1196]: https://github.com/cardano-foundation/CIPs/pull/1196
[cip-1167]: https://github.com/cardano-foundation/CIPs/pull/1167
[cip-1213]: https://github.com/cardano-foundation/CIPs/pull/1213
[peras-96]: https://github.com/tweag/cardano-peras/issues/96
[ol-898]: https://github.com/input-output-hk/ouroboros-leios/issues/898
[kleioscan]: https://kleioscan.com/#/leios/leios
[oc-2068]: https://github.com/IntersectMBO/ouroboros-consensus/pull/2068
[ol-790]: https://github.com/input-output-hk/ouroboros-leios/issues/790
[ol-690]: https://github.com/input-output-hk/ouroboros-leios/issues/690
[ol-772]: https://github.com/input-output-hk/ouroboros-leios/issues/772
[ol-838]: https://github.com/input-output-hk/ouroboros-leios/issues/838
[sims-2026w18]: https://github.com/input-output-hk/ouroboros-leios/tree/main/analysis/sims/2026w18
[fetchlogic]: https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/targeted-design-investigations/a-baseline-LeiosFetch-design/LeiosFetchLogic.md
[ol-853]: https://github.com/input-output-hk/ouroboros-leios/issues/853
[ol-889]: https://github.com/input-output-hk/ouroboros-leios/pull/889
[eb-avail]: https://docs.google.com/document/d/1L2sWKqk96XfHToWXBcz82Tey69lFnsdGBlvEDNLw0HM/edit
[mr-2026-02]: https://youtube.com/live/5uAJ-XBAysY
[mr-2026-03]: https://www.youtube.com/live/_FkCLJLTNco
[mr-2026-04]: https://www.youtube.com/live/IYDMqkEPLDs
[mr-2025-10]: https://www.youtube.com/watch?v=5baqGY7WXAc
[mr-2025-11]: https://youtube.com/live/rraKzt-JIqM
[mr-2026-05]: https://www.youtube.com/live/Z4uA9tRGS7g
[oc-1701]: https://github.com/IntersectMBO/ouroboros-consensus/issues/1701
[on-5261]: https://github.com/IntersectMBO/ouroboros-network/issues/5261
[on-5271]: https://github.com/IntersectMBO/ouroboros-network/issues/5271
