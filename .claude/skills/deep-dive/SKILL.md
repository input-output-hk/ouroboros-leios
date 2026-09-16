---
name: deep-dive
description: Create a comprehensive technical deep-dive assessment of a blockchain, consensus protocol, or distributed system, with mandatory archival reconnaissance, primary-source verification, and a twelve-H2 skeleton. Use when asked for a deep dive, technical teardown, or comprehensive assessment of a system relevant to Leios.
---

# Skill: Deep Dive Assessment

Create a comprehensive technical deep-dive assessment of a blockchain or distributed system. The structure below is the canonical skeleton; this repository has no local exemplar yet, so link the first completed dive here once it exists.

## When to Use

Use this skill when asked to create a deep dive, technical teardown, or comprehensive assessment of a blockchain, consensus protocol, or distributed system. The subject should be a production, near-production, or seriously-specified system whose throughput, diffusion, or finality design bears on Leios — either as a comparator, as prior art for a mechanism Leios uses, or as a cautionary operational history.

## Inputs

- **Subject**: The blockchain, protocol, or system to analyze (e.g., a DAG-based mempool-and-consensus stack, a high-throughput L1, another Ouroboros variant)
- **Prior work** (optional): Path to a background assessment to build on (e.g., `assessments/<subject>-background.md`)

## Output

A new Markdown file at `assessments/<subject>-deep-dive.md`.

## Workflow Patterns

Two production workflows have been used to drive this skill end-to-end. The skill's Pipeline (below) describes the LLM-side stages; this section describes how the human and LLM iterate through them together. Either pattern is acceptable — the user typically signals which one. The LLM should ask if it isn't obvious.

### Pattern A — Section-at-a-time

The user asks for one H2 section at a time. The LLM drafts the section against the relevant stages of the pipeline; the user discusses, pushes back, asks for evidence, edits inline. When the section is in reasonable shape the user moves to the next H2. The document accretes H2 by H2; each section is settled before the next starts.

- **Pros.** Tight control. The document never gets out of shape, because the previous section is settled before the next starts. Disagreements are litigated immediately, while the relevant context is still loaded.
- **Cons.** Slower wall-clock. Cross-cutting structure (forward references, the §1 overview that depends on what §4–§9 will say) is harder to land early; the §1 Overview may need a final pass after the body is complete.
- **Best when.** The subject is unfamiliar to the user, has contested facts the user wants to litigate inline, or carries archival-vs-public disagreements that need careful adjudication per H2.

### Pattern B — Full-draft then iterate

The user asks the LLM to draft the entire document in one pass — all twelve H2s, Stages 0–3 of the pipeline executed end-to-end before any user review. Then the user walks through the draft H2-by-H2 with the LLM, discussing and editing.

- **Pros.** A complete artifact early. Forward references and the §1 Overview can be drafted with the body's actual content visible. The user sees the whole shape immediately and can prioritize editorial attention.
- **Cons.** Early sections may need rework once later sections reveal facts that shift the framing. The Stage-4 cross-check has more to verify; the editing pass tends to be longer in absolute terms.
- **Best when.** The subject is familiar to the user, the archival corpus is light or absent, or the user wants a complete shape early to share with stakeholders.

### When to run the qa-afterword skill

Both workflows converge on the same gate: **the qa-afterword skill must not run until the document is stable.** "Stable" means both LLM editing and the user's editorial pass have settled — no more H2 reorderings, no more substantial prose revisions, no more new sources being added. Running the audit on a moving target produces a stale snapshot that has to be redone after the next edit lands.

When the user signals the document is done, invoke the `qa-afterword` skill explicitly. Until then, the deep-dive skill does not produce an Afterword.

## Pipeline

Execute these stages in order. Do not skip Stage 0 or Stage 4 — they are what distinguish a deep dive from a web-research summary.

### Stage 0 — Archival reconnaissance (mandatory, do before any external research)

The project's `background/` corpus holds internal IOG and Cardano material that often carries primary or proprietary information not reproduced on the public web — internal benchmark runs, design memos, unpublished measurement reports. Skipping this stage means missing facts that are sitting on disk. *All paths in this skill are relative to the repository root; run commands from the repo root unless noted otherwise.*

1. **Search the archival corpus**: `grep -l -i -r "<subject>" background/drive/ background/confluence/ background/github/` for the subject and adjacent terms (consensus name, smart-contract language, VM, founders).
2. **Read every matching file**. Some are full whitepapers converted to Markdown; others are internal technical-intelligence dives, post-mortems, or Confluence design docs.
3. **Consult `background/archival-index.md`** for the master triage and per-file relevance / freshness annotations.
4. **Extract an archival fact list**: every quantitative claim, named author, date, protocol-config constant, and architectural fact the archival establishes about the subject. This becomes a checklist for Stage 4 (cross-check).

**If the archival corpus is absent on this branch or checkout** (`background/` missing, or contains no material on the subject): record that fact in Appendix A (one paragraph stating what was searched and that nothing was found), then proceed to Stage 1 with no archival fact list. This is a supported case, not a skill failure — primary-source rigor in Stage 1 carries the deep dive on its own.

### Stage 1 — Primary-source identification (mandatory)

For each of the following high-stakes claim categories, identify and open the primary source. Do not rely on secondary coverage.

- **Protocol authors**: open the whitepaper or formal-spec PDF/Markdown and read the title page.
- **Fault-model parameters** (n=3f+1, 20%+20%, etc.): open the whitepaper's "Assumptions" or "Threat Model" section.
- **Finality / commit-latency figures**: open the whitepaper's evaluation section and any official benchmarks published by the maintaining org.
- **Hardware-requirement minima**: open the maintainer's operations/validator documentation.
- **Named protocol constants** (block size, slot time, FEC parameters): open the canonical source repository's protocol-config file or formal spec.

Where the archival corpus (Stage 0) contains the primary source itself, use that copy as the citation target.

### Stage 2 — External research (optional parallel agents)

If the subject is large enough to warrant parallel research agents:

1. **Brief the agents with the Stage-0 fact list and Stage-1 primary-source URLs.** Each agent prompt must include: "Read these archival files first: [list]. Cite primary sources for these claims: [list]. Flag any contradiction with secondary coverage." **This is non-negotiable** — parallel agents without the Stage-0/Stage-1 brief silently produce secondary-sourced fluff that Stage 4 then spends disproportionate effort catching as drift. Front-load the brief and Stage 4 stays manageable.
2. Use parallel agents for breadth (one per H2 or pair of H2s). They are bad at deep verification but good at gathering structured coverage.
3. Distinguish source authority in agent output: **Primary** (whitepaper, formal spec, canonical source code), **Secondary** (maintainer docs, Helius/Anza-tier blogs), **Tertiary** (third-party analysis, news). Critical claims must cite Primary or carry SCRUTINY.

### Stage 3 — Draft

Compose the document using the structure in "Document Structure" below. SCRUTINY-flag any claim sourced only Tertiary or whose Primary source could not be opened.

### Stage 4 — Quality pass (mandatory, before marking Complete)

Before changing `**Status:** In progress.` to `**Status:** Complete.`:

1. **Cross-check against the archival fact list from Stage 0.** For each archival fact: mark it incorporated (with section reference), contradicted-with-reason (with citation to the primary source that overrides the archival), or omitted-with-reason (e.g., obsolete due to a subsequent protocol upgrade). No archival fact should be silently absent.
2. **Verify the top ~10 quantitative claims against the Stage-1 primary sources.** Specifically: authors, fault-model parameters, finality figures, hardware minima, named constants. Mismatches here are the most consequential errors a deep dive can carry.
3. **Append an `## Appendix A: Archival Corpus Cross-Check`** section recording (a) which archival files were consulted, with relative-path links, (b) discrepancies surfaced, separated into "deep dive correct / archival wrong," "deep dive wrong / archival correct," and "within-archival inconsistencies," (c) facts now incorporated, (d) gaps remaining. If no archival material exists for the subject, the appendix is one paragraph documenting that fact.

## Document Structure

### Front Matter

```markdown
# <Subject> — Deep Dive

**Created:** <today's date>
**Status:** In progress.
**Provenance:** <provenance marker per AGENTS.md>
**Upstream refs:** <commit / version / spec revision this dive describes, where the subject has one>

---
```

### Required H2 Sections (in order)

The following H2 sections form the standard skeleton. Not every H3 will apply to every subject — omit those that are genuinely irrelevant, but do not skip an H2 without justification. Adapt H3 titles to the subject's specifics (e.g., an object-model H3 becomes a record-model or UTxO-set H3 depending on the subject's ledger).

**H2 adaptation is also permitted when the subject's architecture warrants it.** A subject whose throughput story is dominated by one subsystem may replace `§7 Throughput` with an H2 on that subsystem, folding the throughput numbers into it rather than letting them stand alone. In this repository `§10 Privacy` is the most commonly substituted H2 — for most Leios comparators, a `§10 Data Availability and Storage Growth` treatment earns its place where a privacy treatment would not. The default skeleton fits most subjects; treat H2 substitution as a deliberate choice the deep dive justifies in its front matter or §1.6 Differentiating Features, not as silent drift.

#### 1. Overview
- **1.1 Raison d'Etre** — founding thesis, team, launch date
- **1.2 Deployment Summary** — table of key metrics (market cap, token price, supply, total transactions, validator count, staking, Nakamoto coefficient, epoch length, block time, finality, throughput, ledger size, transaction size, validator hardware). Include date and source for each metric. Use SCRUTINY markers on unverified estimates.
- **1.3 Security Incidents** — brief summary with forward reference to the Security H2
- **1.4 Technical Aspects** — summary table (layer, consensus family, consensus model, finality type, commit latency, leader election, data model, smart contracts, VM, network transport, execution model, privacy, token model, storage model, pruning, state growth defense, cross-chain)
- **1.5 Formal and Informal Specifications** — brief summary with forward reference to the Specifications H2
- **1.6 Differentiating Features** — numbered list of what makes this system architecturally distinctive

#### 2. Validator Hardware and Network Resources
- Minimum hardware table (CPU, RAM, storage, network)
- Comparison with Ethereum and Solana requirements
- Storage growth analysis
- Hosting cost estimates (with SCRUTINY)
- Bandwidth analysis from first principles (with SCRUTINY)

#### 3. Network Architecture
- Transport layer (protocol, authentication, multiplexing)
- Protocol layering and data dissemination (ports, data flow stages)
- Peer discovery and topology
- Notable network features (e.g., SCION, custom p2p libraries)
- **Network implications for Leios** — how these choices bear on Leios's diffusion and bandwidth requirements
- State synchronization and catch-up mechanisms
- RPC and client-facing API

#### 4. Consensus Algorithm
- Evolution (table of periods, stacks, and latencies)
- Fault model (BFT assumptions, quorum sizes)
- Core architecture (detailed mechanics, commit rules, diagrams where helpful)
- Transaction submission data flow
- Block dissemination
- Notable subprotocols (e.g., block synchronizers, reputation systems, leader scheduling)
- Dual/multiple transaction paths (if applicable)
- Finality (types, empirical latency, degraded-case analysis, tail latency gaps)
- Epoch reconfiguration

#### 5. Ledger Model
- Data model and ownership semantics
- Transaction structure (with struct definitions and examples where available)
- Data types and use cases
- Conflict resolution and locking
- Block/checkpoint structure
- State model and storage (live state, commitments, pruning, archival)
- Gas and fee model
- Transaction lifecycle end-to-end
- Versioning and history

#### 6. Smart Contracts
- Language design and type system
- Platform-specific extensions
- Module and package system
- Transaction composition (batching, atomic operations)
- Security model (with forward reference to Security H2)
- Gas and execution model
- Developer ecosystem (tooling, testing, SDKs, documentation)
- Standard library and framework
- Limitations and criticisms
- **Comparison table with Plutus/Cardano** (and with Solidity/EVM as the common reference point) — at least 12 dimensions

#### 7. Throughput
- Theoretical/controlled-test performance (table)
- Mainnet observed performance (table)
- Throughput commentary (contextualizing headline numbers)
- Throughput under adversarial conditions
- Throughput decomposition (phase-by-phase breakdown)
- Latency distribution / tail latency
- **Explicit `tx · MB/s` data-rate capacity (mandatory).** Resolve TPS-only throughput numbers into per-node and chain-wide byte throughput by combining TPS × average transaction size. Provide at least one workload-specific breakdown (e.g. simple transfer, script/contract call, the subject's heaviest common transaction class). Compare against the Cardano Praos baseline and the Leios throughput target, citing both from [`facts.md`](../../../facts.md) rather than restating them from memory; if `facts.md` does not yet record them, establish and record them there first. This dimension lets readers compare throughput across chains in a common unit and reason about diffusion bandwidth requirements explicitly — which for Leios is the crux, since bytes per second per node, not transactions per second, is what the network must actually carry.

#### 8. Security and Reliability
- Security incidents (table: date, incident, impact, root cause, resolution)
- Smart contract security (structural defenses, known vulnerability classes, major exploits)
- Attack surface (consensus-layer, network-layer, application-layer)
- Liveness incidents and recovery (network stalls, validator-set degradations, partition behavior)
- Governance and supply concentration concerns
- Audit history (table: auditor, scope, dates, key findings)
- Bug bounty program
- MEV and transaction ordering fairness

(*Use "Security and Reliability" rather than "Security": the heading has to cover liveness incidents alongside safety incidents, and for a throughput-scaling comparator the liveness and degraded-mode history is usually the more informative half.*)

#### 9. Validators, Governance, and Decentralization
- Validator set metrics (table)
- Validator selection and governance
- What limits the validator count
- Decentralization assessment
- Node implementations (single vs. multiple)
- Protocol upgrade mechanism
- Governance process
- Treasury and token supply (allocation table with vesting)
- **Comparison with Cardano's governance model**
- Slashing and penalties
- Validator economics

#### 10. Privacy
- Current state
- Planned privacy features
- **Privacy comparison with Cardano**
- Technical details of privacy mechanisms
- Privacy limitations and metadata leakage

#### 11. Specifications
- Specification inventory (table: artifact, scope, type, status)
- Notable formal verification results or findings
- Specification gaps
- Threat model (or note its absence)

#### 12. Relevance to Leios
This section is always the **last H2 before Sources**.
- Architectural lessons
- Which Leios design question the subject speaks to, named explicitly
- Mapping of the subject's block, mempool, and voting structures onto Leios's block classes and stages (if applicable)
- Key differences from Cardano's and Leios's context — stake distribution, node population, governance, and the longest-chain versus BFT-finality starting point
- Lessons from the subject's operational history for Leios, especially degraded-mode and adversarial behavior
- What of this would transfer to Leios, what would not, and what is untestable from outside

#### Sources
Organize into named H3 subsections by topic domain. Every entry in format:
```
- [Title — Publisher/Context](URL)
```

Where a source is one of the archival files in `background/`, include the relative-path link as the URL (e.g., `[<Subject> Whitepaper v1.0 (archival)](../background/drive/<file>.md)`) rather than the external URL — archival copies are stable and primary; external URLs can move. *If the archival corpus is absent (see Stage 0), cite the external URL directly; mark the lack of archival anchoring in Appendix A.*

#### Appendix A: Archival Corpus Cross-Check
Mandatory output of Stage 4. Structure:
1. **Archival files consulted** — list with relative-path links and one-line essence.
2. **Discrepancies surfaced**, split into three subsections: (a) deep dive correct / archival wrong, (b) deep dive wrong / archival correct, (c) within-archival inconsistencies (deep dive sides with more rigorous source).
3. **Archival facts incorporated into the deep dive** — table mapping archival facts to the deep-dive section that uses them.
4. **Gaps remaining** — facts the archival cannot resolve, with notes on whether external follow-up is warranted.

If no archival material exists for the subject, the appendix is one paragraph documenting that fact and any adjacent material that informs the subject indirectly.

## Conventions

1. **SCRUTINY markers**: Use `❓🤖 **SCRUTINY**` for unverified quantitative estimates or LLM-generated conclusions requiring particular scrutiny. Use `❓ **SCRUTINY**` for human-originated claims needing verification. Err on the side of marking — 40+ markers in a comprehensive deep dive is normal. **A SCRUTINY marker is mandatory** on any claim whose primary source could not be opened or whose only citation is a Tertiary source (news, third-party analysis).

1a. **Source authority tiers.** Distinguish:
   - **Primary** — original whitepaper, formal specification, canonical source-code repo's protocol-config file, the maintainer org's published reference. Always preferable.
   - **Secondary** — maintainer-org documentation site, well-known protocol-research blogs and engineering blogs of the maintaining organization.
   - **Tertiary** — news coverage, third-party explainers, ecosystem-aggregator summaries.

   Any claim sourced Primary may stand without SCRUTINY. Claims sourced only Secondary or Tertiary must either carry SCRUTINY or be cross-checked against a Primary source during Stage 4. If Primary and Secondary disagree, resolve in favor of Primary and note the discrepancy.

2. **Provenance markers**: Per [AGENTS.md](../../../AGENTS.md) — use 🤖 (LLM-generated, human-reviewed), 👱🤖 (human-drafted, LLM-refined), 🤖👱 (LLM-drafted, human-refined), or unmarked (human only).

3. **Semantic markers**: Use 🧪 HYPOTHESIS, 📊 EVIDENCE, 🛑 BLOCKER, 🏛️ ADR, 🛡️ SPEC, ⚠️ RISK as appropriate per [AGENTS.md](../../../AGENTS.md).

4. **Cross-references**: Use `§N` or `§N.M` notation for internal cross-references. When security or specification content appears in overview sections, add a forward reference ("See §8 Security for the full treatment").

5. **Tables over prose**: Prefer tables for structured comparisons, metrics, and inventories. Use prose for analysis, explanation, and argument.

6. **Examples**: Include code examples (struct definitions, transaction structures) where the subject's source code or documentation provides them. Simplify for clarity, noting omissions.

7. **Mermaid diagrams**: Use for consensus commit rules, transaction lifecycles, or protocol architectures where visual representation adds clarity. Use real line breaks in node labels (not `\n`).

8. **American English spelling** throughout.

9. **Protocol cheatsheet**: After creating the deep dive, update [`artifacts/leios-cheatsheet.md`](../../../artifacts/leios-cheatsheet.md) with any newly covered protocols or mechanisms. Each entry needs at least one source link.

10. **Journal entry**: After creating the deep dive, add a reverse-chronological journal entry in the current phase logbook under `journal/` (e.g., `journal/phase-0.md`). Inspect the directory to find the active file; the entry goes as the first H3 under today's H2 section, and carries the same provenance marker as the deep dive itself.

11. **Follow-up work**: If the deep dive identifies follow-up work, file it with the [`ticket-create`](../ticket-create/SKILL.md) skill against whichever repository and ProjectV2 board this effort is tracked on. That target is not yet fixed — see that skill's Board section — so confirm it with the user before filing rather than guessing.

## Quality Targets

- **100+ H3 sections** for a comprehensive deep dive of a major system
- **40+ SCRUTINY markers** — epistemic humility is a feature, not a defect
- **Tail-latency analysis** for the consensus section — not just median/mean
- **Leios comparison** in every relevant section, not just the final H2
- **Layer named** on every quantitative claim: paper, formal specification, simulator, implementation, or deployed network
- **No unsourced quantitative claims** — either cite a source or mark SCRUTINY
- **Sources section** with 50+ references organized by topic
- **Stage-0 archival reconnaissance executed**, with at least one of: a populated Appendix A listing consulted files, or an Appendix A documenting that no archival material exists
- **Top ~10 quantitative claims cite Primary sources** (Stage 1) — authors, fault model, finality, hardware minima, named constants
- **No Primary-vs-Secondary contradiction left unresolved** in the body of the document

## Quality-Scrutiny Afterword

The five-subsection `## Afterword: Quality Scrutiny` review described in [AGENTS.md](../../../AGENTS.md) is **not** part of this skill. It runs *after* all LLM and human editing on the deep dive has settled — including the human editorial pass that follows initial generation. Treating it as a step in the deep-dive pipeline encourages running it while content is still in flux, which wastes effort and produces a stale audit.

When (and only when) the user explicitly asks for a quality-scrutiny pass on a completed deep dive, invoke the [`qa-afterword`](../qa-afterword/SKILL.md) skill. That skill expands each of the five subsections into a concrete procedure and is shared across document types (deep dives, weekly reports, assessments, technical reports).
