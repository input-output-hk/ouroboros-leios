# Leios requirements

Ouroboros Praos, the consensus protocol securing Cardano mainnet, provides two guarantees that underpin the chain's value: **persistence** — confirmed transactions are immutable, so history can be neither forged nor rewritten — and **liveness** — new valid transactions are eventually included. Both rest on timely block diffusion: blocks must reach nearly all stake within the $\Delta$ parameter (5 seconds), and Praos deliberately leaves the network idle between blocks so that this holds even in the worst case. Leios ([CIP-164](https://cips.cardano.org/cip/CIP-0164)) uses that reserved headroom to add **high throughput** as a third guarantee: block producers may announce a larger endorser block (EB) alongside each Praos block (now a ranking block, RB), whose transactions enter the ledger only once a stake-weighted committee has certified their availability and validity and the certificate is anchored in a subsequent RB.

This document enumerates the requirements that Leios must satisfy as implemented and deployed. See [Notation](#notation) below for the assurance tags and rules of use.

**Preserve Praos persistence and liveness**

1. Ensure that Praos RBs are always transferred and accepted under the same network and stake conditions (and limits thereon) that they are now: RB diffusion and adoption continue to meet the existing $\Delta$ budget (5 seconds to reach $\geq 95\%$ of nodes) in the presence of maximal Leios traffic and computation. [S, B]
2. Ensure that transactions in an accepted EB have the same impact on the ledger state as transactions in an RB. [P, C, T]
3. Ensure that chain validity and selection are unchanged: EBs and votes are auxiliary data; only a certificate included in an RB affects the ledger, and nothing in Leios affects chain preference. [P, C]
4. Ensure that the protocol's security constraints hold for any deployed parameterisation: worst-case certified-EB transmission completes within $3L_\text{hdr} + L_\text{vote} + L_\text{diff} + (\Delta_\text{RB} - \Delta_\text{applyTxs})$, and applying a certified EB is cheaper than validating its transactions. [P, S, B]
5. Leios offers adversaries no amplification lever against Praos: a maximal protocol burst (withheld-then-released EBs, gigabyte scale) violates neither R1 nor R13, and the resource cost Leios imposes on an honest node is bounded relative to the attacker's cost. [S, B]

**Deliver and sustain high throughput**

6. Sustain the target throughput (140–300 TxkB/s per CIP-164) on mainnet-like topology and SPO-grade hardware under nominal conditions. [S, B]
7. Honest nodes include a certificate in each RB they issue whenever they have seen a quorum of votes for the EB announced by the preceding RB. [P, C, T]
8. Degrade gracefully: under honest load, throughput reaches the target maximum and remains there until the mempool empties; under adversarial participation, throughput degrades at most in proportion to adversarial stake (up to the loss of EB certification at adversarial committee stake above $1-\tau$) and never falls below the Praos baseline; it returns to maximum once the adversarial condition subsides. [S, B]
9. Bound the distribution of latency from mempool acceptance to ledger inclusion — stated percentiles, not only means — under nominal and congested load. [S, B, T]
10. The worst-case resource envelope — bandwidth, CPU, memory, disk I/O, and the rate of disk capacity growth — at the target parameterisation is quantified and sustainable on SPO-grade hardware. [B, S]

**Accept EBs only by distributed consensus**

11. A certificate verifies only if voters representing at least the quorum $\tau$ of committee stake voted for the EB; forging a certificate without such a quorum is computationally infeasible under the BLS and proof-of-possession assumptions. [P, S]
12. Honest nodes vote exactly according to the CIP-164 voting rules (timely header, no observed equivocation, EB announced by the tip of the current selection, closure fully validated in time). [P, C, T]
13. A certified EB's transaction closure is retrievable by honest nodes within $L_\text{diff}$ of certification at the 99th percentile or better, measured across honest nodes and certified EBs. [S, B]
14. Committee selection is stake-proportional and manipulation-resistant within quantified bounds (Fait Accompli persistent voters; sortition for non-persistent voters). [P, S]
15. Equivocation is contained: honest nodes never vote for an equivocated EB, consider at most two announcements per election, and disconnect peers exceeding that limit. [P, C, T]
16. Nodes acquire and serve every promptly-announced EB for the required window, independent of whether they voted for it or prefer its chain. [C, T]
17. All rules governing transaction history under Praos apply equally to transactions accepted via EBs: they are retained indefinitely as part of the chain, served to peers, and sufficient to reconstruct the complete ledger state when syncing from genesis. [T]

**Maintain compatible interfaces as far as possible**

18. Clients on node-to-client interfaces observe certified transactions inlined into blocks; changes visible to existing consumers (wallets, explorers, Mithril, db-sync) are minimal and documented. [T]
19. A network of mixed pre- and post-Leios node versions remains safe and live through the hard-fork transition. [T]
20. A heterogeneous network of conforming implementations interoperates: any node satisfying these requirements can peer with any other, with no reliance on behaviour of the reference implementation beyond what CIP-164 specifies. [C, T]
21. Implementations emit execution traces conforming to the implementation-independent trace semantics, sufficient for the conformance verification of the items above. [T]

## Notation

- Items are cited by number as "R1" … "R21"; the category headings group them but carry no significance beyond presentation.
- Proposed assurance routes are suggested for each item, and are preferred but not exclusive. **P** and **S** are protocol-level and discharge once for all implementations; **C**, **B** and **T** are per-implementation and must be produced for each implementation claiming to implement Leios.
    - **P** — proof obligation (Agda formal spec)
    - **S** — simulation or statistical analysis
    - **C** — conformance (trace verification of implementation logs)
    - **B** — benchmark or prototype measurement
    - **T** — test suite (property, integration, testnet)
- What must be demonstrated is adherence to these requirements. Conformance (**C**) is one pillar of that: it establishes that an implementation realises the formal specification, and so carries weight only in composition with the proofs (**P**) and statistical analyses (**S**) establishing that the specification itself satisfies the requirement.
- Every test set, proof obligation, model-checking result, or statistical analysis report produced by the project must cite the requirement identifier(s) it discharges (e.g. "R2"); every requirement must eventually be discharged by at least one such artefact.
- These requirements are implementation-neutral: they constrain the observable behaviour of a node implementation — at its network interfaces, in the on-chain artefacts it produces, and in its resource consumption.
- Requirements are stated relative to a protocol parameterisation ($L_\text{hdr}$, $L_\text{vote}$, $L_\text{diff}$, $\tau$, committee size $n$, size limits $S_\text{RB}$, $S_\text{EB}$, $S_\text{EB-tx}$); verification artefacts must state the parameter ranges over which they hold.
- "SPO-grade hardware" (R6, R10) means hardware meeting the SPO recommendations published for Cardano mainnet at the time of assessment, allowing at most a stated, bounded uplift; an uplift that would exclude currently viable SPOs fails this definition. Artefacts must state the exact specification they measured against.
