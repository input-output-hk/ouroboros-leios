---
sidebar_position: 3
---

# How It Works

Leios is a high-throughput overlay protocol designed to enhance blockchain
scalability, such as for Cardano’s Ouroboros, by managing a structured flow of
transactions. Here’s a breakdown of how it operates:

1. **Creating Input Blocks (IBs)**:<br /> Stake pool operators (SPOs), acting as
   validators, bundle transactions into Input Blocks (IBs) every 0.2–2 seconds
   and broadcast them across the network for parallel processing.

2. **Proofs of Data Availability**:<br /> Validators check that IBs’ transaction
   data is valid and accessible, a process later confirmed through Endorser
   Blocks (EBs) and voting, ensuring no data is missing or malformed.

3. **Generating Endorser Blocks (EBs)**:<br /> EBs aggregate multiple verified
   IBs, grouping them for validation and proposing their inclusion in the
   blockchain’s final ledger.

4. **Pipelined Processing**:<br /> The protocol uses a seven-stage endorsing
   pipeline (detailed below) to process IBs, EBs, and votes in parallel,
   maximizing network bandwidth and throughput.

5. **Voting and Certification**:<br /> Validators vote on EBs using
   stake-weighted BLS signatures to certify their correctness and data
   availability, ensuring only compliant IBs (e.g., valid scripts) proceed.

6. **Final Inclusion in the Blockchain**:<br /> Certified EBs are referenced by
   a certificate included in a Ranking Block (RB)—a Praos-style block minted
   every ~20 seconds—finalizing IB transactions on the blockchain while
   maintaining a verifiable, efficient record.

## Leios architecture

The Leios protocol utilizes a pipelined architecture to achieve high throughput.
A pipeline instance comprises seven stages:

1. **Propose**:<br />

   - Validators concurrently generate and propose IBs with transaction data,
     kicking off the pipeline instance and targeting frequent output (e.g.,
     every 0.2–2 seconds).
   - IBs proposed during this stage are the focus of the current pipeline
     instance.

2. **Deliver1**:<br />

   - Time is allocated for proposed IBs to spread across the network using a
     freshest-first diffusion strategy, ensuring honest nodes receive them
     within a set delay (e.g., Δ_hdr) despite potential adversarial bursts.
   - Duration is crucial for ensuring all honest nodes receive IBs before the
     next stage.

3. **Link**:<br />

   - Validators create EBs that reference Propose-stage IBs, grouping and
     ordering them for validation and eventual blockchain inclusion.
   - EBs serve as containers for grouping and ordering IBs.

4. **Deliver2**:<br />

   - Time is allocated for any adversarial IBs referenced by EBs to disseminate,
     ensuring honest nodes have all data needed for fair voting and availability
     checks.
   - Ensures honest nodes have received all relevant IBs before casting votes.

5. **Vote1**:<br />

   - Validators cast stake-weighted votes (via BLS signatures) for EBs from the
     Link stage, certifying them as Vote1-certified if enough votes confirm
     their IBs’ validity and availability.

6. **Endorse**:<br />

   - New EBs reference Vote1-certified EBs, linking across pipeline instances to
     reinforce IB confirmation and ensure high throughput by cross-referencing
     honest data.
   - Strengthens overall confirmation of IBs.

7. **Vote2**:<br />
   - Validators cast final votes for Endorse-stage EBs, certifying them as
     Vote2-certified if they reference a majority of Vote1-certified EBs,
     preparing them for RB inclusion and ledger finality.
   - Must reference a majority of Vote1-certified EBs.

## Network Resilience

Leios counters adversarial tactics with:

- **Freshest-First Diffusion**: Nodes prioritize downloading the newest IBs and
  EBs (via VRF-based timestamps), limiting delays from malicious message bursts.
- **Equivocation Proofs**: If a validator double-signs (e.g., sends conflicting
  EBs), honest nodes detect and propagate proofs, ensuring only one valid block
  per slot is processed, minimizing bandwidth waste.

## Integration with Ouroboros

- Leios enhances Ouroboros Praos by overlaying its Ranking Blocks (RBs) with
  high-throughput IB and EB processing. RBs, minted every ~20 seconds, anchor
  the ledger’s security, while Leios’ pipeline scales transaction capacity
  without altering Praos’ core settlement guarantees.

This pipelined architecture ensures continuous IB generation, parallel
processing, and robust confirmation, enabling Leios to achieve near-optimal
transaction throughput (e.g., (1-δ) of network capacity) while resisting
adversarial tactics like message bursts and equivocations.
