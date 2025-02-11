---
sidebar_position: 3
---

# How it works

Leios' unique design manages a structured flow of transactions. Here's a
breakdown of how it works:

1. **Creating input blocks (IBs)**:<br />
   Validators bundle transactions into IBs and broadcast them across the network.

2. **Proofs of data availability**:<br />
   Validators verify that the IBs contain valid and accessible data.

3. **Generating endorser blocks (EBs)**:<br />
   EBs aggregate several verified IBs and propose them for inclusion in the
   blockchain.

4. **Pipelined processing**:<br />
   The protocol follows a seven-stage endorsing pipeline (described below).

5. **Voting and certification**:<br />
   Validators ensure that IBs contain valid and accessible data by checking
   their correctness
   This process is primarily handled by the endorser block producer
   Includes verifying that all available IBs adhere to network rules and
   ensuring transactions are script compliant if required.

6. **Final inclusion in the blockchain**:<br />
   A certificate (generated from the voting process and referencing the EB) is
   stored in the blockchain.
   This certificate is included in the Praos block (ranking block)
   Ensures blockchain efficiency while maintaining a verifiable record of
   endorsed transactions.

## Leios architecture

The Leios protocol utilizes a pipelined architecture to achieve high throughput.
A pipeline instance comprises seven stages:

1. **Propose**:
   - Validators generate and propose IBs containing transaction data
   - IBs proposed during this stage are the focus of the current pipeline
     instance.

2. **Deliver1**:
   - Allocates time for proposed IBs to be disseminated throughout the network
   - Duration is crucial for ensuring all honest nodes receive IBs before the
     next stage.

3. **Link**:
   - Validators create EBs that reference the IBs generated in the 'Propose'
     stage
   - EBs serve as containers for grouping and ordering IBs.

4. **Deliver2**:
   - Allows time for dissemination of any adversarial IBs referenced by EBs in
     the 'Link' stage
   - Ensures honest nodes have received all relevant IBs before casting votes.

5. **Vote1**:
   - Validators cast votes for EBs from the 'Link' stage
   - Specifically for EBs whose referenced IBs have been successfully delivered
   - An EB becomes Vote1-certified if it receives enough votes.

6. **Endorse**:
   - Vote1-certified EBs are referenced by new EBs created during this stage
   - Links EBs across different pipeline instances
   - Strengthens overall confirmation of IBs.

7. **Vote2**:
   - Validators cast final votes for EBs from the 'Endorse' stage
   - An EB becomes Vote2-certified if it meets specific criteria
   - Must reference a majority of Vote1-certified EBs.
  
  This pipelined architecture ensures the continuous generation, parallel processing,  dissemination, and confirmation of IBs, enabling Leios to achieve a high transaction throughput.
