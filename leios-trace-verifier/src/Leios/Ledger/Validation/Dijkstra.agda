{-# OPTIONS --safe #-}

{- Module: Leios.Ledger.Validation.Dijkstra

   The validation functionality backed by the Dijkstra era of the formal
   ledger specification: a submission is the ledger environment with the
   EB's resolved transactions, the ledger state the EB extends, and the
   Dijkstra 'EndorserBlock', and a completed validation accepts it exactly
   when the 'EB' rule ('Ledger.Dijkstra.Specification.Leios.Validity') has a
   transition on it:

     (Γ , txs) ⊢ ls ⇀⦇ eb ,EB⦈ ls′

   which checks that the EB is well formed, that its references are those
   of 'txs', its size limits, and 'LEDGERS' on 'txs'.  The rule is decided
   by its 'Computational' instance, and EBs are referenced by 'hashEB'.

   'EB-Valid' and 'EB-Invalid' are the agreement of the machine's answers
   with the rule, and 'EB-decided' says that past the bound it answers by
   the rule.

   Not used by the trace verifier: traces carry transaction ids and sizes,
   never the transaction bodies 'LEDGERS' needs.  It needs the
   formal-ledger library (see the Makefile's 'ledger-validation' target).
-}

open import Ledger.Dijkstra.Specification.Transaction using (TransactionStructure)
open import Ledger.Dijkstra.Specification.Abstract using (AbstractFunctions)

open import Leios.Prelude hiding (_⊗_; map)

module Leios.Ledger.Validation.Dijkstra
  (txs : TransactionStructure) (open TransactionStructure txs using (cryptoStructure; leiosCryptoStructure))
  (abs : AbstractFunctions txs)
  -- How long validation may stay in progress after submission.
  (Δ : ℕ)
  where

open import Interface.ComputationalRelation using (Computational; success; failure; map-failure)
open import Ledger.Dijkstra.Specification.Crypto using (LeiosCryptoStructure)
open import Ledger.Dijkstra.Specification.Leios.Types cryptoStructure leiosCryptoStructure
  using (EndorserBlock; hashEB)
open import Ledger.Dijkstra.Specification.Leios.Validity txs abs using (_⊢_⇀⦇_,EB⦈_)
open import Ledger.Dijkstra.Specification.Leios.Validity.Properties.Computational txs abs
  using (Computational-EB)
open LeiosCryptoStructure leiosCryptoStructure using (EBHash; DecEq-EBHash)

open import Leios.Ledger.Validation

private
  module C = Computational Computational-EB

-- The 'EB' rule, decided by its computational instance.
decideEB : ∀ Γ ls eb → Dec (∃[ ls′ ] Γ ⊢ ls ⇀⦇ eb ,EB⦈ ls′)
decideEB Γ ls eb with C.computeProof Γ ls eb in eq
... | success p = yes p
... | failure e = no λ (ls′ , p) → C.failure⇒∀¬STS (e , map-failure eq) ls′ p

open import Leios.Ledger.Validation.STS _⊢_⇀⦇_,EB⦈_ decideEB public
  using (Submission; submission; env; state; signal; Accepts; stsBackend)

open import Leios.Ledger.Validation.STS _⊢_⇀⦇_,EB⦈_ decideEB as V using ()

-- EBs are referenced by their Dijkstra hash.
refEB : Submission → EBHash
refEB x = hashEB (signal x)

open V.Instance EBHash refEB Δ public

-- A 'Valid' answer is an 'EB' transition on the submission.
EB-Valid : ∀ s h → status s h ≡ Valid
         → ∃[ x ] submissionOf s h ≡ just x × ∃[ ls′ ] env x ⊢ state x ⇀⦇ signal x ,EB⦈ ls′
EB-Valid = Valid-agrees

-- An 'Invalid' answer is a submission the 'EB' rule rejects.
EB-Invalid : ∀ s h → status s h ≡ Invalid
           → ∃[ x ] submissionOf s h ≡ just x × ¬ (∃[ ls′ ] env x ⊢ state x ⇀⦇ signal x ,EB⦈ ls′)
EB-Invalid = Invalid-agrees

-- At least 'Δ' slots after submission the answer is the rule's.
EB-decided : ∀ s h {m} → submittedAt s h ≡ just m → m + Δ N.≤ ValState.clock s
           → ∀ {x} → submissionOf s h ≡ just x
           → ((∃[ ls′ ] env x ⊢ state x ⇀⦇ signal x ,EB⦈ ls′) → status s h ≡ Valid)
           × (¬ (∃[ ls′ ] env x ⊢ state x ⇀⦇ signal x ,EB⦈ ls′) → status s h ≡ Invalid)
EB-decided = decided
