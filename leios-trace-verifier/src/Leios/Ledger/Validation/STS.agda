{-# OPTIONS --safe #-}

{- Module: Leios.Ledger.Validation.STS

   The validation functionality backed by a ledger transition system
   'Γ ⊢ s ⇀⦇ b ⦈ s′' whose applicability is decidable: a submission is the
   environment, the ledger state and the signal, and a completed validation
   accepts it exactly when the system has a transition on it.  The agreement
   lemmas say that the machine's 'Valid' and 'Invalid' answers are those of
   the transition system, and that past the bound it gives one of the two.

   'Leios.Ledger.Validation.Dijkstra' instantiates this with the Dijkstra
   era's 'EB' rule, deciding it with that rule's 'Computational' instance.
-}

open import Leios.Prelude hiding (_⊗_; _∨_)
open import Data.Bool using (_∨_; if_then_else_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Maybe.Properties using (just-injective)

open import CategoricalCrypto hiding (id; _∘_)

open import Leios.Ledger.Validation

module Leios.Ledger.Validation.STS
  {Env St Sig : Type}
  (STS    : Env → St → Sig → St → Type)
  (decide : ∀ Γ s b → Dec (∃[ s′ ] STS Γ s b s′))
  where

record Submission : Type where
  constructor submission
  field env    : Env
        state  : St
        signal : Sig

open Submission public

-- The transition system accepts the submission.
Accepts : Submission → Type
Accepts x = ∃[ s′ ] STS (env x) (state x) (signal x) s′

verdictOf : Submission → Verdict
verdictOf x with decide (env x) (state x) (signal x)
... | yes _ = accept
... | no  _ = reject

stsBackend : Backend Submission
stsBackend = record { verdict = verdictOf }

verdict-accept : ∀ x → verdictOf x ≡ accept → Accepts x
verdict-accept x eq with decide (env x) (state x) (signal x)
... | yes p = p
... | no  _ = case eq of λ ()

verdict-reject : ∀ x → verdictOf x ≡ reject → ¬ Accepts x
verdict-reject x eq with decide (env x) (state x) (signal x)
... | yes _ = case eq of λ ()
... | no ¬p = ¬p

accept-verdict : ∀ x → Accepts x → verdictOf x ≡ accept
accept-verdict x p with decide (env x) (state x) (signal x)
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p p)

reject-verdict : ∀ x → ¬ Accepts x → verdictOf x ≡ reject
reject-verdict x ¬p with decide (env x) (state x) (signal x)
... | yes p = ⊥-elim (¬p p)
... | no  _ = refl

module Instance (Ref : Type) ⦃ _ : DecEq Ref ⦄ (ref : Submission → Ref) (Δ : ℕ) where

  open Functionality Submission Ref ref stsBackend Δ public

  -- The submission recorded under a reference.
  submissionOf : ValState → Ref → Maybe Submission
  submissionOf s h = Submitted.eb <$> lookupᵛ h (ValState.subs s)

  private
    statusAt-Valid : ∀ c me → statusAt c me ≡ Valid
                   → ∃[ x ] (Submitted.eb <$> me) ≡ just x × Accepts x
    statusAt-Valid c (just e) eq with completed c e
    ... | false = case eq of λ ()
    ... | true with verdictOf (Submitted.eb e) in v
    ...   | accept = _ , refl , verdict-accept _ v
    ...   | reject = case eq of λ ()

    statusAt-Invalid : ∀ c me → statusAt c me ≡ Invalid
                     → ∃[ x ] (Submitted.eb <$> me) ≡ just x × ¬ Accepts x
    statusAt-Invalid c (just e) eq with completed c e
    ... | false = case eq of λ ()
    ... | true with verdictOf (Submitted.eb e) in v
    ...   | accept = case eq of λ ()
    ...   | reject = _ , refl , verdict-reject _ v

  -- A 'Valid' answer is a transition of the system on the submission.
  Valid-agrees : ∀ s h → status s h ≡ Valid
               → ∃[ x ] submissionOf s h ≡ just x × Accepts x
  Valid-agrees s h = statusAt-Valid (ValState.clock s) (lookupᵛ h (ValState.subs s))

  -- An 'Invalid' answer is a submission the system has no transition on.
  Invalid-agrees : ∀ s h → status s h ≡ Invalid
                 → ∃[ x ] submissionOf s h ≡ just x × ¬ Accepts x
  Invalid-agrees s h = statusAt-Invalid (ValState.clock s) (lookupᵛ h (ValState.subs s))

  -- Past the bound the answer is the system's: 'Valid' if it accepts the
  -- submission, else 'Invalid'.
  decided : ∀ s h {m} → submittedAt s h ≡ just m → m + Δ N.≤ ValState.clock s
          → ∀ {x} → submissionOf s h ≡ just x
          → (Accepts x → status s h ≡ Valid) × (¬ Accepts x → status s h ≡ Invalid)
  decided s h eq le sx with lookupᵛ h (ValState.subs s)
  ... | just e with refl ← just-injective eq | refl ← just-injective sx
    rewrite T⇒≡ (N.≤⇒≤ᵇ le) | ∨-zeroʳ (Submitted.done e) =
      (λ p → cong toResult (accept-verdict _ p)) , (λ ¬p → cong toResult (reject-verdict _ ¬p))

  -- The same, of the machine's query steps.
  query-Valid : ∀ {s s′ o h} → s -⟦ L⊗ (ϵ ᵗ¹) ↑ₒ QUERY h / o ⟧ᵛ⇀ s′ → answerOf o ≡ just Valid
              → ∃[ x ] submissionOf s h ≡ just x × Accepts x
  query-Valid {s} {h = h} d ans = Valid-agrees s h (just-injective (trans (sym (query-answer d)) ans))
