{- Module: LinearLeiosTrace

   Runs the spec's generic trace verifier over a trace read off a log, where
   one step per slot cannot be named until the verifier has reached it.

   The ranking-block step of a slot is either 'Base₁' (the tip calls for no
   certificate) or 'Base₂' followed by a certificate answer (it does).  Which
   one applies is 'certRequest' of the state at that point, which depends on
   the EBs the verifier has ingested and on the chain it was given; the
   converters do not track either.  The premises of the two are disjoint, so
   naming the step from the state rejects nothing that a correct choice by the
   converter would have accepted.

   The log does not say whether the certifier had a certificate, so the
   answer is 'CERT nothing'.  'Cert₁' admits it for any pending query, and the
   resulting RB is an output, which the verifier does not check.
-}

open import Leios.Prelude hiding (id)
open import Leios.Config
open import Leios.SpecStructure using (SpecStructure)

open import Prelude.Errors

module LinearLeiosTrace (⋯ : SpecStructure) (let open SpecStructure ⋯) (params : Params) where

open import Leios.Linear.Trace.Verifier ⋯ params
open Types params

-- An entry of the trace, or the ranking-block step of the given slot.
data Item : Type where
  entry : Action → TestInput → Item
  base  : ℕ → Item

baseEntries : LeiosState → ℕ → Trace
baseEntries s n = case certRequest s of λ where
  nothing  → ⟨ Base₁-Action n , inj₁ FFDT.SLOT ⟩ ∷ []
  (just _) → ⟨ Base₂-Action n , inj₁ FFDT.SLOT ⟩
           ∷ ⟨ Cert₁-Action n , inj₂ (inj₂ (inj₂ (CERT nothing))) ⟩
           ∷ []

-- Verify the items from the given state, returning the final state or the
-- message of the first error.
verifyItems : ⦃ Show Hash ⦄ → LeiosState → List Item → String ⊎ LeiosState
verifyItems s = go s []
  where
    flush : LeiosState → Trace → String ⊎ LeiosState
    flush s es = case verifyTrace s es of λ where
      (inj₁ err)      → inj₁ (errorMsg err)
      (inj₂ (s′ , _)) → inj₂ s′

    -- The entries not yet verified are kept in reverse.
    go : LeiosState → Trace → List Item → String ⊎ LeiosState
    go s pending []                  = flush s (L.reverse pending)
    go s pending (entry a i ∷ items) = go s (⟨ a , i ⟩ ∷ pending) items
    go s pending (base n ∷ items)    = case flush s (L.reverse pending) of λ where
      (inj₁ err) → inj₁ err
      (inj₂ s′)  → go s′ (L.reverse (baseEntries s′ n)) items
