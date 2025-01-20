{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- Deterministic variant of simple Leios
--------------------------------------------------------------------------------

open import Leios.Prelude hiding (id)
open import Prelude.Init using (∃₂-syntax)
open import Leios.FFD

import Data.List as L
open import Data.List.Relation.Unary.Any using (here)

open import Leios.SpecStructure

module Leios.Simple.Deterministic (⋯ : SpecStructure 2) (let open SpecStructure ⋯) (Λ μ : ℕ) where

import Leios.Simplified
open import Leios.Simplified ⋯ Λ μ hiding (_-⟦_/_⟧⇀_)
module ND = Leios.Simplified ⋯ Λ μ

open import Class.Computational
open import Class.Computational22
open import StateMachine

open BaseAbstract B' using (Cert; V-chkCerts; VTy; initSlot)
open GenFFD

open FFD hiding (_-⟦_/_⟧⇀_)

private variable s s' s0 s1 s2 s3 s4 s5 : LeiosState
                 i      : LeiosInput
                 o      : LeiosOutput
                 ffds'  : FFD.State
                 π      : VrfPf
                 bs'    : B.State
                 ks ks' : K.State
                 msgs   : List (FFDAbstract.Header ffdAbstract ⊎ FFDAbstract.Body ffdAbstract)
                 eb     : EndorserBlock
                 rbs    : List RankingBlock
                 txs    : List Tx
                 V      : VTy
                 SD     : StakeDistr
                 pks    : List PubKey

lemma : ∀ {u} → u ∈ LeiosState.Upkeep (addUpkeep s u)
lemma = to ∈-∪ (inj₂ (to ∈-singleton refl))
  where open Equivalence

addUpkeep⇒¬needsUpkeep : ∀ {u} → ¬ LeiosState.needsUpkeep (addUpkeep s u) u
addUpkeep⇒¬needsUpkeep {s = s} = λ x → x (lemma {s = s})

data _⊢_ : LeiosInput → LeiosState → Type where
  Init :
       ∙ ks K.-⟦ K.INIT pk-IB pk-EB pk-V / K.PUBKEYS pks ⟧⇀ ks'
       ∙ initBaseState B.-⟦ B.INIT (V-chkCerts pks) / B.STAKE SD ⟧⇀ bs'
       ────────────────────────────────────────────────────────────────
       INIT V ⊢ initLeiosState V SD bs'

data _-⟦Base⟧⇀_ : LeiosState → LeiosState → Type where

  Base₂a  : ∀ {ebs} → let open LeiosState s renaming (BaseState to bs) in
          ∙ needsUpkeep Base
          ∙ eb ∷ ebs ≡ filter (λ eb → isVote2Certified s eb × eb ∈ᴮ slice L slot 2) EBs
          ∙ bs B.-⟦ B.SUBMIT (this eb) / B.EMPTY ⟧⇀ bs'
          ───────────────────────────────────────────────────────────────────────
          s -⟦Base⟧⇀ addUpkeep record s { BaseState = bs' } Base

  Base₂b  : let open LeiosState s renaming (BaseState to bs) in
          ∙ needsUpkeep Base
          ∙ [] ≡ filter (λ eb → isVote2Certified s eb × eb ∈ᴮ slice L slot 2) EBs
          ∙ bs B.-⟦ B.SUBMIT (that ToPropose) / B.EMPTY ⟧⇀ bs'
          ───────────────────────────────────────────────────────────────────────
          s -⟦Base⟧⇀ addUpkeep record s { BaseState = bs' } Base

Base⇒ND : s -⟦Base⟧⇀ s' → just s ND.-⟦ SLOT / EMPTY ⟧⇀ s'
Base⇒ND (Base₂a x x₁ x₂) = Base₂a x (subst (_ ∈_) x₁ (Equivalence.to ∈-fromList (here refl))) x₂
Base⇒ND (Base₂b x x₁ x₂) = Base₂b x x₁ x₂

opaque
  Base-total : LeiosState.needsUpkeep s Base → ∃[ s' ] s -⟦Base⟧⇀ s'
  Base-total {s = s} needsUpkeep with
    (let open LeiosState s in filter (λ eb → isVote2Certified s eb × eb ∈ᴮ slice L slot 2) EBs)
    in eq
  ... | []    = -, Base₂b needsUpkeep (sym eq) (proj₂ B.SUBMIT-total)
  ... | x ∷ l = -, Base₂a needsUpkeep (sym eq) (proj₂ B.SUBMIT-total)

Base-Upkeep : s -⟦Base⟧⇀ s' → LeiosState.needsUpkeep s Base × ¬ LeiosState.needsUpkeep s' Base
Base-Upkeep {s = s} (Base₂a x x₁ x₂) = x , (addUpkeep⇒¬needsUpkeep {s = s})
Base-Upkeep {s = s} (Base₂b x x₁ x₂) = x , (addUpkeep⇒¬needsUpkeep {s = s})

data _-⟦IB-Role⟧⇀_ : LeiosState → LeiosState → Type where

  IB-Role : let open LeiosState s renaming (FFDState to ffds)
                b = ibBody (record { txs = ToPropose })
                h = ibHeader (mkIBHeader slot id π sk-IB ToPropose)
          in
          ∙ needsUpkeep IB-Role
          ∙ canProduceIB slot sk-IB (stake s) π
          ∙ ffds FFD.-⟦ Send h (just b) / SendRes ⟧⇀ ffds'
          ────────────────────────────────────────────────────────────────────
          s -⟦IB-Role⟧⇀ addUpkeep record s { FFDState = ffds' } IB-Role

  No-IB-Role : let open LeiosState s in
          ∙ needsUpkeep IB-Role
          ∙ (∀ π → ¬ canProduceIB slot sk-IB (stake s) π)
          ────────────────────────────────────────
          s -⟦IB-Role⟧⇀ addUpkeep s IB-Role

IB-Role⇒ND : s -⟦IB-Role⟧⇀ s' → just s ND.-⟦ SLOT / EMPTY ⟧⇀ s'
IB-Role⇒ND (IB-Role x x₁ x₂) = Roles (IB-Role x x₁ x₂)
IB-Role⇒ND (No-IB-Role x x₁) = Roles (No-IB-Role x x₁)

opaque
  IB-Role-total : LeiosState.needsUpkeep s IB-Role → ∃[ s' ] s -⟦IB-Role⟧⇀ s'
  IB-Role-total {s = s} h = let open LeiosState s in case Dec-canProduceIB of λ where
    (inj₁ (π , pf)) → -, IB-Role    h pf (proj₂ FFD.FFD-total)
    (inj₂ pf)       → -, No-IB-Role h pf

IB-Role-Upkeep : s -⟦IB-Role⟧⇀ s' → LeiosState.needsUpkeep s IB-Role × ¬ LeiosState.needsUpkeep s' IB-Role
IB-Role-Upkeep {s = s} (IB-Role x x₁ x₂) = x , (addUpkeep⇒¬needsUpkeep {s = s})
IB-Role-Upkeep {s = s} (No-IB-Role x x₁) = x , (addUpkeep⇒¬needsUpkeep {s = s})

data _-⟦EB-Role⟧⇀_ : LeiosState → LeiosState → Type where

  EB-Role : let open LeiosState s renaming (FFDState to ffds)
                LI = map getIBRef $ filter (_∈ᴮ slice L slot (Λ + 1)) IBs
                LE = map getEBRef $ filter (isVote1Certified s) $
                           filter (_∈ᴮ slice L slot (μ + 2)) EBs
                h = mkEB slot id π sk-EB LI LE
          in
          ∙ needsUpkeep EB-Role
          ∙ canProduceEB slot sk-EB (stake s) π
          ∙ ffds FFD.-⟦ Send (ebHeader h) nothing / SendRes ⟧⇀ ffds'
          ────────────────────────────────────────────────────────────────────
          s -⟦EB-Role⟧⇀ addUpkeep record s { FFDState = ffds' } EB-Role

  No-EB-Role : let open LeiosState s in
          ∙ needsUpkeep EB-Role
          ∙ (∀ π → ¬ canProduceEB slot sk-EB (stake s) π)
          ────────────────────────────────────────
          s -⟦EB-Role⟧⇀ addUpkeep s EB-Role

EB-Role⇒ND : s -⟦EB-Role⟧⇀ s' → just s ND.-⟦ SLOT / EMPTY ⟧⇀ s'
EB-Role⇒ND (EB-Role x x₁ x₂) = Roles (EB-Role x x₁ x₂)
EB-Role⇒ND (No-EB-Role x x₁) = Roles (No-EB-Role x x₁)

opaque
  EB-Role-total : LeiosState.needsUpkeep s EB-Role → ∃[ s' ] s -⟦EB-Role⟧⇀ s'
  EB-Role-total {s = s} h = let open LeiosState s in case Dec-canProduceEB of λ where
    (inj₁ (π , pf)) → -, EB-Role    h pf (proj₂ FFD.FFD-total)
    (inj₂ pf)       → -, No-EB-Role h pf

EB-Role-Upkeep : s -⟦EB-Role⟧⇀ s' → LeiosState.needsUpkeep s EB-Role × ¬ LeiosState.needsUpkeep s' EB-Role
EB-Role-Upkeep {s = s} (EB-Role x x₁ x₂) = x , (addUpkeep⇒¬needsUpkeep {s = s})
EB-Role-Upkeep {s = s} (No-EB-Role x x₁) = x , (addUpkeep⇒¬needsUpkeep {s = s})

data _-⟦V1-Role⟧⇀_ : LeiosState → LeiosState → Type where

  V1-Role : let open LeiosState s renaming (FFDState to ffds)
                EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot (μ + 1)) EBs
                votes = map (vote sk-V ∘ hash) EBs'
          in
          ∙ needsUpkeep V1-Role
          ∙ canProduceV1 slot sk-V (stake s)
          ∙ ffds FFD.-⟦ Send (vHeader votes) nothing / SendRes ⟧⇀ ffds'
          ────────────────────────────────────────────────────────────────────
          s -⟦V1-Role⟧⇀ addUpkeep record s { FFDState = ffds' } V1-Role

  No-V1-Role : let open LeiosState s in
          ∙ needsUpkeep V1-Role
          ∙ ¬ canProduceV1 slot sk-V (stake s)
          ────────────────────────────────────────
          s -⟦V1-Role⟧⇀ addUpkeep s V1-Role

V1-Role⇒ND : s -⟦V1-Role⟧⇀ s' → just s ND.-⟦ SLOT / EMPTY ⟧⇀ s'
V1-Role⇒ND (V1-Role x x₁ x₂) = Roles (V1-Role x x₁ x₂)
V1-Role⇒ND (No-V1-Role x x₁) = Roles (No-V1-Role x x₁)

opaque
  V1-Role-total : LeiosState.needsUpkeep s V1-Role → ∃[ s' ] s -⟦V1-Role⟧⇀ s'
  V1-Role-total {s = s} h = let open LeiosState s in case Dec-canProduceV1 of λ where
    (yes p) → -, V1-Role h p (proj₂ FFD.FFD-total)
    (no ¬p) → -, No-V1-Role h ¬p

V1-Role-Upkeep : s -⟦V1-Role⟧⇀ s' → LeiosState.needsUpkeep s V1-Role × ¬ LeiosState.needsUpkeep s' V1-Role
V1-Role-Upkeep {s = s} (V1-Role x x₁ x₂) = x , (addUpkeep⇒¬needsUpkeep {s = s})
V1-Role-Upkeep {s = s} (No-V1-Role x x₁) = x , (addUpkeep⇒¬needsUpkeep {s = s})

data _-⟦V2-Role⟧⇀_ : LeiosState → LeiosState → Type where

  V2-Role : let open LeiosState s renaming (FFDState to ffds)
                EBs' = filter (vote2Eligible s) $ filter (_∈ᴮ slice L slot 1) EBs
                votes = map (vote sk-V ∘ hash) EBs'
          in
          ∙ needsUpkeep V2-Role
          ∙ canProduceV2 slot sk-V (stake s)
          ∙ ffds FFD.-⟦ Send (vHeader votes) nothing / SendRes ⟧⇀ ffds'
          ────────────────────────────────────────────────────────────────────
          s -⟦V2-Role⟧⇀ addUpkeep record s { FFDState = ffds' } V2-Role

  No-V2-Role : let open LeiosState s in
          ∙ needsUpkeep V2-Role
          ∙ ¬ canProduceV2 slot sk-V (stake s)
          ────────────────────────────────────────
          s -⟦V2-Role⟧⇀ addUpkeep s V2-Role

V2-Role⇒ND : s -⟦V2-Role⟧⇀ s' → just s ND.-⟦ SLOT / EMPTY ⟧⇀ s'
V2-Role⇒ND (V2-Role x x₁ x₂) = Roles (V2-Role x x₁ x₂)
V2-Role⇒ND (No-V2-Role x x₁) = Roles (No-V2-Role x x₁)

opaque
  V2-Role-total : LeiosState.needsUpkeep s V2-Role → ∃[ s' ] s -⟦V2-Role⟧⇀ s'
  V2-Role-total {s = s} h = let open LeiosState s in case Dec-canProduceV2 of λ where
    (yes p) → -, V2-Role h p (proj₂ FFD.FFD-total)
    (no ¬p) → -, No-V2-Role h ¬p

V2-Role-Upkeep : s -⟦V2-Role⟧⇀ s' → LeiosState.needsUpkeep s V2-Role × ¬ LeiosState.needsUpkeep s' V2-Role
V2-Role-Upkeep {s = s} (V2-Role x x₁ x₂) = x , (addUpkeep⇒¬needsUpkeep {s = s})
V2-Role-Upkeep {s = s} (No-V2-Role x x₁) = x , (addUpkeep⇒¬needsUpkeep {s = s})

↑-Upkeep : ∀ {x} → LeiosState.Upkeep s ≡ LeiosState.Upkeep (s ↑ x)
↑-Upkeep = {!!}

data _-⟦_/_⟧⇀_ : LeiosState → LeiosInput → LeiosOutput → LeiosState → Type where

  -- Network and Ledger

  Slot : let open LeiosState s renaming (FFDState to ffds; BaseState to bs)
             s0 = record s
                    { FFDState = ffds'
                    ; Ledger   = constructLedger rbs
                    ; slot     = suc slot
                    ; Upkeep   = ∅
                    ; BaseState = bs'
                    } ↑ L.filter isValid? msgs
       in
       ∙ Upkeep ≡ᵉ allUpkeep
       ∙ bs B.-⟦ B.FTCH-LDG / B.BASE-LDG rbs ⟧⇀ bs'
       ∙ ffds FFD.-⟦ Fetch / FetchRes msgs ⟧⇀ ffds'
       ∙ s0 -⟦Base⟧⇀    s1
       ∙ s1 -⟦IB-Role⟧⇀ s2
       ∙ s2 -⟦EB-Role⟧⇀ s3
       ∙ s3 -⟦V1-Role⟧⇀ s4
       ∙ s4 -⟦V2-Role⟧⇀ s5
       ───────────────────────────────────────────────────────────────────────
       s -⟦ SLOT / EMPTY ⟧⇀ s5

  Ftch :
       ───────────────────────────────────────────────────
       s -⟦ FTCH-LDG / FTCH-LDG (LeiosState.Ledger s) ⟧⇀ s

  -- Base chain
  --
  -- Note: Submitted data to the base chain is only taken into account
  --       if the party submitting is the block producer on the base chain
  --       for the given slot

  Base₁   :
          ──────────────────────────────────────────────────────────────
          s -⟦ SUBMIT (inj₂ txs) / EMPTY ⟧⇀ record s { ToPropose = txs }

  -- Protocol rules

_-⟦_/_⟧ⁿᵈ⇀_ : LeiosState → LeiosInput → LeiosOutput → LeiosState → Type
s -⟦ i / o ⟧ⁿᵈ⇀ s' = just s ND.-⟦ i / o ⟧⇀ s'

_-⟦_/_⟧ⁿᵈ*⇀_ : LeiosState → List LeiosInput → List LeiosOutput → LeiosState → Type
_-⟦_/_⟧ⁿᵈ*⇀_ = ReflexiveTransitiveClosure _-⟦_/_⟧ⁿᵈ⇀_

-- Key fact: stepping with the deterministic relation means we can
-- also step with the non-deterministic one
-- TODO: this is a lot like a weak simulation, can we do something prettier?
-⟦/⟧⇀⇒ND : s -⟦ i / o ⟧⇀ s' → ∃₂[ i , o ] (s -⟦ i / o ⟧ⁿᵈ*⇀ s')
-⟦/⟧⇀⇒ND (Slot x x₁ x₂ hB hIB hEB hV1 hV2) = replicate 6 SLOT , replicate 6 EMPTY ,
  (BS-ind (ND.Slot x x₁ x₂) $
   BS-ind (Base⇒ND hB) $
   BS-ind (IB-Role⇒ND hIB) $
   BS-ind (EB-Role⇒ND hEB) $
   BS-ind (V1-Role⇒ND hV1) $
   STS⇒RTC (V2-Role⇒ND hV2))
-⟦/⟧⇀⇒ND Ftch = _ , _ , STS⇒RTC Ftch
-⟦/⟧⇀⇒ND Base₁ = _ , _ , STS⇒RTC Base₁

open Computational22 ⦃...⦄

module _ ⦃ Computational-B : Computational22 B._-⟦_/_⟧⇀_ String ⦄
         ⦃ Computational-FFD : Computational22 FFD._-⟦_/_⟧⇀_ String ⦄ where
  instance
    Computational--⟦/⟧⇀ : Computational22 _-⟦_/_⟧⇀_ String
    Computational--⟦/⟧⇀ .computeProof s (INIT x) = failure "No handling of INIT here"
    Computational--⟦/⟧⇀ .computeProof s (SUBMIT (inj₁ eb)) = failure "Cannot submit EB here"
    Computational--⟦/⟧⇀ .computeProof s (SUBMIT (inj₂ txs)) = success (-, Base₁)
    Computational--⟦/⟧⇀ .computeProof s SLOT = let open LeiosState s in
      case (¿ Upkeep ≡ᵉ allUpkeep ¿ ,′ computeProof BaseState B.FTCH-LDG ,′ computeProof FFDState FFD.Fetch) of λ where
        (yes p , success ((B.BASE-LDG l , bs) , p₁) , success ((FFD.FetchRes msgs , ffds) , p₂)) →
          success (let
            open ≡-Reasoning
            s = _ -- solved later by unification
            s0 = s ↑ L.filter isValid? msgs
            upkeep≡∅ : LeiosState.Upkeep s0 ≡ ∅
            upkeep≡∅ = sym (↑-Upkeep {s = s} {x = L.filter isValid? msgs})
            in (_ , Slot p p₁ p₂
                            (proj₂ (Base-total {s = s0} (subst (Base ∉_) (sym upkeep≡∅) Properties.∉-∅)))
                            (proj₂ (IB-Role-total {!!}))
                            (proj₂ (EB-Role-total {!!}))
                            (proj₂ (V1-Role-total {!!}))
                            (proj₂ (V2-Role-total {!!}))))
        (yes p , _ , _) → failure "Subsystem failed"
        (no ¬p , _) → failure "Upkeep incorrect"
    Computational--⟦/⟧⇀ .computeProof s FTCH-LDG = success (-, Ftch)
    Computational--⟦/⟧⇀ .completeness = {!!}
