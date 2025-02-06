-- {-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}

--------------------------------------------------------------------------------
-- Deterministic variant of short Leios
--------------------------------------------------------------------------------

open import Leios.Prelude hiding (id)
open import Prelude.Init using (∃₂-syntax)
open import Leios.FFD

import Data.List as L
open import Data.List.Relation.Unary.Any using (here)

open import Leios.SpecStructure

module Leios.Short.Deterministic (⋯ : SpecStructure 1) (let open SpecStructure ⋯) where

import Leios.Short
open import Leios.Short ⋯ hiding (_-⟦_/_⟧⇀_)
module ND = Leios.Short ⋯ 

open import Class.Computational
open import Class.Computational22
open import StateMachine

open BaseAbstract B' using (Cert; V-chkCerts; VTy; initSlot)
open GenFFD

open FFD hiding (_-⟦_/_⟧⇀_)

private variable s s' s0 s1 s2 s3 s4 : LeiosState
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
          ∙ eb ∷ ebs ≡ filter (λ eb → ND.isVoteCertified s eb × eb ∈ᴮ slice L slot 2) EBs
          ∙ bs B.-⟦ B.SUBMIT (this eb) / B.EMPTY ⟧⇀ bs'
          ───────────────────────────────────────────────────────────────────────
          s -⟦Base⟧⇀ addUpkeep record s { BaseState = bs' } Base

  Base₂b  : let open LeiosState s renaming (BaseState to bs) in
          ∙ needsUpkeep Base
          ∙ [] ≡ filter (λ eb → ND.isVoteCertified s eb × eb ∈ᴮ slice L slot 2) EBs
          ∙ bs B.-⟦ B.SUBMIT (that ToPropose) / B.EMPTY ⟧⇀ bs'
          ───────────────────────────────────────────────────────────────────────
          s -⟦Base⟧⇀ addUpkeep record s { BaseState = bs' } Base

Base⇒ND : s -⟦Base⟧⇀ s' → just s ND.-⟦ SLOT / EMPTY ⟧⇀ s'
Base⇒ND (Base₂a x x₁ x₂) = Base₂a x (subst (_ ∈_) x₁ (Equivalence.to ∈-fromList (here refl))) x₂
Base⇒ND (Base₂b x x₁ x₂) = Base₂b x x₁ x₂

opaque
  Base-total : LeiosState.needsUpkeep s Base → ∃[ s' ] s -⟦Base⟧⇀ s'
  Base-total {s = s} needsUpkeep with
    (let open LeiosState s in filter (λ eb → ND.isVoteCertified s eb × eb ∈ᴮ slice L slot 2) EBs)
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
                LI = map getIBRef $ filter (_∈ᴮ slice L slot 3) IBs
                h = mkEB slot id π sk-EB LI []
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

data _-⟦V-Role⟧⇀_ : LeiosState → LeiosState → Type where

  V-Role : let open LeiosState s renaming (FFDState to ffds)
               EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot 1) EBs
               votes = map (vote sk-V ∘ hash) EBs'
          in
          ∙ needsUpkeep V-Role
          ∙ canProduceV slot sk-V (stake s)
          ∙ ffds FFD.-⟦ Send (vHeader votes) nothing / SendRes ⟧⇀ ffds'
          ────────────────────────────────────────────────────────────────────
          s -⟦V-Role⟧⇀ addUpkeep record s { FFDState = ffds' } V-Role

  No-V-Role : let open LeiosState s in
          ∙ needsUpkeep V-Role
          ∙ ¬ canProduceV slot sk-V (stake s)
          ────────────────────────────────────────
          s -⟦V-Role⟧⇀ addUpkeep s V-Role

V-Role⇒ND : s -⟦V-Role⟧⇀ s' → just s ND.-⟦ SLOT / EMPTY ⟧⇀ s'
V-Role⇒ND (V-Role x x₁ x₂) = Roles (V-Role x x₁ x₂)
V-Role⇒ND (No-V-Role x x₁) = Roles (No-V-Role x x₁)

opaque
  V-Role-total : LeiosState.needsUpkeep s V-Role → ∃[ s' ] s -⟦V-Role⟧⇀ s'
  V-Role-total {s = s} h = let open LeiosState s in case Dec-canProduceV of λ where
    (yes p) → -, V-Role h p (proj₂ FFD.FFD-total)
    (no ¬p) → -, No-V-Role h ¬p

V-Role-Upkeep : s -⟦V-Role⟧⇀ s' → LeiosState.needsUpkeep s V-Role × ¬ LeiosState.needsUpkeep s' V-Role
V-Role-Upkeep {s = s} (V-Role x x₁ x₂) = x , (addUpkeep⇒¬needsUpkeep {s = s})
V-Role-Upkeep {s = s} (No-V-Role x x₁) = x , (addUpkeep⇒¬needsUpkeep {s = s})

upd-Upkeep : ∀ {x} → LeiosState.Upkeep s ≡ LeiosState.Upkeep (upd s x)
upd-Upkeep {record { IBBodies = bds }} {inj₁ (ibHeader h)} with A.any? (matchIB? h) bds
... | yes p = refl
... | no ¬p = refl
upd-Upkeep {_} {inj₁ (ebHeader _)} = refl 
upd-Upkeep {_} {inj₁ (vHeader _)} = refl
upd-Upkeep {record { IBHeaders = hds }} {inj₂ (ibBody b)} with A.any? (flip matchIB? b) hds
... | yes p = refl
... | no ¬p = refl

open import Data.List.Properties

↑-Upkeep : ∀ {x} → LeiosState.Upkeep s ≡ LeiosState.Upkeep (s ↑ x)
↑-Upkeep {s} {[]} = {!!}
↑-Upkeep {s} {x ∷ x₁} =
  let xx = ↑-Upkeep {s} {x₁}
      yy = upd-Upkeep {s} {x}
      -- zz = cong LeiosState.Upkeep (foldr-++ (flip upd) s (x ∷ []) x₁)
  in {!!}

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
--       ∙ Upkeep ≡ᵉ allUpkeep
       ∙ bs B.-⟦ B.FTCH-LDG / B.BASE-LDG rbs ⟧⇀ bs'
       ∙ ffds FFD.-⟦ Fetch / FetchRes msgs ⟧⇀ ffds'
       ∙ s0 -⟦Base⟧⇀    s1
       ∙ s1 -⟦IB-Role⟧⇀ s2
       ∙ s2 -⟦EB-Role⟧⇀ s3
       ∙ s3 -⟦V-Role⟧⇀  s4
       ───────────────────────────────────────────────────────────────────────
       s -⟦ SLOT / EMPTY ⟧⇀ s4

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
{-
-⟦/⟧⇀⇒ND : s -⟦ i / o ⟧⇀ s' → ∃₂[ i , o ] (s -⟦ i / o ⟧ⁿᵈ*⇀ s')
-⟦/⟧⇀⇒ND (Slot x x₁ x₂ hB hIB hEB hV) = replicate 5 SLOT , replicate 5 EMPTY ,
  (BS-ind (ND.Slot x x₁ x₂) $
   BS-ind (Base⇒ND hB) $
   BS-ind (IB-Role⇒ND hIB) $
   BS-ind (EB-Role⇒ND hEB) $
   STS⇒RTC (V-Role⇒ND hV))
-⟦/⟧⇀⇒ND Ftch = _ , _ , STS⇒RTC Ftch
-⟦/⟧⇀⇒ND Base₁ = _ , _ , STS⇒RTC Base₁
-}
open Computational22 ⦃...⦄

open import Function.Related.TypeIsomorphisms
open import Function.Bundles using (Equivalence)
open Equivalence

a≢b→a∉b : ∀ {A} {a b : A} → a ≢ b → a ∉ singleton b
a≢b→a∉b = to (¬-cong-⇔ ∈-singleton)

module _ ⦃ Computational-B : Computational22 B._-⟦_/_⟧⇀_ String ⦄
         ⦃ Computational-FFD : Computational22 FFD._-⟦_/_⟧⇀_ String ⦄ where
  instance
    Computational--⟦/⟧⇀ : Computational22 _-⟦_/_⟧⇀_ String
    Computational--⟦/⟧⇀ .computeProof s (INIT x) = failure "No handling of INIT here"
    Computational--⟦/⟧⇀ .computeProof s (SUBMIT (inj₁ eb)) = failure "Cannot submit EB here"
    Computational--⟦/⟧⇀ .computeProof s (SUBMIT (inj₂ txs)) = success (-, Base₁)
    Computational--⟦/⟧⇀ .computeProof s SLOT = let open LeiosState s in
      case (¿ Upkeep ≡ᵉ allUpkeep ¿ ,′ computeProof BaseState B.FTCH-LDG ,′ computeProof FFDState FFD.Fetch) of λ where
        (_ {- yes p -}, success ((B.BASE-LDG l , bs) , p₁) , success ((FFD.FetchRes msgs , ffds) , p₂)) →
          success (let
            open ≡-Reasoning
            s = _ -- solved later by unification
            s0 = s ↑ L.filter isValid? msgs
            upkeep≡∅ : LeiosState.Upkeep s0 ≡ ∅
            upkeep≡∅ = sym (↑-Upkeep {s = s} {x = L.filter isValid? msgs})
            (s1 , base-step) = Base-total {s = s0} (subst (Base ∉_) (sym upkeep≡∅) Properties.∉-∅)

            upkeep-s1≡Base : LeiosState.Upkeep s1 ≡ singleton Base
            upkeep-s1≡Base = {!!} 

            (s2 , ib-step) = IB-Role-total {s = s1} (subst (IB-Role ∉_) (sym upkeep-s1≡Base) (a≢b→a∉b λ ()))
            (s3 , eb-step) = EB-Role-total {s = s2} {!!}
            (s4 , v-step) = V-Role-total {s = s3} {!!}
            in (_ , Slot {- p -} p₁ p₂ base-step ib-step eb-step v-step))
        (_ {-yes p-} , _ , _) → failure "Subsystem failed"
        -- (_ {-no ¬p-} , _) → failure "Upkeep incorrect"
    Computational--⟦/⟧⇀ .computeProof s FTCH-LDG = success (-, Ftch)
    Computational--⟦/⟧⇀ .completeness = {!!}


  open import Data.Product
  open import Class.Computational

  v : VTy
  v = {!!}
  
  sd : StakeDistr
  sd = {!!}

  bs : B.State
  bs = {!!}

  test₁ : ∀ tx
    → Σ[ x ∈ LeiosOutput × LeiosState ] compute (initLeiosState v sd bs) (SUBMIT (inj₂ [ tx ]))
      ≡ success x
  test₁ tx = -, refl

  test₂ :
      Σ[ x ∈ LeiosOutput × LeiosState ] compute (initLeiosState v sd bs) SLOT
      ≡ success x
  test₂ = -, {!refl!} -- refl

  trace : ComputationResult String (List LeiosOutput × LeiosState)
  trace = {!!} -- computeTrace (initLeiosState v sd bs) (SLOT ∷ SLOT ∷ [])
