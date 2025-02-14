--{-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}

--------------------------------------------------------------------------------
-- Deterministic variant of simple Leios
--------------------------------------------------------------------------------

open import Leios.Prelude hiding (id)
open import Prelude.Init using (∃₂-syntax)
open import Leios.FFD

import Data.List as L
open import Data.List.Relation.Unary.Any using (here)

open import Leios.SpecStructure

module Leios.Simplified.Deterministic (⋯ : SpecStructure 2) (let open SpecStructure ⋯) (Λ μ : ℕ) where

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
          ∙ eb ∷ ebs ≡ filter (λ eb → isVote2Certified s eb × eb ∈ᴮ slice L slot 2) EBs
          ∙ bs B.-⟦ B.SUBMIT (this eb) / B.EMPTY ⟧⇀ bs'
          ───────────────────────────────────────────────────────────────────────
          s -⟦Base⟧⇀ addUpkeep record s { BaseState = bs' } Base

  Base₂b  : let open LeiosState s renaming (BaseState to bs) in
          ∙ [] ≡ filter (λ eb → isVote2Certified s eb × eb ∈ᴮ slice L slot 2) EBs
          ∙ bs B.-⟦ B.SUBMIT (that ToPropose) / B.EMPTY ⟧⇀ bs'
          ───────────────────────────────────────────────────────────────────────
          s -⟦Base⟧⇀ addUpkeep record s { BaseState = bs' } Base

Base⇒ND : LeiosState.needsUpkeep s Base → s -⟦Base⟧⇀ s' → just s ND.-⟦ SLOT / EMPTY ⟧⇀ s'
Base⇒ND u (Base₂a x₁ x₂) = Base₂a u (subst (_ ∈_) x₁ (Equivalence.to ∈-fromList (here refl))) x₂
Base⇒ND u (Base₂b x₁ x₂) = Base₂b u x₁ x₂

Base-Upkeep : ∀ {u} → u ≢ Base → LeiosState.needsUpkeep s u → s -⟦Base⟧⇀ s'
                  → LeiosState.needsUpkeep s' u
Base-Upkeep u≢Base h (Base₂a _ _) u∈su = case Equivalence.from ∈-∪ u∈su of λ where
  (inj₁ x) → h x
  (inj₂ y) → u≢Base (Equivalence.from ∈-singleton y)
Base-Upkeep u≢Base h (Base₂b _ _) u∈su = case Equivalence.from ∈-∪ u∈su of λ where
  (inj₁ x) → h x
  (inj₂ y) → u≢Base (Equivalence.from ∈-singleton y)

opaque
  Base-total : ∃[ s' ] s -⟦Base⟧⇀ s'
  Base-total {s = s} with
    (let open LeiosState s in filter (λ eb → isVote2Certified s eb × eb ∈ᴮ slice L slot 2) EBs)
    in eq
  ... | []    = -, Base₂b (sym eq) (proj₂ B.SUBMIT-total)
  ... | x ∷ l = -, Base₂a (sym eq) (proj₂ B.SUBMIT-total)

  Base-total' : ⦃ Computational-B : Computational22 B._-⟦_/_⟧⇀_ String ⦄
              → ∃[ bs ] s -⟦Base⟧⇀ addUpkeep record s { BaseState = bs } Base
  Base-total' {s = s} = let open LeiosState s in
    case ∃[ ebs ] ebs ≡ filter (λ eb → isVote2Certified s eb × eb ∈ᴮ slice L slot 2) EBs ∋ -, refl
      of λ where
        (eb ∷ _ , eq) → -, Base₂a eq (proj₂ B.SUBMIT-total)
        ([]     , eq) → -, Base₂b eq (proj₂ B.SUBMIT-total)

data _-⟦IB-Role⟧⇀_ : LeiosState → LeiosState → Type where

  IB-Role : let open LeiosState s renaming (FFDState to ffds)
                b = ibBody (record { txs = ToPropose })
                h = ibHeader (mkIBHeader slot id π sk-IB ToPropose)
          in
          ∙ canProduceIB slot sk-IB (stake s) π
          ∙ ffds FFD.-⟦ Send h (just b) / SendRes ⟧⇀ ffds'
          ────────────────────────────────────────────────────────────────────
          s -⟦IB-Role⟧⇀ addUpkeep record s { FFDState = ffds' } IB-Role

  No-IB-Role : let open LeiosState s in
          ∙ (∀ π → ¬ canProduceIB slot sk-IB (stake s) π)
          ────────────────────────────────────────
          s -⟦IB-Role⟧⇀ addUpkeep s IB-Role

IB-Role⇒ND : LeiosState.needsUpkeep s IB-Role → s -⟦IB-Role⟧⇀ s' → just s ND.-⟦ SLOT / EMPTY ⟧⇀ s'
IB-Role⇒ND u (IB-Role x₁ x₂) = Roles (IB-Role u x₁ x₂)
IB-Role⇒ND u (No-IB-Role x₁) = Roles (No-IB-Role u x₁)

IB-Role-Upkeep : ∀ {u} → u ≢ IB-Role → LeiosState.needsUpkeep s u → s -⟦IB-Role⟧⇀ s'
                  → LeiosState.needsUpkeep s' u
IB-Role-Upkeep u≢IB-Role h (IB-Role _ _) u∈su = case Equivalence.from ∈-∪ u∈su of λ where
  (inj₁ x) → h x
  (inj₂ y) → u≢IB-Role (Equivalence.from ∈-singleton y)
IB-Role-Upkeep u≢IB-Role h (No-IB-Role _) u∈su = case Equivalence.from ∈-∪ u∈su of λ where
  (inj₁ x) → h x
  (inj₂ y) → u≢IB-Role (Equivalence.from ∈-singleton y)

opaque
  IB-Role-total : ∃[ s' ] s -⟦IB-Role⟧⇀ s'
  IB-Role-total {s = s} = let open LeiosState s in case Dec-canProduceIB of λ where
    (inj₁ (π , pf)) → -, IB-Role    pf (proj₂ FFD.FFD-Send-total)
    (inj₂ pf)       → -, No-IB-Role pf

  IB-Role-total' : ∃[ ffds ] s -⟦IB-Role⟧⇀ addUpkeep record s { FFDState = ffds } IB-Role
  IB-Role-total' {s = s} = let open LeiosState s in case Dec-canProduceIB of λ where
    (inj₁ (π , pf)) → -, IB-Role    pf (proj₂ FFD.FFD-Send-total)
    (inj₂ pf)       → -, No-IB-Role pf

data _-⟦EB-Role⟧⇀_ : LeiosState → LeiosState → Type where

  EB-Role : let open LeiosState s renaming (FFDState to ffds)
                LI = map getIBRef $ filter (_∈ᴮ slice L slot (Λ + 1)) IBs
                LE = map getEBRef $ filter (isVote1Certified s) $
                           filter (_∈ᴮ slice L slot (μ + 2)) EBs
                h = mkEB slot id π sk-EB LI LE
          in
          ∙ canProduceEB slot sk-EB (stake s) π
          ∙ ffds FFD.-⟦ Send (ebHeader h) nothing / SendRes ⟧⇀ ffds'
          ────────────────────────────────────────────────────────────────────
          s -⟦EB-Role⟧⇀ addUpkeep record s { FFDState = ffds' } EB-Role

  No-EB-Role : let open LeiosState s in
          ∙ (∀ π → ¬ canProduceEB slot sk-EB (stake s) π)
          ────────────────────────────────────────
          s -⟦EB-Role⟧⇀ addUpkeep s EB-Role

EB-Role⇒ND : LeiosState.needsUpkeep s EB-Role → s -⟦EB-Role⟧⇀ s' → just s ND.-⟦ SLOT / EMPTY ⟧⇀ s'
EB-Role⇒ND u (EB-Role x₁ x₂) = Roles (EB-Role u x₁ x₂)
EB-Role⇒ND u (No-EB-Role x₁) = Roles (No-EB-Role u x₁)

EB-Role-Upkeep : ∀ {u} → u ≢ EB-Role → LeiosState.needsUpkeep s u → s -⟦EB-Role⟧⇀ s'
                  → LeiosState.needsUpkeep s' u
EB-Role-Upkeep u≢EB-Role h (EB-Role _ _) u∈su = case Equivalence.from ∈-∪ u∈su of λ where
  (inj₁ x) → h x
  (inj₂ y) → u≢EB-Role (Equivalence.from ∈-singleton y)
EB-Role-Upkeep u≢EB-Role h (No-EB-Role _) u∈su = case Equivalence.from ∈-∪ u∈su of λ where
  (inj₁ x) → h x
  (inj₂ y) → u≢EB-Role (Equivalence.from ∈-singleton y)

opaque
  EB-Role-total : ∃[ s' ] s -⟦EB-Role⟧⇀ s'
  EB-Role-total {s = s} = let open LeiosState s in case Dec-canProduceEB of λ where
    (inj₁ (π , pf)) → -, EB-Role    pf (proj₂ FFD.FFD-Send-total)
    (inj₂ pf)       → -, No-EB-Role pf

  EB-Role-total' : ∃[ ffds ] s -⟦EB-Role⟧⇀ addUpkeep record s { FFDState = ffds } EB-Role
  EB-Role-total' {s = s} = let open LeiosState s in case Dec-canProduceEB of λ where
    (inj₁ (π , pf)) → -, EB-Role    pf (proj₂ FFD.FFD-Send-total)
    (inj₂ pf)       → -, No-EB-Role pf

data _-⟦V1-Role⟧⇀_ : LeiosState → LeiosState → Type where

  V1-Role : let open LeiosState s renaming (FFDState to ffds)
                EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot (μ + 1)) EBs
                votes = map (vote sk-V ∘ hash) EBs'
          in
          ∙ canProduceV1 slot sk-V (stake s)
          ∙ ffds FFD.-⟦ Send (vHeader votes) nothing / SendRes ⟧⇀ ffds'
          ────────────────────────────────────────────────────────────────────
          s -⟦V1-Role⟧⇀ addUpkeep record s { FFDState = ffds' } V1-Role

  No-V1-Role : let open LeiosState s in
          ∙ ¬ canProduceV1 slot sk-V (stake s)
          ────────────────────────────────────────
          s -⟦V1-Role⟧⇀ addUpkeep s V1-Role

V1-Role⇒ND : LeiosState.needsUpkeep s V1-Role → s -⟦V1-Role⟧⇀ s' → just s ND.-⟦ SLOT / EMPTY ⟧⇀ s'
V1-Role⇒ND u (V1-Role x₁ x₂) = Roles (V1-Role u x₁ x₂)
V1-Role⇒ND u (No-V1-Role x₁) = Roles (No-V1-Role u x₁)

V1-Role-Upkeep : ∀ {u} → u ≢ V1-Role → LeiosState.needsUpkeep s u → s -⟦V1-Role⟧⇀ s'
                  → LeiosState.needsUpkeep s' u
V1-Role-Upkeep u≢V1-Role h (V1-Role _ _) u∈su = case Equivalence.from ∈-∪ u∈su of λ where
  (inj₁ x) → h x
  (inj₂ y) → u≢V1-Role (Equivalence.from ∈-singleton y)
V1-Role-Upkeep u≢V1-Role h (No-V1-Role _) u∈su = case Equivalence.from ∈-∪ u∈su of λ where
  (inj₁ x) → h x
  (inj₂ y) → u≢V1-Role (Equivalence.from ∈-singleton y)

opaque
  V1-Role-total : ∃[ s' ] s -⟦V1-Role⟧⇀ s'
  V1-Role-total {s = s} = let open LeiosState s in case Dec-canProduceV1 of λ where
    (yes p) → -, V1-Role p (proj₂ FFD.FFD-Send-total)
    (no ¬p) → -, No-V1-Role ¬p

  V1-Role-total' : ∃[ ffds ] s -⟦V1-Role⟧⇀ addUpkeep record s { FFDState = ffds } V1-Role
  V1-Role-total' {s = s} = let open LeiosState s in case Dec-canProduceV1 of λ where
    (yes p) → -, V1-Role    p (proj₂ FFD.FFD-Send-total)
    (no ¬p) → -, No-V1-Role ¬p

data _-⟦V2-Role⟧⇀_ : LeiosState → LeiosState → Type where

  V2-Role : let open LeiosState s renaming (FFDState to ffds)
                EBs' = filter (vote2Eligible s) $ filter (_∈ᴮ slice L slot 1) EBs
                votes = map (vote sk-V ∘ hash) EBs'
          in
          ∙ canProduceV2 slot sk-V (stake s)
          ∙ ffds FFD.-⟦ Send (vHeader votes) nothing / SendRes ⟧⇀ ffds'
          ────────────────────────────────────────────────────────────────────
          s -⟦V2-Role⟧⇀ addUpkeep record s { FFDState = ffds' } V2-Role

  No-V2-Role : let open LeiosState s in
          ∙ ¬ canProduceV2 slot sk-V (stake s)
          ────────────────────────────────────────
          s -⟦V2-Role⟧⇀ addUpkeep s V2-Role

V2-Role⇒ND : LeiosState.needsUpkeep s V2-Role → s -⟦V2-Role⟧⇀ s' → just s ND.-⟦ SLOT / EMPTY ⟧⇀ s'
V2-Role⇒ND u (V2-Role x₁ x₂) = Roles (V2-Role u x₁ x₂)
V2-Role⇒ND u (No-V2-Role x₁) = Roles (No-V2-Role u x₁)

V2-Role-Upkeep : ∀ {u} → u ≢ V2-Role → LeiosState.needsUpkeep s u → s -⟦V2-Role⟧⇀ s'
                  → LeiosState.needsUpkeep s' u
V2-Role-Upkeep u≢V2-Role h (V2-Role _ _) u∈su = case Equivalence.from ∈-∪ u∈su of λ where
  (inj₁ x) → h x
  (inj₂ y) → u≢V2-Role (Equivalence.from ∈-singleton y)
V2-Role-Upkeep u≢V2-Role h (No-V2-Role _) u∈su = case Equivalence.from ∈-∪ u∈su of λ where
  (inj₁ x) → h x
  (inj₂ y) → u≢V2-Role (Equivalence.from ∈-singleton y)

opaque
  V2-Role-total : ∃[ s' ] s -⟦V2-Role⟧⇀ s'
  V2-Role-total {s = s} = let open LeiosState s in case Dec-canProduceV2 of λ where
    (yes p) → -, V2-Role p (proj₂ FFD.FFD-Send-total)
    (no ¬p) → -, No-V2-Role ¬p

  V2-Role-total' : ∃[ ffds ] s -⟦V2-Role⟧⇀ addUpkeep record s { FFDState = ffds } V2-Role
  V2-Role-total' {s = s} = let open LeiosState s in case Dec-canProduceV2 of λ where
    (yes p) → -, V2-Role    p (proj₂ FFD.FFD-Send-total)
    (no ¬p) → -, No-V2-Role ¬p

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
-⟦/⟧⇀⇒ND (Slot {s = s} {msgs = msgs} {s1 = s1} {s2 = s2} {s3 = s3} {s4 = s4} x x₁ x₂ hB hIB hEB hV1 hV2) = replicate 6 SLOT , replicate 6 EMPTY ,
  let
    s0 = _
    upkeep≡∅ : LeiosState.Upkeep s0 ≡ ∅
    upkeep≡∅ = sym (↑-preserves-Upkeep {x = L.filter isValid? msgs})
    needsAllUpkeep : ∀ {u} → LeiosState.needsUpkeep s0 u
    needsAllUpkeep {u} = subst (u ∉_) (sym upkeep≡∅) Properties.∉-∅
    needsUpkeep1 : ∀ {u} → u ≢ Base → LeiosState.needsUpkeep s1 u
    needsUpkeep1 h1 = Base-Upkeep h1 needsAllUpkeep hB
    needsUpkeep2 : ∀ {u} → u ≢ Base → u ≢ IB-Role → LeiosState.needsUpkeep s2 u
    needsUpkeep2 h1 h2 = IB-Role-Upkeep h2 (needsUpkeep1 h1) hIB
    needsUpkeep3 : ∀ {u} → u ≢ Base → u ≢ IB-Role → u ≢ EB-Role → LeiosState.needsUpkeep s3 u
    needsUpkeep3 h1 h2 h3 = EB-Role-Upkeep h3 (needsUpkeep2 h1 h2) hEB
    needsUpkeep4 : ∀ {u} → u ≢ Base → u ≢ IB-Role → u ≢ EB-Role → u ≢ V1-Role → LeiosState.needsUpkeep s4 u
    needsUpkeep4 h1 h2 h3 h4 = V1-Role-Upkeep h4 (needsUpkeep3 h1 h2 h3) hV1
  in (BS-ind (ND.Slot x x₁ x₂) $
      BS-ind (Base⇒ND {s = s0} needsAllUpkeep hB) $
      BS-ind (IB-Role⇒ND (needsUpkeep1 (λ ())) hIB) $
      BS-ind (EB-Role⇒ND (needsUpkeep2 (λ ()) (λ ())) hEB) $
      BS-ind (V1-Role⇒ND (needsUpkeep3 (λ ()) (λ ()) (λ ())) hV1) $
      STS⇒RTC (V2-Role⇒ND (needsUpkeep4 (λ ()) (λ ()) (λ ()) (λ ())) hV2))
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
    Computational--⟦/⟧⇀ .computeProof s* SLOT = let open LeiosState s* in
      case (¿ Upkeep ≡ᵉ allUpkeep ¿ ,′ computeProof BaseState B.FTCH-LDG ,′ computeProof FFDState FFD.Fetch) of λ where
        (yes p , success ((B.BASE-LDG l , bs) , p₁) , success ((FFD.FetchRes msgs , ffds) , p₂)) →
          success ((_ , (Slot p p₁ p₂ (proj₂ Base-total) (proj₂ IB-Role-total) (proj₂ EB-Role-total) (proj₂ V1-Role-total) (proj₂ V2-Role-total))))
        (yes p , _ , _) → failure "Subsystem failed"
        (no ¬p , _) → failure "Upkeep incorrect"
    Computational--⟦/⟧⇀ .computeProof s FTCH-LDG = success (-, Ftch)
    Computational--⟦/⟧⇀ .completeness = {!!}
