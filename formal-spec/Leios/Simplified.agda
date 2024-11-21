{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id)
open import Leios.FFD
open import Leios.SpecStructure

module Leios.Simplified (⋯ : SpecStructure) (let open SpecStructure ⋯) (Λ μ : ℕ) where

open import Leios.Protocol (⋯)

open FFD
open GenFFD

-- Predicates about EBs
module _ (s : LeiosState) (eb : EndorserBlock) where
  open EndorserBlockOSig eb
  open LeiosState s

  vote2Eligible : Type
  vote2Eligible = length ebRefs ≥ lengthˢ candidateEBs / 2 -- should this be `>`?
                × fromList ebRefs ⊆ candidateEBs
    where candidateEBs : ℙ Hash
          candidateEBs = mapˢ getEBRef $ filterˢ (_∈ᴮ slice L slot (μ + 3)) (fromList EBs)

private variable s s'  : LeiosState
                 ffds' : FFD.State
                 π     : VrfPf

data _↝_ : LeiosState → LeiosState → Type where

  IB-Role : let open LeiosState s renaming (FFDState to ffds)
                b = ibBody (record { txs = ToPropose })
                h = ibHeader (mkIBHeader slot id π sk-IB ToPropose)
          in
          ∙ needsUpkeep IB-Role
          ∙ canProduceIB slot sk-IB (stake s) π
          ∙ ffds FFD.-⟦ Send h (just b) / SendRes ⟧⇀ ffds'
          ─────────────────────────────────────────────────────────────────────────
          s ↝ addUpkeep record s { FFDState = ffds' } IB-Role

  EB-Role : let open LeiosState s renaming (FFDState to ffds)
                LI = map getIBRef $ filter (_∈ᴮ slice L slot (Λ + 1)) IBs
                LE = map getEBRef $ filter (isVote1Certified votingState) $
                           filter (_∈ᴮ slice L slot (μ + 2)) EBs
                h = mkEB slot id π sk-EB LI LE
          in
          ∙ needsUpkeep EB-Role
          ∙ canProduceEB slot sk-EB (stake s) π
          ∙ ffds FFD.-⟦ Send (ebHeader h) nothing / SendRes ⟧⇀ ffds'
          ─────────────────────────────────────────────────────────────────────────
          s ↝ addUpkeep record s { FFDState = ffds' } EB-Role

  V1-Role : let open LeiosState s renaming (FFDState to ffds)
                EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot (μ + 1)) EBs
                votes = map (vote sk-V ∘ hash) EBs'
          in
          ∙ needsUpkeep V1-Role
          ∙ canProduceV1 slot sk-V (stake s)
          ∙ ffds FFD.-⟦ Send (vHeader votes) nothing / SendRes ⟧⇀ ffds'
          ─────────────────────────────────────────────────────────────────────────
          s ↝ addUpkeep record s { FFDState = ffds' } V1-Role

  V2-Role : let open LeiosState s renaming (FFDState to ffds)
                EBs' = filter (vote2Eligible s) $ filter (_∈ᴮ slice L slot 1) EBs
                votes = map (vote sk-V ∘ hash) EBs'
          in
          ∙ needsUpkeep V2-Role
          ∙ canProduceV2 slot sk-V (stake s)
          ∙ ffds FFD.-⟦ Send (vHeader votes) nothing / SendRes ⟧⇀ ffds'
          ─────────────────────────────────────────────────────────────────────────
          s ↝ addUpkeep record s { FFDState = ffds' } V2-Role

  -- Note: Base doesn't need a negative rule, since it can always be invoked

  No-IB-Role : let open LeiosState s in
          ∙ needsUpkeep IB-Role
          ∙ ¬ canProduceIB slot sk-IB (stake s) π
          ─────────────────────────────────────────────
          s ↝ addUpkeep s IB-Role

  No-EB-Role : let open LeiosState s in
          ∙ needsUpkeep EB-Role
          ∙ ¬ canProduceEB slot sk-EB (stake s) π
          ─────────────────────────────────────────────
          s ↝ addUpkeep s EB-Role

  No-V1-Role : let open LeiosState s in
          ∙ needsUpkeep V1-Role
          ∙ ¬ canProduceV1 slot sk-V (stake s)
          ─────────────────────────────────────────────
          s ↝ addUpkeep s V1-Role

  No-V2-Role : let open LeiosState s in
          ∙ needsUpkeep V2-Role
          ∙ ¬ canProduceV2 slot sk-V (stake s)
          ─────────────────────────────────────────────
          s ↝ addUpkeep s V2-Role


allUpkeep : ℙ SlotUpkeep
allUpkeep = fromList (Base ∷ IB-Role ∷ EB-Role ∷ V1-Role ∷ V2-Role ∷ [])

module SimplifiedRules = Rules _↝_ allUpkeep
open SimplifiedRules public
