{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id)
open import Leios.FFD
open import Leios.SpecStructure

module Leios.UniformShort (⋯ : SpecStructure) (let open SpecStructure ⋯) where

open import Leios.Protocol (⋯)

open FFD
open GenFFD

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
                LI = map getIBRef $ filter (_∈ᴮ slice L slot 3) IBs
                LE = map getEBRef $ filter (isVote1Certified votingState) $
                           filter (_∈ᴮ slice L slot 3) EBs
                h = mkEB slot id π sk-EB LI LE
          in
          ∙ needsUpkeep EB-Role
          ∙ canProduceEB slot sk-EB (stake s) π
          ∙ ffds FFD.-⟦ Send (ebHeader h) nothing / SendRes ⟧⇀ ffds'
          ─────────────────────────────────────────────────────────────────────────
          s ↝ addUpkeep record s { FFDState = ffds' } EB-Role

  V1-Role : let open LeiosState s renaming (FFDState to ffds)
                EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot 2) EBs
                votes = map (vote sk-V ∘ hash) EBs'
          in
          ∙ needsUpkeep V1-Role
          ∙ canProduceV1 slot sk-V (stake s)
          ∙ ffds FFD.-⟦ Send (vHeader votes) nothing / SendRes ⟧⇀ ffds'
          ─────────────────────────────────────────────────────────────────────────
          s ↝ addUpkeep record s { FFDState = ffds' } V1-Role

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


allUpkeep : ℙ SlotUpkeep
allUpkeep = fromList (Base ∷ IB-Role ∷ EB-Role ∷ V1-Role ∷ [])

module UniformShortRules = Rules _↝_ allUpkeep
open UniformShortRules public
