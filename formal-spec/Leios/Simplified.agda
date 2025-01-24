{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id)
open import Leios.FFD
open import Leios.SpecStructure
open import Data.Fin.Patterns

open import Tactic.Defaults
open import Tactic.Derive.DecEq

module Leios.Simplified (⋯ : SpecStructure 2) (let open SpecStructure ⋯) (Λ μ : ℕ) where

data SlotUpkeep : Type where
  Base IB-Role EB-Role V1-Role V2-Role : SlotUpkeep

unquoteDecl DecEq-SlotUpkeep = derive-DecEq ((quote SlotUpkeep , DecEq-SlotUpkeep) ∷ [])

allUpkeep : ℙ SlotUpkeep
allUpkeep = fromList (Base ∷ IB-Role ∷ EB-Role ∷ V1-Role ∷ V2-Role ∷ [])

open import Leios.Protocol (⋯) SlotUpkeep public

open BaseAbstract B' using (Cert; V-chkCerts; VTy; initSlot)
open FFD hiding (_-⟦_/_⟧⇀_)
open GenFFD

isVote1Certified : LeiosState → EndorserBlock → Type
isVote1Certified s eb = isVoteCertified (LeiosState.votingState s) (0F , eb)

isVote2Certified : LeiosState → EndorserBlock → Type
isVote2Certified s eb = isVoteCertified (LeiosState.votingState s) (1F , eb)

-- Predicates about EBs
module _ (s : LeiosState) (eb : EndorserBlock) where
  open EndorserBlockOSig eb
  open LeiosState s

  vote2Eligible : Type
  vote2Eligible = length ebRefs ≥ lengthˢ candidateEBs / 2 -- should this be `>`?
                × fromList ebRefs ⊆ candidateEBs
    where candidateEBs : ℙ Hash
          candidateEBs = mapˢ getEBRef $ filterˢ (_∈ᴮ slice L slot (μ + 3)) (fromList EBs)

private variable s s'   : LeiosState
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
                LE = map getEBRef $ filter (isVote1Certified s) $
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
          ∙ (∀ π → ¬ canProduceIB slot sk-IB (stake s) π)
          ─────────────────────────────────────────────
          s ↝ addUpkeep s IB-Role

  No-EB-Role : let open LeiosState s in
          ∙ needsUpkeep EB-Role
          ∙ (∀ π → ¬ canProduceEB slot sk-EB (stake s) π)
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

data _-⟦_/_⟧⇀_ : Maybe LeiosState → LeiosInput → LeiosOutput → LeiosState → Type where

  -- Initialization

  Init :
       ∙ ks K.-⟦ K.INIT pk-IB pk-EB pk-V / K.PUBKEYS pks ⟧⇀ ks'
       ∙ initBaseState B.-⟦ B.INIT (V-chkCerts pks) / B.STAKE SD ⟧⇀ bs'
       ────────────────────────────────────────────────────────────────
       nothing -⟦ INIT V / EMPTY ⟧⇀ initLeiosState V SD bs' pks

  -- Network and Ledger

  Slot : let open LeiosState s renaming (FFDState to ffds; BaseState to bs) in
       ∙ Upkeep ≡ᵉ allUpkeep
       ∙ bs B.-⟦ B.FTCH-LDG / B.BASE-LDG rbs ⟧⇀ bs'
       ∙ ffds FFD.-⟦ Fetch / FetchRes msgs ⟧⇀ ffds'
       ───────────────────────────────────────────────────────────────────────
       just s -⟦ SLOT / EMPTY ⟧⇀ record s
           { FFDState  = ffds'
           ; Ledger    = constructLedger rbs
           ; slot      = suc slot
           ; Upkeep    = ∅
           ; BaseState = bs'
           } ↑ L.filter (isValid? s) msgs

  Ftch :
       ────────────────────────────────────────────────────────
       just s -⟦ FTCH-LDG / FTCH-LDG (LeiosState.Ledger s) ⟧⇀ s

  -- Base chain
  --
  -- Note: Submitted data to the base chain is only taken into account
  --       if the party submitting is the block producer on the base chain
  --       for the given slot

  Base₁   :
          ───────────────────────────────────────────────────────────────────
          just s -⟦ SUBMIT (inj₂ txs) / EMPTY ⟧⇀ record s { ToPropose = txs }

  Base₂a  : let open LeiosState s renaming (BaseState to bs) in
          ∙ needsUpkeep Base
          ∙ eb ∈ filter (λ eb → isVote2Certified s eb × eb ∈ᴮ slice L slot 2) EBs
          ∙ bs B.-⟦ B.SUBMIT (this eb) / B.EMPTY ⟧⇀ bs'
          ───────────────────────────────────────────────────────────────────────
          just s -⟦ SLOT / EMPTY ⟧⇀ addUpkeep record s { BaseState = bs' } Base

  Base₂b  : let open LeiosState s renaming (BaseState to bs) in
          ∙ needsUpkeep Base
          ∙ [] ≡ filter (λ eb → isVote2Certified s eb × eb ∈ᴮ slice L slot 2) EBs
          ∙ bs B.-⟦ B.SUBMIT (that ToPropose) / B.EMPTY ⟧⇀ bs'
          ───────────────────────────────────────────────────────────────────────
          just s -⟦ SLOT / EMPTY ⟧⇀ addUpkeep record s { BaseState = bs' } Base

  -- Protocol rules

  Roles : ∙ s ↝ s'
          ─────────────────────────────
          just s -⟦ SLOT / EMPTY ⟧⇀ s'
