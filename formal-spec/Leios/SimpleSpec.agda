{-# OPTIONS --allow-unsolved-metas #-}

open import Leios.Prelude
open import Leios.Abstract
open import Leios.FFD
import Leios.Blocks

module Leios.SimpleSpec (a : LeiosAbstract) (let open LeiosAbstract a) (let open Leios.Blocks a)
  (id : PoolID) (pKey : PrivKey) (FFD : FFDAbstract.Functionality ffdAbstract) where

import Leios.BaseFunctionality

module FFD' = FFDAbstract.Functionality FFD using (State) renaming (stepRel to _⇀⟦_⟧_)
module B = Leios.BaseFunctionality a

-- High level structure:


--                                      (simple) Leios
--                                        /         |
-- +-------------------------------------+          |
-- | Header Diffusion     Body Diffusion |          |
-- +-------------------------------------+       Base Protocol
--                                        \      /
--                                        Network

postulate VTy FTCHTy : Type
          initSlot : VTy → ℕ
          initFFDState : FFD'.State

data LeiosInput : Type where
  INIT     : VTy → LeiosInput
  SLOT     : LeiosInput
  FTCH-LDG : LeiosInput

data LeiosOutput : Type where
  FTCH-LDG : FTCHTy → LeiosOutput
  EMPTY : LeiosOutput

record LeiosState : Type where
  field V : VTy
        SD : B.StakeDistr
        FFDState : FFD'.State
        Ledger : List Tx
        MemPool : List Tx
        IBs : List InputBlock
        EBs : List EndorserBlock
        Vs  : List (List Vote)
        slot : ℕ

initLeiosState : VTy → B.StakeDistr → LeiosState
initLeiosState V SD = record
  { V        = V
  ; SD       = SD
  ; FFDState = initFFDState
  ; Ledger   = []
  ; MemPool  = []
  ; IBs      = []
  ; EBs      = []
  ; Vs       = []
  ; slot     = initSlot V
  }

postulate canProduceIB : ℕ → VrfPf → Type
          canProduceEB : ℕ → VrfPf → Type
          canProduceV1 : ℕ → Type
          canProduceV2 : ℕ → Type

-- some predicates about EBs
module _ (s : LeiosState) (eb : EndorserBlock) where
  open EndorserBlockOSig eb
  open LeiosState s

  postulate isVote1Certified : Type -- Q: what's the threshold? (pg 7, (5))

  vote2Eligible : Type
  vote2Eligible = length ebRefs ≥ lengthˢ candidateEBs / 2 -- should this be `>`?
                × fromList ebRefs ⊆ candidateEBs
    where candidateEBs : ℙ Hash
          candidateEBs = mapˢ getEBRef $ filterˢ (_∈ᴮ slice L slot (μ + 3)) (fromList EBs)

  allIBRefsKnown : Type
  allIBRefsKnown = ∀[ ref ∈ fromList ibRefs ] ref ∈ˡ map getIBRef IBs

postulate instance isVote1Certified? : ∀ {s eb} → isVote1Certified s eb ⁇

private variable s     : LeiosState
                 ffds' : FFD'.State
                 π     : VrfPf

open LeiosState using (FFDState; MemPool)

data _⇀⟦_⟧_ : Maybe LeiosState → LeiosInput → LeiosState × LeiosOutput → Type where
  Init : ∀ {V bs bs' SD} →
       ∙ {!!} -- create & register the IB/EB lottery and voting keys with key reg
       ∙ bs B.⇀⟦ B.INIT {!V_chkCerts!} ⟧ (bs' , B.STAKE SD)
       ───────────────────────────────────────────────────
       nothing ⇀⟦ INIT V ⟧ (initLeiosState V SD , EMPTY)

  -- fix: we need to do Slot before every other SLOT transition
  Slot : ∀ {msgs} → let ffds = s .FFDState
                        l = {!!} -- construct ledger l
         in
       ∙ FFDAbstract.Fetch FFD'.⇀⟦ ffds ⟧ (ffds' , FFDAbstract.FetchRes msgs)
       ──────────────────────────────────────────────────────────────────────
         just s ⇀⟦ SLOT ⟧ (record s { FFDState = ffds' ; Ledger = l } , EMPTY)

  Ftch : ∀ {l} →
       ────────────────────────────────────
       just s ⇀⟦ FTCH-LDG ⟧ (s , FTCH-LDG l)

  -- TODO: Base chain

  IB-Role : let open LeiosState s
                txs  = s .MemPool
                ffds = s .FFDState
                b = GenFFD.ibBody (record { txs = txs })
                h = GenFFD.ibHeader (mkIBHeader slot id π pKey txs)
          in
          ∙ canProduceIB slot π
          ∙ FFDAbstract.Send h (just b) FFD'.⇀⟦ ffds ⟧ (ffds' , FFDAbstract.SendRes)
          ─────────────────────────────────────────────────────────────────────────
          just s ⇀⟦ SLOT ⟧ (record s { FFDState = ffds' } , EMPTY)

  EB-Role : let open LeiosState s
                LI = map {F = List} getIBRef $ setToList $ filterˢ (_∈ᴮ slice L slot (Λ + 1)) (fromList IBs)
                LE = map getEBRef $ setToList $ filterˢ (isVote1Certified s) $
                           filterˢ (_∈ᴮ slice L slot (μ + 2)) (fromList EBs)
                h = mkEB slot id π pKey LI LE
                ffds = s .FFDState
          in
          ∙ canProduceEB slot π
          ∙ FFDAbstract.Send (GenFFD.ebHeader h) nothing FFD'.⇀⟦ ffds ⟧ (ffds' , FFDAbstract.SendRes)
          ──────────────────────────────────────────────────────────────────────────────────────────
          just s ⇀⟦ SLOT ⟧ (record s { FFDState = ffds' } , EMPTY)

  V1-Role : let open LeiosState s
                EBs' = filterˢ (allIBRefsKnown s) $ filterˢ (_∈ᴮ slice L slot (μ + 1)) (fromList EBs)
                votes = map (vote ∘ hash) (setToList EBs')
                ffds = s .FFDState
          in
          ∙ canProduceV1 slot
          ∙ FFDAbstract.Send (GenFFD.vHeader votes) nothing FFD'.⇀⟦ ffds ⟧ (ffds' , FFDAbstract.SendRes)
          ─────────────────────────────────────────────────────────────────────────────────────────────
          just s ⇀⟦ SLOT ⟧ (record s { FFDState = ffds' } , EMPTY)

  V2-Role : let open LeiosState s
                EBs' = filterˢ (vote2Eligible s) $ filterˢ (_∈ᴮ slice L slot 1) (fromList EBs)
                votes = map (vote ∘ hash) (setToList EBs')
                ffds = s .FFDState
          in
          ∙ canProduceV2 slot
          ∙ FFDAbstract.Send (GenFFD.vHeader votes) nothing FFD'.⇀⟦ ffds ⟧ (ffds' , FFDAbstract.SendRes)
          ─────────────────────────────────────────────────────────────────────────────────────────────
          just s ⇀⟦ SLOT ⟧ (record s { FFDState = ffds' } , EMPTY)
