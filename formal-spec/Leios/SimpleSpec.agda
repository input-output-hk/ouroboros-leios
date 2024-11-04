{-# OPTIONS --allow-unsolved-metas #-}

open import Leios.Prelude
open import Leios.Abstract
open import Leios.FFD
open import Leios.VRF

import Leios.Base
import Leios.Blocks
import Leios.KeyRegistration

open import Data.List.Properties using (length-map)

module Leios.SimpleSpec (a : LeiosAbstract) (let open LeiosAbstract a) (let open Leios.Blocks a)
  (id : PoolID) (pKey : PrivKey) (FFD' : FFDAbstract.Functionality ffdAbstract)
  (vrf' : LeiosVRF a) (let open LeiosVRF vrf') (pubKey : PubKey)
  (let open Leios.Base a) (B' : BaseAbstract) (BF' : BaseAbstract.Functionality B')
  (let open Leios.KeyRegistration a vrf') (K' : KeyRegistrationAbstract) (KF' : KeyRegistrationAbstract.Functionality K') where

module B   = BaseAbstract B'
module BF  = BaseAbstract.Functionality BF'
module K   = KeyRegistrationAbstract K'
module KF  = KeyRegistrationAbstract.Functionality KF'
module FFD = FFDAbstract.Functionality FFD' using (State) renaming (stepRel to _⇀⟦_⟧_)

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
          initFFDState : FFD.State

data LeiosInput : Type where
  INIT     : VTy → LeiosInput
  SUBMIT   : List Tx → LeiosInput
  SLOT     : LeiosInput
  FTCH-LDG : LeiosInput

data LeiosOutput : Type where
  FTCH-LDG : FTCHTy → LeiosOutput
  EMPTY : LeiosOutput

record LeiosState : Type where
  field V : VTy
        SD : StakeDistr
        FFDState : FFD.State
        Ledger : List Tx
        MemPool : List Tx
        IBs : List InputBlock
        EBs : List EndorserBlock
        Vs  : List (List Vote)
        slot : ℕ

  lookupEB : EBRef → Maybe EndorserBlock
  lookupEB r with i ← findIndex (_≟ r) (map getEBRef EBs) rewrite length-map getEBRef EBs
    = map (lookup EBs) i

  lookupIB : IBRef → Maybe InputBlock
  lookupIB r with i ← findIndex (_≟ r) (map getIBRef IBs) rewrite length-map getIBRef IBs
    = map (lookup IBs) i

  lookupTxs : EndorserBlock → List Tx
  lookupTxs = join ∘ map txs ∘ map body ∘ mapMaybe lookupIB ∘ join ∘ map ibRefs ∘ mapMaybe lookupEB ∘ ebRefs
    where open EndorserBlockOSig
          open IBBody
          open InputBlock

  constructLedger : List EndorserBlock → List Tx
  constructLedger = join ∘ map lookupTxs

initLeiosState : VTy → StakeDistr → LeiosState
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

postulate canProduceV1 : ℕ → Type
          canProduceV2 : ℕ → Type

-- some predicates about EBs
module _ (s : LeiosState) (eb : EndorserBlock) where
  open EndorserBlockOSig eb
  open LeiosState s

  postulate isVote1Certified : Type -- Q: what's the threshold? (pg 7, (5))
  postulate isVote2Certified : Type

  vote2Eligible : Type
  vote2Eligible = length ebRefs ≥ lengthˢ candidateEBs / 2 -- should this be `>`?
                × fromList ebRefs ⊆ candidateEBs
    where candidateEBs : ℙ Hash
          candidateEBs = mapˢ getEBRef $ filterˢ (_∈ᴮ slice L slot (μ + 3)) (fromList EBs)

  allIBRefsKnown : Type
  allIBRefsKnown = ∀[ ref ∈ fromList ibRefs ] ref ∈ˡ map getIBRef IBs

postulate instance isVote1Certified? : ∀ {s eb} → isVote1Certified s eb ⁇
                   isVote2Certified? : ∀ {s eb} → isVote2Certified s eb ⁇

private variable s     : LeiosState
                 ffds' : FFD.State
                 π     : VrfPf

stake : LeiosState → ℕ
stake record { SD = SD } = case lookupᵐ? SD id of λ where
  (just s) → s
  nothing  → 0

postulate
  V_chkCerts : List PubKey → (EndorserBlock × B.Cert) → Type

data _⇀⟦_⟧_ : Maybe LeiosState → LeiosInput → LeiosState × LeiosOutput → Type where

  -- Initialization

  Init : ∀ {V bs bs' SD ks ks' pkey pkeys} →
       ∙ ks KF.⇀⟦ K.INIT pkey ⟧ (ks' , K.PUBKEYS pkeys) -- create & register the IB/EB lottery and voting keys with key reg
       ∙ bs BF.⇀⟦ B.INIT (V_chkCerts pkeys) ⟧ (bs' , B.STAKE SD)
       ──────────────────────────────────────────────────────
       nothing ⇀⟦ INIT V ⟧ (initLeiosState V SD , EMPTY)

  -- Network and Ledger

  -- fix: we need to do Slot before every other SLOT transition
  Slot : ∀ {bs bs' msgs ebs} → let open LeiosState s renaming (FFDState to ffds) in
       ∙ bs BF.⇀⟦ B.FTCH-LDG ⟧ (bs' , B.LDG ebs)
       ∙ FFDAbstract.Fetch FFD.⇀⟦ ffds ⟧ (ffds' , FFDAbstract.FetchRes msgs)
       ────────────────────────────────────────────────────────────────────────────────────────
       just s ⇀⟦ SLOT ⟧ (record s { FFDState = ffds' ; Ledger = constructLedger ebs } , EMPTY)

  Ftch : ∀ {l} →
       ────────────────────────────────────
       just s ⇀⟦ FTCH-LDG ⟧ (s , FTCH-LDG l)

  -- Base chain

  Base₁ : ∀ {bs bs' eb txs} → let open LeiosState s in
       ∙ eb ∈ filterˢ (λ eb → isVote2Certified s eb × eb ∈ᴮ slice L slot 2) (fromList EBs)
       ∙ bs BF.⇀⟦ B.SUBMIT (inj₁ eb) ⟧ (bs' , B.EMPTY)
       ────────────────────────────────────────────────────────────────────────────────────
       just s ⇀⟦ SUBMIT txs ⟧ (record s { MemPool = MemPool ++ txs } , EMPTY)

  Base₂ : ∀ {bs bs' txs} → let open LeiosState s in
       ∙ ∅ˢ ≡ filterˢ (λ eb → isVote2Certified s eb × eb ∈ᴮ slice L slot 2) (fromList EBs)
       ∙ bs BF.⇀⟦ B.SUBMIT (inj₂ txs) ⟧ (bs' , B.EMPTY)
       ────────────────────────────────────────────────────────────────────────────────────
       just s ⇀⟦ SUBMIT txs ⟧ (record s { MemPool = MemPool ++ txs } , EMPTY)

  -- Protocol rules

  IB-Role : let open LeiosState s renaming (MemPool to txs; FFDState to ffds)
                b = GenFFD.ibBody (record { txs = txs })
                h = GenFFD.ibHeader (mkIBHeader slot id π pKey txs)
          in
          ∙ canProduceIB slot pKey (stake s) -- TODO: let π be the corresponding proof
          ∙ FFDAbstract.Send h (just b) FFD.⇀⟦ ffds ⟧ (ffds' , FFDAbstract.SendRes)
          ─────────────────────────────────────────────────────────────────────────
          just s ⇀⟦ SLOT ⟧ (record s { FFDState = ffds' } , EMPTY)

  EB-Role : let open LeiosState s renaming (FFDState to ffds)
                LI = map {F = List} getIBRef $ setToList $ filterˢ (_∈ᴮ slice L slot (Λ + 1)) (fromList IBs)
                LE = map getEBRef $ setToList $ filterˢ (isVote1Certified s) $
                           filterˢ (_∈ᴮ slice L slot (μ + 2)) (fromList EBs)
                h = mkEB slot id π pKey LI LE
          in
          ∙ canProduceEB slot pKey (stake s)
          ∙ FFDAbstract.Send (GenFFD.ebHeader h) nothing FFD.⇀⟦ ffds ⟧ (ffds' , FFDAbstract.SendRes)
          ──────────────────────────────────────────────────────────────────────────────────────────
          just s ⇀⟦ SLOT ⟧ (record s { FFDState = ffds' } , EMPTY)

  V1-Role : let open LeiosState s renaming (FFDState to ffds)
                EBs' = filterˢ (allIBRefsKnown s) $ filterˢ (_∈ᴮ slice L slot (μ + 1)) (fromList EBs)
                votes = map (vote ∘ hash) (setToList EBs')
          in
          ∙ canProduceV1 slot
          ∙ FFDAbstract.Send (GenFFD.vHeader votes) nothing FFD.⇀⟦ ffds ⟧ (ffds' , FFDAbstract.SendRes)
          ─────────────────────────────────────────────────────────────────────────────────────────────
          just s ⇀⟦ SLOT ⟧ (record s { FFDState = ffds' } , EMPTY)

  V2-Role : let open LeiosState s renaming (FFDState to ffds)
                EBs' = filterˢ (vote2Eligible s) $ filterˢ (_∈ᴮ slice L slot 1) (fromList EBs)
                votes = map (vote ∘ hash) (setToList EBs')
          in
          ∙ canProduceV2 slot
          ∙ FFDAbstract.Send (GenFFD.vHeader votes) nothing FFD.⇀⟦ ffds ⟧ (ffds' , FFDAbstract.SendRes)
          ─────────────────────────────────────────────────────────────────────────────────────────────
          just s ⇀⟦ SLOT ⟧ (record s { FFDState = ffds' } , EMPTY)
