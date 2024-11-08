-- {-# OPTIONS --safe #-}

open import Leios.Prelude
open import Leios.Abstract
open import Leios.FFD
open import Leios.VRF

import Leios.Base
import Leios.Blocks
import Leios.KeyRegistration

import Data.List.Relation.Unary.Any as L

module Leios.SimpleSpec (a : LeiosAbstract) (let open LeiosAbstract a) (let open Leios.Blocks a)
  ⦃ IsBlock-Vote : IsBlock (List Vote) ⦄
  ⦃ Hashable-IBHeaderOSig : ∀ {b} → Hashable (IBHeaderOSig b) Hash ⦄
  ⦃ Hashable-PreEndorserBlock : Hashable PreEndorserBlock Hash ⦄
  (id : PoolID) (pKey : PrivKey) (FFD' : FFDAbstract.Functionality ffdAbstract)
  (vrf' : LeiosVRF a) (let open LeiosVRF vrf') (pubKey : PubKey)
  (let open Leios.Base a) (B' : BaseAbstract) (BF : BaseAbstract.Functionality B')
  (let open Leios.KeyRegistration a vrf') (K' : KeyRegistrationAbstract) (KF : KeyRegistrationAbstract.Functionality K') where

module B   = BaseAbstract B'
module K   = KeyRegistrationAbstract K'
module FFD = FFDAbstract.Functionality FFD' using (State)

open BaseAbstract.Functionality BF renaming (_⇀⟦_⟧_ to _⇀⟦_⟧ᴮ_)
open KeyRegistrationAbstract.Functionality KF renaming (_⇀⟦_⟧_ to _⇀⟦_⟧ᴷ_)
open FFDAbstract ffdAbstract
open FFDAbstract.Functionality FFD' renaming (stepRel to _⇀⟦_⟧ᴺ_)

-- High level structure:


--                                      (simple) Leios
--                                        /         |
-- +-------------------------------------+          |
-- | Header Diffusion     Body Diffusion |          |
-- +-------------------------------------+       Base Protocol
--                                        \      /
--                                        Network

postulate VTy : Type
          initSlot : VTy → ℕ
          initFFDState : FFD.State

data LeiosInput : Type where
  INIT     : VTy → LeiosInput
  SUBMIT   : EndorserBlock ⊎ List Tx → LeiosInput
  SLOT     : LeiosInput
  FTCH-LDG : LeiosInput

data LeiosOutput : Type where
  FTCH-LDG : List Tx → LeiosOutput
  EMPTY    : LeiosOutput

record LeiosState : Type where
  field V         : VTy
        SD        : StakeDistr
        FFDState  : FFD.State
        Ledger    : List Tx
        ToPropose : List Tx
        IBs       : List InputBlock
        EBs       : List EndorserBlock
        Vs        : List (List Vote)
        slot      : ℕ
        IBHeaders : List IBHeader
        IBBodies  : List IBBody

  lookupEB : EBRef → Maybe EndorserBlock
  lookupEB r = find (λ b → getEBRef b ≟ r) EBs

  lookupIB : IBRef → Maybe InputBlock
  lookupIB r = find (λ b → getIBRef b ≟ r) IBs

  lookupTxs : EndorserBlock → List Tx
  lookupTxs eb = do
    eb′ ← mapMaybe lookupEB $ ebRefs eb
    ib  ← mapMaybe lookupIB $ ibRefs eb′
    txs $ body ib
    where open EndorserBlockOSig
          open IBBody
          open InputBlock

  constructLedger : List EndorserBlock → List Tx
  constructLedger = concatMap lookupTxs

initLeiosState : VTy → StakeDistr → LeiosState
initLeiosState V SD = record
  { V         = V
  ; SD        = SD
  ; FFDState  = initFFDState
  ; Ledger    = []
  ; ToPropose = []
  ; IBs       = []
  ; EBs       = []
  ; Vs        = []
  ; slot      = initSlot V
  ; IBHeaders = []
  ; IBBodies  = []
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


module _ (s : LeiosState) where

  open LeiosState s
  open GenFFD hiding (Header; Body)

  upd : Header ⊎ Body → LeiosState
  upd (inj₁ (ebHeader eb)) = record s { EBs = eb ∷ EBs }
  upd (inj₁ (vHeader vs)) = record s { Vs = vs ∷ Vs }
  upd (inj₁ (ibHeader h)) with L.any? (matchIB? h) IBBodies
  ... | yes p =
    record s
      { IBs = record { header = h ; body = L.lookup p } ∷ IBs
      ; IBBodies = IBBodies L.─ p
      }
  ... | no _ =
    record s
      { IBHeaders = h ∷ IBHeaders
      }
  upd (inj₂ (ibBody b)) with L.any? (flip matchIB? b) IBHeaders
  ... | yes p =
    record s
      { IBs = record { header = L.lookup p ; body = b } ∷ IBs
      ; IBHeaders = IBHeaders L.─ p }
  ... | no _ =
    record s
      { IBBodies = b ∷ IBBodies
      }

_↑_ : LeiosState → List (Header ⊎ Body) → LeiosState
_↑_ = foldr (flip upd)

postulate
  V_chkCerts : List PubKey → EndorserBlock × B.Cert → Type

data _⇀⟦_⟧_ : Maybe LeiosState → LeiosInput → LeiosState × LeiosOutput → Type where

  -- Initialization

  Init : ∀ {V bs bs' SD ks ks' pk pks} →
       ∙ ks ⇀⟦ K.INIT pk ⟧ᴷ (ks' , K.PUBKEYS pks) -- create & register the IB/EB lottery and voting keys with key reg
       ∙ bs ⇀⟦ B.INIT (V_chkCerts pks) ⟧ᴮ (bs' , B.STAKE SD)
       ───────────────────────────────────────────────────────
       nothing ⇀⟦ INIT V ⟧ (initLeiosState V SD , EMPTY)

  -- Network and Ledger

  -- fix: we need to do Slot before every other SLOT transition
  Slot : ∀ {bs bs' msgs ebs} → let open LeiosState s renaming (FFDState to ffds) in
       ∙ bs ⇀⟦ B.FTCH-LDG ⟧ᴮ (bs' , B.BASE-LDG ebs)
       ∙ FFDAbstract.Fetch ⇀⟦ ffds ⟧ᴺ (ffds' , FFDAbstract.FetchRes msgs)
       ──────────────────────────────────────────────────────────────────────────────────────────────
       just s ⇀⟦ SLOT ⟧ (record s { FFDState = ffds' ; Ledger = constructLedger ebs } ↑ msgs , EMPTY)

  Ftch : let open LeiosState s in
       ──────────────────────────────────────────
       just s ⇀⟦ FTCH-LDG ⟧ (s , FTCH-LDG Ledger)

  -- Base chain
  --
  -- Note: Submitted data to the base chain is only taken into account
  --       if the party submitting is the block producer on the base chain
  --       for the given slot

  Base₁ : ∀ {txs} → let open LeiosState s in
        ────────────────────────────────────────────────────────────────────
        just s ⇀⟦ SUBMIT (inj₂ txs) ⟧ (record s { ToPropose = txs } , EMPTY)

  Base₂a : ∀ {bs bs' eb} → let open LeiosState s in
         ∙ eb ∈ filterˢ (λ eb → isVote2Certified s eb × eb ∈ᴮ slice L slot 2) (fromList EBs)
         ∙ bs ⇀⟦ B.SUBMIT (inj₁ eb) ⟧ᴮ (bs' , B.EMPTY)
         ────────────────────────────────────────────────────────────────────────────────────
         just s ⇀⟦ SUBMIT (inj₁ eb) ⟧ (s , EMPTY)

  Base₂b : ∀ {bs bs'} → let open LeiosState s renaming (ToPropose to txs) in
         ∙ ∅ ≡ filterˢ (λ eb → isVote2Certified s eb × eb ∈ᴮ slice L slot 2) (fromList EBs)
         ∙ bs ⇀⟦ B.SUBMIT (inj₂ txs) ⟧ᴮ (bs' , B.EMPTY)
         ────────────────────────────────────────────────────────────────────────────────────
         just s ⇀⟦ SUBMIT (inj₂ txs) ⟧ (s , EMPTY)

  -- Protocol rules

  IB-Role : let open LeiosState s renaming (ToPropose to txs; FFDState to ffds)
                b = GenFFD.ibBody (record { txs = txs })
                h = GenFFD.ibHeader (mkIBHeader slot id π pKey txs)
          in
          ∙ canProduceIB slot pKey (stake s) -- TODO: let π be the corresponding proof
          ∙ FFDAbstract.Send h (just b) ⇀⟦ ffds ⟧ᴺ (ffds' , FFDAbstract.SendRes)
          ──────────────────────────────────────────────────────────────────────
          just s ⇀⟦ SLOT ⟧ (record s { FFDState = ffds' } , EMPTY)

  EB-Role : let open LeiosState s renaming (FFDState to ffds)
                LI = map {F = List} getIBRef $ setToList $ filterˢ (_∈ᴮ slice L slot (Λ + 1)) (fromList IBs)
                LE = map getEBRef $ setToList $ filterˢ (isVote1Certified s) $
                           filterˢ (_∈ᴮ slice L slot (μ + 2)) (fromList EBs)
                h = mkEB slot id π pKey LI LE
          in
          ∙ canProduceEB slot pKey (stake s)
          ∙ FFDAbstract.Send (GenFFD.ebHeader h) nothing ⇀⟦ ffds ⟧ᴺ (ffds' , FFDAbstract.SendRes)
          ───────────────────────────────────────────────────────────────────────────────────────
          just s ⇀⟦ SLOT ⟧ (record s { FFDState = ffds' } , EMPTY)

  V1-Role : let open LeiosState s renaming (FFDState to ffds)
                EBs' = filterˢ (allIBRefsKnown s) $ filterˢ (_∈ᴮ slice L slot (μ + 1)) (fromList EBs)
                votes = map (vote ∘ hash) (setToList EBs')
          in
          ∙ canProduceV1 slot
          ∙ FFDAbstract.Send (GenFFD.vHeader votes) nothing ⇀⟦ ffds ⟧ᴺ (ffds' , FFDAbstract.SendRes)
          ──────────────────────────────────────────────────────────────────────────────────────────
          just s ⇀⟦ SLOT ⟧ (record s { FFDState = ffds' } , EMPTY)

  V2-Role : let open LeiosState s renaming (FFDState to ffds)
                EBs' = filterˢ (vote2Eligible s) $ filterˢ (_∈ᴮ slice L slot 1) (fromList EBs)
                votes = map (vote ∘ hash) (setToList EBs')
          in
          ∙ canProduceV2 slot
          ∙ FFDAbstract.Send (GenFFD.vHeader votes) nothing ⇀⟦ ffds ⟧ᴺ (ffds' , FFDAbstract.SendRes)
          ──────────────────────────────────────────────────────────────────────────────────────────
          just s ⇀⟦ SLOT ⟧ (record s { FFDState = ffds' } , EMPTY)
