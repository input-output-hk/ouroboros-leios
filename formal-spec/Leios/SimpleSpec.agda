{-# OPTIONS --safe #-}

open import Leios.Prelude
open import Leios.Abstract
open import Leios.FFD
open import Leios.VRF
import Leios.Voting

import Leios.Base
import Leios.Blocks
import Leios.KeyRegistration

import Data.List as L
import Data.List.Relation.Unary.Any as A

module Leios.SimpleSpec (a : LeiosAbstract) (let open LeiosAbstract a) (let open Leios.Blocks a)
  ⦃ IsBlock-Vote : IsBlock (List Vote) ⦄
  ⦃ Hashable-IBHeaderOSig : ∀ {b} → Hashable (IBHeaderOSig b) Hash ⦄
  ⦃ Hashable-PreEndorserBlock : Hashable PreEndorserBlock Hash ⦄
  (id : PoolID) (FFD' : FFDAbstract.Functionality ffdAbstract)
  (vrf' : LeiosVRF a) (let open LeiosVRF vrf')
  (sk-IB sk-EB sk-V : PrivKey)
  (pk-IB pk-EB pk-V : PubKey)
  (let open Leios.Base a vrf') (B' : BaseAbstract) (BF : BaseAbstract.Functionality B')
  (initBaseState : BaseAbstract.Functionality.State BF)
  (let open Leios.KeyRegistration a vrf') (K' : KeyRegistrationAbstract) (KF : KeyRegistrationAbstract.Functionality K') where

module B   = BaseAbstract.Functionality BF
module K   = KeyRegistrationAbstract.Functionality KF
module FFD = FFDAbstract.Functionality FFD'

open BaseAbstract B' using (Cert; V-chkCerts; VTy; initSlot)
open GenFFD

filter : {A : Set} → (P : A → Type) ⦃ _ : P ⁇¹ ⦄ → List A → List A
filter P = L.filter ¿ P ¿¹

instance
  IsSet-List : {A : Set} → IsSet (List A) A
  IsSet-List .toSet A = fromList A

-- High level structure:


--                                      (simple) Leios
--                                        /         |
-- +-------------------------------------+          |
-- | Header Diffusion     Body Diffusion |          |
-- +-------------------------------------+       Base Protocol
--                                        \      /
--                                        Network

data LeiosInput : Type where
  INIT     : VTy → LeiosInput
  SUBMIT   : EndorserBlock ⊎ List Tx → LeiosInput
  SLOT     : LeiosInput
  FTCH-LDG : LeiosInput

data LeiosOutput : Type where
  FTCH-LDG : List Tx → LeiosOutput
  EMPTY    : LeiosOutput

data SlotUpkeep : Type where
  Base IB-Role EB-Role V1-Role V2-Role : SlotUpkeep

allUpkeep : ℙ SlotUpkeep
allUpkeep = fromList (Base ∷ IB-Role ∷ EB-Role ∷ V1-Role ∷ V2-Role ∷ [])

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
        Upkeep    : ℙ SlotUpkeep
        BaseState : B.State

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

  needsUpkeep : SlotUpkeep → Set
  needsUpkeep = _∈ Upkeep

addUpkeep : LeiosState → SlotUpkeep → LeiosState
addUpkeep s u = let open LeiosState s in record s { Upkeep = Upkeep ∪ ❴ u ❵ }

initLeiosState : VTy → StakeDistr → B.State → LeiosState
initLeiosState V SD bs = record
  { V         = V
  ; SD        = SD
  ; FFDState  = FFD.initFFDState
  ; Ledger    = []
  ; ToPropose = []
  ; IBs       = []
  ; EBs       = []
  ; Vs        = []
  ; slot      = initSlot V
  ; IBHeaders = []
  ; IBBodies  = []
  ; Upkeep    = ∅
  ; BaseState = bs
  }

-- some predicates about EBs
module _ (s : LeiosState) (eb : EndorserBlock) where
  open EndorserBlockOSig eb
  open LeiosState s

  vote2Eligible : Type
  vote2Eligible = length ebRefs ≥ lengthˢ candidateEBs / 2 -- should this be `>`?
                × fromList ebRefs ⊆ candidateEBs
    where candidateEBs : ℙ Hash
          candidateEBs = mapˢ getEBRef $ filterˢ (_∈ᴮ slice L slot (μ + 3)) (fromList EBs)

  allIBRefsKnown : Type
  allIBRefsKnown = ∀[ ref ∈ fromList ibRefs ] ref ∈ˡ map getIBRef IBs

stake : LeiosState → ℕ
stake record { SD = SD } = case lookupᵐ? SD id of λ where
  (just s) → s
  nothing  → 0

module _ (s : LeiosState) where

  open LeiosState s

  upd : Header ⊎ Body → LeiosState
  upd (inj₁ (ebHeader eb)) = record s { EBs = eb ∷ EBs }
  upd (inj₁ (vHeader vs)) = record s { Vs = vs ∷ Vs }
  upd (inj₁ (ibHeader h)) with A.any? (matchIB? h) IBBodies
  ... | yes p =
    record s
      { IBs = record { header = h ; body = A.lookup p } ∷ IBs
      ; IBBodies = IBBodies A.─ p
      }
  ... | no _ =
    record s
      { IBHeaders = h ∷ IBHeaders
      }
  upd (inj₂ (ibBody b)) with A.any? (flip matchIB? b) IBHeaders
  ... | yes p =
    record s
      { IBs = record { header = A.lookup p ; body = b } ∷ IBs
      ; IBHeaders = IBHeaders A.─ p
      }
  ... | no _ =
    record s
      { IBBodies = b ∷ IBBodies
      }

infix 25 _↑_
_↑_ : LeiosState → List (Header ⊎ Body) → LeiosState
_↑_ = foldr (flip upd)

open FFD hiding (_-⟦_/_⟧⇀_)

private variable s      : LeiosState
                 ffds'  : FFD.State
                 π      : VrfPf
                 bs'    : B.State
                 ks ks' : K.State
                 msgs   : List (FFDAbstract.Header ffdAbstract ⊎ FFDAbstract.Body ffdAbstract)
                 eb     : EndorserBlock
                 ebs    : List EndorserBlock
                 txs    : List Tx
                 V      : VTy
                 SD     : StakeDistr
                 pks    : List PubKey

module _ (open Leios.Voting a) (va : VotingAbstract LeiosState) (open VotingAbstract va)
         ⦃ _ : ∀ {vs} {eb} → isVote1Certified vs eb ⁇ ⦄
         ⦃ _ : ∀ {vs} {eb} → isVote2Certified vs eb ⁇ ⦄ where

  data _-⟦_/_⟧⇀_ : Maybe LeiosState → LeiosInput → LeiosOutput → LeiosState → Type where

    -- Initialization

    Init :
         ∙ ks K.-⟦ K.INIT pk-IB pk-EB pk-V / K.PUBKEYS pks ⟧⇀ ks'
         ∙ initBaseState B.-⟦ B.INIT (V-chkCerts pks) / B.STAKE SD ⟧⇀ bs'
         ────────────────────────────────────────────────────────────────
         nothing -⟦ INIT V / EMPTY ⟧⇀ initLeiosState V SD bs'

    -- Network and Ledger

    Slot : let open LeiosState s renaming (FFDState to ffds; BaseState to bs) in
         ∙ Upkeep ≡ᵉ allUpkeep
         ∙ bs B.-⟦ B.FTCH-LDG / B.BASE-LDG ebs ⟧⇀ bs'
         ∙ ffds FFD.-⟦ Fetch / FetchRes msgs ⟧⇀ ffds'
         ───────────────────────────────────────────────────────────────────────
         just s -⟦ SLOT / EMPTY ⟧⇀ record s
             { FFDState = ffds'
             ; Ledger   = constructLedger ebs
             ; slot     = suc slot
             ; Upkeep   = ∅
             } ↑ L.filter isValid? msgs

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
            ∙ bs B.-⟦ B.SUBMIT (inj₁ eb) / B.EMPTY ⟧⇀ bs'
            ───────────────────────────────────────────────────────────────────────
            just s -⟦ SLOT / EMPTY ⟧⇀ addUpkeep record s { BaseState = bs' } Base

    Base₂b  : let open LeiosState s renaming (BaseState to bs) in
            ∙ needsUpkeep Base
            ∙ [] ≡ filter (λ eb → isVote2Certified s eb × eb ∈ᴮ slice L slot 2) EBs
            ∙ bs B.-⟦ B.SUBMIT (inj₂ ToPropose) / B.EMPTY ⟧⇀ bs'
            ───────────────────────────────────────────────────────────────────────
            just s -⟦ SLOT / EMPTY ⟧⇀ addUpkeep s Base

    -- Protocol rules

    IB-Role : let open LeiosState s renaming (FFDState to ffds)
                  b = ibBody (record { txs = ToPropose })
                  h = ibHeader (mkIBHeader slot id π sk-IB ToPropose)
            in
            ∙ needsUpkeep IB-Role
            ∙ canProduceIB slot sk-IB (stake s) π
            ∙ ffds FFD.-⟦ Send h (just b) / SendRes ⟧⇀ ffds'
            ─────────────────────────────────────────────────────────────────────────
            just s -⟦ SLOT / EMPTY ⟧⇀ addUpkeep record s { FFDState = ffds' } IB-Role

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
            just s -⟦ SLOT / EMPTY ⟧⇀ addUpkeep record s { FFDState = ffds' } EB-Role

    V1-Role : let open LeiosState s renaming (FFDState to ffds)
                  EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot (μ + 1)) EBs
                  votes = map (vote sk-V ∘ hash) EBs'
            in
            ∙ needsUpkeep V1-Role
            ∙ canProduceV1 slot sk-V (stake s)
            ∙ ffds FFD.-⟦ Send (vHeader votes) nothing / SendRes ⟧⇀ ffds'
            ─────────────────────────────────────────────────────────────────────────
            just s -⟦ SLOT / EMPTY ⟧⇀ addUpkeep record s { FFDState = ffds' } V1-Role

    V2-Role : let open LeiosState s renaming (FFDState to ffds)
                  EBs' = filter (vote2Eligible s) $ filter (_∈ᴮ slice L slot 1) EBs
                  votes = map (vote sk-V ∘ hash) EBs'
            in
            ∙ needsUpkeep V2-Role
            ∙ canProduceV2 slot sk-V (stake s)
            ∙ ffds FFD.-⟦ Send (vHeader votes) nothing / SendRes ⟧⇀ ffds'
            ─────────────────────────────────────────────────────────────────────────
            just s -⟦ SLOT / EMPTY ⟧⇀ addUpkeep record s { FFDState = ffds' } V2-Role

    -- Note: Base doesn't need a negative rule, since it can always be invoked

    No-IB-Role : let open LeiosState s in
            ∙ needsUpkeep IB-Role
            ∙ ¬ canProduceIB slot sk-IB (stake s) π
            ─────────────────────────────────────────────
            just s -⟦ SLOT / EMPTY ⟧⇀ addUpkeep s IB-Role

    No-EB-Role : let open LeiosState s in
            ∙ needsUpkeep EB-Role
            ∙ ¬ canProduceEB slot sk-EB (stake s) π
            ─────────────────────────────────────────────
            just s -⟦ SLOT / EMPTY ⟧⇀ addUpkeep s EB-Role

    No-V1-Role : let open LeiosState s in
            ∙ needsUpkeep V1-Role
            ∙ ¬ canProduceV1 slot sk-V (stake s)
            ─────────────────────────────────────────────
            just s -⟦ SLOT / EMPTY ⟧⇀ addUpkeep s V1-Role

    No-V2-Role : let open LeiosState s in
            ∙ needsUpkeep V2-Role
            ∙ ¬ canProduceV2 slot sk-V (stake s)
            ─────────────────────────────────────────────
            just s -⟦ SLOT / EMPTY ⟧⇀ addUpkeep s V2-Role
