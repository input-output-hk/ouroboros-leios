{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id)
open import Leios.FFD
open import Leios.SpecStructure

module Leios.Protocol {n} (⋯ : SpecStructure n) (let open SpecStructure ⋯) (SlotUpkeep : Type) where

open BaseAbstract B' using (Cert; V-chkCerts; VTy; initSlot)
open GenFFD

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

record LeiosState : Type where
  field V           : VTy
        SD          : StakeDistr
        FFDState    : FFD.State
        Ledger      : List Tx
        ToPropose   : List Tx
        IBs         : List InputBlock
        EBs         : List EndorserBlock
        Vs          : List (List Vote)
        slot        : ℕ
        IBHeaders   : List IBHeader
        IBBodies    : List IBBody
        Upkeep      : ℙ SlotUpkeep
        BaseState   : B.State
        votingState : VotingState

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

  constructLedger : List RankingBlock → List Tx
  constructLedger = L.concat ∘ L.map (T.mergeThese L._++_ ∘ T.map₁ lookupTxs)

  needsUpkeep : SlotUpkeep → Set
  needsUpkeep = _∉ Upkeep

addUpkeep : LeiosState → SlotUpkeep → LeiosState
addUpkeep s u = let open LeiosState s in record s { Upkeep = Upkeep ∪ ❴ u ❵ }
{-# INJECTIVE_FOR_INFERENCE addUpkeep #-}

initLeiosState : VTy → StakeDistr → B.State → LeiosState
initLeiosState V SD bs = record
  { V           = V
  ; SD          = SD
  ; FFDState    = FFD.initFFDState
  ; Ledger      = []
  ; ToPropose   = []
  ; IBs         = []
  ; EBs         = []
  ; Vs          = []
  ; slot        = initSlot V
  ; IBHeaders   = []
  ; IBBodies    = []
  ; Upkeep      = ∅
  ; BaseState   = bs
  ; votingState = initVotingState
  }

-- some predicates about EBs
module _ (s : LeiosState) (eb : EndorserBlock) where
  open EndorserBlockOSig eb
  open LeiosState s

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
