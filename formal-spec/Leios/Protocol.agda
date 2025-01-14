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
        PubKeys     : List PubKey

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

initLeiosState : VTy → StakeDistr → B.State → List PubKey → LeiosState
initLeiosState V SD bs pks = record
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
  ; PubKeys     = pks
  }

stake' : PoolID → LeiosState → ℕ
stake' pid s = let open LeiosState s in
  case lookupᵐ? SD pid of λ where
    (just s) → s
    nothing  → 0

stake'' : PubKey → LeiosState → ℕ
stake'' pk = stake' (poolID pk)

stake : LeiosState → ℕ
stake = stake' id

lookupPubKeyAndStake : ∀ {B} → ⦃ _ : IsBlock B ⦄ → LeiosState → B → Maybe (PubKey × ℕ)
lookupPubKeyAndStake s b =
  L.head $
    L.map (λ pk → (pk , stake'' pk s)) $
      L.filter ((producerID b ≟_) ∘ poolID) (LeiosState.PubKeys s)

module _ (s : LeiosState)  where

  record ibHeaderValid (h : IBHeader) (pk : PubKey) (st : ℕ) : Type where
    field lotteryPfValid : verify pk (slotNumber h) st (lotteryPf h)
          signatureValid : verifySig pk (signature h)

  record ibBodyValid (b : IBBody) : Type where

  ibHeaderValid? : (h : IBHeader) (pk : PubKey) (st : ℕ) → Dec (ibHeaderValid h pk st)
  ibHeaderValid? h pk st
    with verify? pk (slotNumber h) st (lotteryPf h)
  ... | no ¬p = no (¬p ∘ ibHeaderValid.lotteryPfValid)
  ... | yes p
    with verifySig? pk (signature h)
  ... | yes q = yes (record { lotteryPfValid = p ; signatureValid = q })
  ... | no ¬q = no (¬q ∘ ibHeaderValid.signatureValid)

  ibBodyValid? : (b : IBBody) → Dec (ibBodyValid b)
  ibBodyValid? _ = yes record {}

  ibValid : InputBlock → Type
  ibValid record { header = h ; body = b }
    with lookupPubKeyAndStake s h
  ... | just (pk , pid) = ibHeaderValid h pk (stake'' pk s) × ibBodyValid b
  ... | nothing = ⊥

  ibValid? : (ib : InputBlock) → Dec (ibValid ib)
  ibValid? record { header = h ; body = b }
    with lookupPubKeyAndStake s h
  ... | just (pk , pid) = ibHeaderValid? h pk (stake'' pk s) ×-dec ibBodyValid? b
  ... | nothing = no λ x → x

  record ebValid (eb : EndorserBlock) (pk : PubKey) (st : ℕ) : Type where
    field lotteryPfValid : verify pk (slotNumber eb) st (lotteryPf eb)
          signatureValid : verifySig pk (signature eb)
    -- TODO
    -- ibRefsValid : ?
    -- ebRefsValid : ?

  ebValid? : (eb : EndorserBlock) (pk : PubKey) (st : ℕ) → Dec (ebValid eb pk st)
  ebValid? h pk st
    with verify? pk (slotNumber h) st (lotteryPf h)
  ... | no ¬p = no (¬p ∘ ebValid.lotteryPfValid)
  ... | yes p
    with verifySig? pk (signature h)
  ... | yes q = yes (record { lotteryPfValid = p ; signatureValid = q })
  ... | no ¬q = no (¬q ∘ ebValid.signatureValid)

  -- TODO
  record vsValid (vs : List Vote) : Type where

  vsValid? : (vs : List Vote) → Dec (vsValid vs)
  vsValid? _ = yes record {}

  headerValid : Header → Type
  headerValid (ibHeader h)
    with lookupPubKeyAndStake s h
  ... | just (pk , pid) = ibHeaderValid h pk (stake'' pk s)
  ... | nothing = ⊥
  headerValid (ebHeader h)
    with lookupPubKeyAndStake s h
  ... | just (pk , pid) = ebValid h pk (stake'' pk s)
  ... | nothing = ⊥
  headerValid (vHeader h)  = vsValid h

  headerValid? : (h : Header) → Dec (headerValid h)
  headerValid? (ibHeader h)
    with lookupPubKeyAndStake s h
  ... | just (pk , pid) = ibHeaderValid? h pk (stake'' pk s)
  ... | nothing = no λ x → x
  headerValid? (ebHeader h)
    with lookupPubKeyAndStake s h
  ... | just (pk , pid) = ebValid? h pk (stake'' pk s)
  ... | nothing = no λ x → x
  headerValid? (vHeader h) = vsValid? h

  bodyValid : Body → Type
  bodyValid (ibBody b) = ibBodyValid b

  bodyValid? : (b : Body) → Dec (bodyValid b)
  bodyValid? (ibBody b) = ibBodyValid? b

  isValid : Header ⊎ Body → Type
  isValid (inj₁ h) = headerValid h
  isValid (inj₂ b) = bodyValid b

  isValid? : ∀ (x : Header ⊎ Body) → Dec (isValid x)
  isValid? (inj₁ h) = headerValid? h
  isValid? (inj₂ b) = bodyValid? b

-- some predicates about EBs
module _ (s : LeiosState) (eb : EndorserBlock) where
  open EndorserBlockOSig eb
  open LeiosState s

  allIBRefsKnown : Type
  allIBRefsKnown = ∀[ ref ∈ fromList ibRefs ] ref ∈ˡ map getIBRef IBs

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
