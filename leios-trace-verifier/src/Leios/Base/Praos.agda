{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (_⊗_)
open import Leios.Abstract
open import Leios.VRF

open import CategoricalCrypto hiding (id; _∘_)
open import CategoricalCrypto.Machine.Trace using (Checker; Step; step)

import Blockchain.IsBlockchain as IsBC

module Leios.Base.Praos
  (a    : LeiosAbstract) (open LeiosAbstract a)
  (vrf' : LeiosVRF a   ) (open LeiosVRF vrf'  )
  where

open import Leios.Base a vrf'
open import Leios.Blocks a using (EndorserBlock)

-- Interface to a Praos node implementation (ouroboros-praos-formal-spec with
-- Txs := RankingBlock), reduced to the honest-local fragment the wrapper
-- needs: the block-tree state and the delivery/minting/read functions, with
-- the node's identity and leader schedule already fixed inside makeBlock
-- (cf. processMsgsʰ, makeBlockʰ, bestChain in Protocol.Semantics).
record PraosAbstract : Type₁ where
  field Block           : Type
        ⦃ DecEq-Block ⦄ : DecEq Block
        LocalState      : Type
        initState       : LocalState
        processMsgs     : List Block → LocalState → LocalState
        makeBlock       : ℕ → RankingBlock → LocalState → List Block × LocalState
        readChain       : ℕ → LocalState → List Block
        payloadOf       : Block → RankingBlock

-- An RB carrying neither transactions nor an announcement.
emptyRB : RankingBlock
emptyRB = record { announcedEB = nothing ; txsOrEbCert = inj₁ [] }

module Node
  (praos      : PraosAbstract) (open PraosAbstract praos)
  (Cert VTy   : Type)
  (initSlot   : VTy → ℕ)
  (V-chkCerts : List PubKey → EndorserBlock × Cert → Bool)
  (stake₀     : StakeDistr)
  where

  B' : BaseAbstract
  B' = record
    { Cert          = Cert
    ; VTy           = VTy
    ; initSlot      = initSlot
    ; V-chkCerts    = V-chkCerts
    ; BaseAdv       = I
    ; BaseMsg       = Block
    ; DecEq-BaseMsg = DecEq-Block
    }

  open BaseAbstract B' hiding (Cert; VTy; initSlot; V-chkCerts)

  record NodeState : Type where
    field ls        : LocalState
          clock     : ℕ
          pending   : Maybe RankingBlock
          checkCert : Maybe (EndorserBlock × Cert → Bool)

  open NodeState

  initNodeState : NodeState
  initNodeState = record
    { ls = initState ; clock = 0 ; pending = nothing ; checkCert = nothing }

  payload : Maybe RankingBlock → RankingBlock
  payload nothing   = emptyRB
  payload (just rb) = rb

  private variable s : NodeState

  data WithState_receive_return_newState_ :
       MachineType BaseNetwork (BaseIO ⊗₀ BaseAdv) NodeState where

    Init : ∀ {chk} →
      WithState s
      receive L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ INIT chk
      return just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ STAKE stake₀)
      newState record s { checkCert = just chk }

    -- No acknowledgement: Linear Leios has no rule that consumes 'EMPTY',
    -- so stacked on this node (see 'node⁻') it could not take a step that
    -- submits.
    Submit : ∀ {rb} →
      WithState s
      receive L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ SUBMIT rb
      return nothing
      newState record s { pending = just rb }

    -- The chain up to the slot of the last 'Deliver', which is the slot
    -- Leios is about to leave when it asks (see 'Deliver').
    FtchLdg :
      WithState s
      receive L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ FTCH-LDG
      return just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ
        BASE-LDG (map payloadOf (readChain (s .clock) (s .ls))))
      newState s

    FtchSlot :
      WithState s
      receive L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ FTCH-SLOT
      return just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ SLOT (s .clock))
      newState s

    -- One DD round, localized: absorb the delivery batch, tick, mint if the
    -- slot is won. The diffusion answer is synchronous (cf. NetTranslate).
    -- The round of slot 'suc clock' closes that slot, after Leios submitted
    -- its block for it, so the clock trails the Leios slot by one.
    Deliver : ∀ {bs} →
      let ls₁         = processMsgs bs (s .ls)
          sl          = suc (s .clock)
          (out , ls₂) = makeBlock sl (payload (s .pending)) ls₁
      in
      WithState s
      receive ϵ ⊗R ↑ᵢ bs
      return just (ϵ ⊗R ↑ₒ out)
      newState record s { ls = ls₂ ; clock = sl }

  node : Machine BaseNetwork (BaseIO ⊗₀ BaseAdv)
  node .Machine.State   = _
  node .Machine.stepRel = WithState_receive_return_newState_

  -- The node without its adversary port, which is the empty channel 'I',
  -- so that it fits under Linear Leios's 'BaseIO' port.
  opaque
    unfolding _⊗₀_

    dropAdv : ∀ {m} → BaseNetwork ⊗₀ BaseIO ᵀ [ m ]⇒[ m ] BaseNetwork ⊗₀ (BaseIO ⊗₀ BaseAdv) ᵀ
    dropAdv {In}  = mk⇒ [ inj₁ , inj₂ ∘ inj₁ ]′
    dropAdv {Out} = mk⇒ [ inj₁ , inj₂ ∘ inj₁ ]′

  node⁻ : Machine BaseNetwork BaseIO
  node⁻ = modifyStepRel dropAdv node

  -- Every input steps, in one way only, so the checker needs no hint and
  -- never fails.
  opaque
    unfolding dropAdv

    node-step : ∀ s i → Step node⁻ s i
    node-step _ (inj₁ _)                = step (just (inj₁ _)) _ Deliver
    node-step _ (inj₂ (INIT _))         = step (just (inj₂ _)) _ Init
    node-step _ (inj₂ (SUBMIT _))       = step nothing _ Submit
    node-step _ (inj₂ FTCH-LDG)         = step (just (inj₂ _)) _ FtchLdg
    node-step _ (inj₂ FTCH-SLOT)        = step (just (inj₂ _)) _ FtchSlot

  nodeᶜ : Checker node⁻
  nodeᶜ = record
    { Hint      = ⊤
    ; hintOf    = λ _ → tt
    ; Err       = λ _ _ _ → ⊥
    ; checkStep = λ _ i s → inj₂ (node-step s i , refl)
    }

  -- producer and slotOf are parameters until RankingBlock determines its
  -- Praos header (see docs/praos-base-machine-sketch.md).
  module Assemble
    (nParties : ℕ)
    (producer : RankingBlock → Fin nParties)
    (slotOf   : RankingBlock → ℕ)
    where

    open IsBC (Fin nParties)

    private
      Query = BlockChainInfo RankingBlock

      queryI' : Query → Channel.inType (Machine.machine-channel node)
      queryI' Chain = L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ FTCH-LDG
      queryI' Slot  = L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ FTCH-SLOT

      queryO' : ∀ {q} → bciQueryType q → Channel.outType (Machine.machine-channel node)
      queryO' {Chain} c  = L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ BASE-LDG c
      queryO' {Slot}  sl = L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ SLOT sl

    -- The channel selections in the step indices only reduce to constructor
    -- form once _⊗₀_ is unfolded (cf. Leios.Linear.Trace.Verifier).
    opaque
      unfolding _⊗₀_

      correctness' : ∀ {q s response' s'}
        → WithState s receive queryI' q return response' newState s'
        → ∃ λ response → response' ≡ just (queryO' {q} response)
      correctness' {Chain} FtchLdg  = _ , refl
      correctness' {Slot}  FtchSlot = _ , refl

      completeness' : ∀ {q s}
        → ∃ λ response' → ∃ λ s'
        → WithState s receive queryI' q return just response' newState s'
      completeness' {Chain} = _ , _ , FtchLdg
      completeness' {Slot}  = _ , _ , FtchSlot

    isConstrained : IsConstrained node (bciQueryType {Block = RankingBlock})
    isConstrained = record
      { queryI       = queryI'
      ; queryO       = λ {q} → queryO' {q}
      ; correctness  = λ {q} → correctness' {q}
      ; completeness = λ {q} {s} → completeness' {q} {s}
      }

    opaque
      unfolding _⊗₀_

      isPure : IsPure isConstrained
      isPure Chain FtchLdg  = refl
      isPure Slot  FtchSlot = refl

    praosBase : BaseMachine
    praosBase = record
      { n             = nParties
      ; m             = node
      ; is-blockchain = record
          { isConstrained = isConstrained
          ; isPure        = isPure
          ; producer      = producer
          ; slotOf        = slotOf
          }
      }
