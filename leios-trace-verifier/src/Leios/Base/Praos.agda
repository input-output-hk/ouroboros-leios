{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (_⊗_)
open import Leios.Abstract
open import Leios.VRF

open import CategoricalCrypto hiding (id; _∘_)
open import CategoricalCrypto.Machine.Trace using (Checker; Checkable; Step; step)
import CategoricalCrypto.Machine.Trace as MT

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

  -- The blocks the node mints in the round that absorbs 'bs': it ticks to
  -- the next slot and mints there if it leads.
  mintedIn : NodeState → List Block → List Block × LocalState
  mintedIn s bs = makeBlock (suc (s .clock)) (payload (s .pending)) (processMsgs bs (s .ls))

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
    -- Leios is about to leave when it asks (see 'Deliver').  Leios keeps its
    -- base chain oldest first, with the tip last, and Praos the other way
    -- round, so the chain is reversed.
    FtchLdg :
      WithState s
      receive L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ FTCH-LDG
      return just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ
        BASE-LDG (reverse (map payloadOf (readChain (s .clock) (s .ls)))))
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
      let (out , ls′) = mintedIn s bs
      in
      WithState s
      receive ϵ ⊗R ↑ᵢ bs
      return just (ϵ ⊗R ↑ₒ out)
      newState record s { ls = ls′ ; clock = suc (s .clock) }

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

  -- Every input steps, in one way only.
  opaque
    unfolding dropAdv

    node-step : ∀ s i → Step node⁻ s i
    node-step _ (inj₁ _)                = step (just (inj₁ _)) _ Deliver
    node-step _ (inj₂ (INIT _))         = step (just (inj₂ _)) _ Init
    node-step _ (inj₂ (SUBMIT _))       = step nothing _ Submit
    node-step _ (inj₂ FTCH-LDG)         = step (just (inj₂ _)) _ FtchLdg
    node-step _ (inj₂ FTCH-SLOT)        = step (just (inj₂ _)) _ FtchSlot

  -- The node's trace checker.  The node is deterministic, so a hint picks
  -- no step; it is what the log observes of the step, and the checker
  -- rejects a step the log observes otherwise.  The log records the blocks
  -- the node mints, as 'observe' sees them, and its selected chain after the
  -- round, as 'observeTip' sees it, and nothing of its other steps: the hint
  -- of a delivery round is its slot with these two, and the hint of every
  -- other step is 'nothing'.  A log that does not record the selected chain
  -- observes it as '⊤'.
  module Check {Obs TipObs : Type} ⦃ DecEq-Obs : DecEq Obs ⦄ ⦃ DecEq-TipObs : DecEq TipObs ⦄
               (observe : Block → Obs) (observeTip : List Block → TipObs) where

    NodeHint : Type
    NodeHint = Maybe (ℕ × List Obs × TipObs)

    opaque
      unfolding dropAdv

      -- What the log observes of the step of the node in state 's' on 'i'.
      hintAt : NodeState → MT.Input node⁻ → NodeHint
      hintAt s (inj₁ bs) =
        let (out , ls′) = mintedIn s bs
            sl          = suc (s .clock)
        in just (sl , map observe out , observeTip (readChain sl ls′))
      hintAt _ (inj₂ _)  = nothing

    nodeᶜ : Checker node⁻
    nodeᶜ = record
      { Hint      = NodeHint
      ; hintOf    = λ {s} {i} _ → hintAt s i
      ; Err       = λ h i s → hintAt s i ≢ h
      ; checkStep = λ h i s → case hintAt s i ≟ h of λ where
          (yes eq) → inj₂ (node-step s i , eq)
          (no neq) → inj₁ neq
      }

    -- An error refutes the step, since the hint of a step is fixed by its
    -- state and input.
    nodeᶜ-refute : ∀ {h i s} → Checkable.Err nodeᶜ h i s
                 → ¬ Checkable.StepWith nodeᶜ h s i
    nodeᶜ-refute neq (_ , eq) = neq eq

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
