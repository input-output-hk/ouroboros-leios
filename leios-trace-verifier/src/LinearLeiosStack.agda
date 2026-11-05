{- Module: LinearLeiosStack

   Linear Leios stacked on its base layer, as one machine with one trace
   verifier.

   The machine is the upper half of the deployed node in the spec's
   'Network.Leios' ('ext-spec' over 'spec'), with the base layer in place of
   the network multiplexer below it:

              IO                  Adv
               ↕                   ↕
      ┌────────┴───────────────────┴──┐
      │          LinearLeios          │
      └────↕──────────↕──────────↕────┘
          FFD       BaseIO     VotingC
           │       ┌──┴───┐      │
           id      │ Base │      id                Below
           │       └──↕───┘      │
          FFD    BaseNetwork   VotingC

   so a request of Leios on 'BaseIO' (the ledger after every slot, a ranking
   block to submit) is answered by the base machine, not by the trace.  The
   trace only feeds the base machine the blocks the node receives.

   Its checker is composed from the checkers of the parts along the same
   builders ('CategoricalCrypto.Machine.Trace.Compose'): the spec's Linear
   Leios checker, lifted from 'TestInput's to the machine's inputs, the base
   machine's checker, and 'idᶜ' for the two wires.  A hint names every
   internal step of an input, in order: a step of a wire, of the base
   machine, or of Leios with its 'Action'.  'hintsFor' derives them from the
   Leios action, since the rule fixes where each output goes.
-}

open import Leios.Prelude hiding (id; _⊗_; _>>=_; return)
open import Leios.Config
open import Leios.SpecStructure using (SpecStructure)

open import Prelude.Errors

open import CategoricalCrypto hiding (id; _∘_; eval; Trace)
import CategoricalCrypto as CC
open import CategoricalCrypto.Channel.Selection
import CategoricalCrypto.Machine.Trace as MT
open MT using (Checker; Checkable)
open import CategoricalCrypto.Machine.Trace.Compose
open import Data.List.NonEmpty using (List⁺; _∷_)

module LinearLeiosStack
  (⋯ : SpecStructure) (let open SpecStructure ⋯) (params : Params)
  (BaseM : Machine (BaseAbstract.BaseNetwork B') (BaseAbstract.BaseIO B'))
  (baseᶜ : Checker BaseM)
  -- The hint of the base machine's steps on requests of Leios; a delivery
  -- of blocks names its own (see 'deliver').
  (baseH : Checkable.Hint baseᶜ)
  -- Why the base machine rejects a step with the given hint.
  (baseMsg : Checkable.Hint baseᶜ → String)
  where

open import Leios.Linear.Trace.Verifier ⋯ params as V
  hiding (verifyTrace; Trace; StepWith; Entry; ⟨_,_⟩; ValidTrace; TraceErr)
open Types params
open BaseAbstract B'

------------------------------------------------------------------------------
-- Linear Leios, checked on its inputs

-- Every input of Linear Leios is the image of a 'TestInput'.
opaque
  unfolding _⊗₀_

  decode : (i : MT.Input LinearLeios) → Σ[ m ∈ TestInput ] toRcvType m ≡ i
  decode (inj₁ (inj₁ (inj₁ x))) = inj₁ x , refl
  decode (inj₁ (inj₁ (inj₂ x))) = inj₂ (inj₁ x) , refl
  decode (inj₁ (inj₂ x))        = inj₂ (inj₂ (inj₂ x)) , refl
  decode (inj₂ (inj₁ x))        = inj₂ (inj₂ (inj₁ x)) , refl
  decode (inj₂ (inj₂ ()))

private
  checkL : ∀ a i s → Err-verifyStep a (proj₁ (decode i)) s
         ⊎ Σ[ x ∈ MT.Step LinearLeios s i ] getAction (MT.derivation x) ≡ a
  checkL a i s with decode i
  ... | m , refl = Checkable.checkStep checkable a m s

leiosᶜ : Checker LinearLeios
leiosᶜ = record
  { Hint      = Action
  ; hintOf    = getAction ∘ MT.derivation
  ; Err       = λ a i s → Err-verifyStep a (proj₁ (decode i)) s
  ; checkStep = checkL
  }

------------------------------------------------------------------------------
-- The stack

Below : Machine ((FFD ⊗₀ BaseNetwork) ⊗₀ VotingC) ((FFD ⊗₀ BaseIO) ⊗₀ VotingC)
Below = (CC.id ⊗₁ BaseM) ⊗₁ CC.id

belowᶜ : Checker Below
belowᶜ = (idᶜ ⊗ᶜ baseᶜ) ⊗ᶜ idᶜ

Stack : Machine ((FFD ⊗₀ BaseNetwork) ⊗₀ VotingC) (IO ⊗₀ Adv)
Stack = LinearLeios CC.∘ Below

stackᶜ : Checker Stack
stackᶜ = leiosᶜ ∘ᶜ belowᶜ

-- The hint of one internal step.
H : Type
H = ((⊤ ⊎ Checkable.Hint baseᶜ) ⊎ ⊤) ⊎ Action

ffdᴴ baseᴴ voteᴴ : H
ffdᴴ  = inj₁ (inj₁ (inj₁ tt))
baseᴴ = inj₁ (inj₁ (inj₂ baseH))
voteᴴ = inj₁ (inj₂ tt)

-- A step of the base machine on blocks from the network.
deliverᴴ : Checkable.Hint baseᶜ → H
deliverᴴ = inj₁ ∘ inj₁ ∘ inj₂

leiosᴴ : Action → H
leiosᴴ = inj₂

-- The internal steps of an input on which Leios takes the given action.
-- An input from below passes a wire on its way up; an output goes down a
-- wire, or to the base machine, whose answer to 'FTCH-LDG' Leios takes in
-- with 'Chain' in the slot it has just entered.
hintsFor : Action → List⁺ H
hintsFor a@(EB-Role-Action _ _)   = ffdᴴ ∷ leiosᴴ a ∷ ffdᴴ ∷ []
hintsFor a@(VT-Role-Action _ _ _) = ffdᴴ ∷ leiosᴴ a ∷ voteᴴ ∷ []
hintsFor a@(No-EB-Role-Action _)  = ffdᴴ ∷ leiosᴴ a ∷ []
hintsFor a@(No-VT-Role-Action _)  = ffdᴴ ∷ leiosᴴ a ∷ []
hintsFor a@(Base₁-Action _)       = ffdᴴ ∷ leiosᴴ a ∷ baseᴴ ∷ []
hintsFor a@(Base₂-Action _)       = ffdᴴ ∷ leiosᴴ a ∷ voteᴴ ∷ []
hintsFor a@(Slot-Action n)        = ffdᴴ ∷ leiosᴴ a ∷ baseᴴ ∷ leiosᴴ (Chain-Action (suc n)) ∷ []
hintsFor a@(Cert₁-Action _)       = voteᴴ ∷ leiosᴴ a ∷ baseᴴ ∷ []
hintsFor a@(Cert₂-Action _)       = voteᴴ ∷ leiosᴴ a ∷ baseᴴ ∷ []
hintsFor a@(Cert₃-Action _)       = voteᴴ ∷ leiosᴴ a ∷ voteᴴ ∷ []
hintsFor a@(Mempool-Action _)     = leiosᴴ a ∷ []
hintsFor a@(Fetch-Action _)       = leiosᴴ a ∷ []
-- Not an input of the stack: the base machine supplies the ledger.
hintsFor a@(Chain-Action _)       = leiosᴴ a ∷ []

------------------------------------------------------------------------------
-- Traces

-- The inputs of the stack, flattened as in 'TestInput': from the network
-- below (FFD messages, blocks for the base machine, voting answers) or from
-- the node's environment above.
data StackInput : Type where
  ffdᵢ  : FFDT Out → StackInput
  netᵢ  : List BaseMsg → StackInput
  voteᵢ : VotingT In → StackInput
  ioᵢ   : IOT In → StackInput

toStackInput : StackInput → MT.Input Stack
toStackInput (ffdᵢ i)  = ((ϵ ⊗R) ⊗R) ⊗R ↑ᵢ i
toStackInput (netᵢ bs) = ((L⊗ ϵ) ⊗R) ⊗R ↑ᵢ bs
toStackInput (ioᵢ i)   = L⊗ (ϵ ᵗ¹ ⊗R) ᵗ¹ ↑ᵢ i
toStackInput (voteᵢ i) = (L⊗ ϵ) ⊗R ↑ᵢ i

stack : MT.Checkable Stack toStackInput
stack = record
  { Hint      = Checkable.Hint stackᶜ
  ; hintOf    = Checkable.hintOf stackᶜ
  ; Err       = λ h m → Checkable.Err stackᶜ h (toStackInput m)
  ; checkStep = λ h m → Checkable.checkStep stackᶜ h (toStackInput m)
  }

open MT.Verifier Stack stack public

leiosState : Machine.State Stack → LeiosState
leiosState = proj₂

------------------------------------------------------------------------------
-- Error messages

-- The checker of the two layers side by side, whose loop is 'stackᶜ'.
Layers : Machine (((FFD ⊗₀ BaseNetwork) ⊗₀ VotingC) ⊗₀ ((FFD ⊗₀ BaseIO) ⊗₀ VotingC))
                 ((IO ⊗₀ Adv) ⊗₀ ((FFD ⊗₀ BaseIO) ⊗₀ VotingC))
Layers = modifyStepRel ∘σ (Below ⊗₁ LinearLeios)

layersᶜ : Checker Layers
layersᶜ = reindexᶜ ∘σ ∘σ-back (belowᶜ ⊗ᶜ leiosᶜ)

module _ ⦃ _ : Show Hash ⦄ where

  -- Leios and the base machine reject steps; the wires step on every input.
  layerMsg : ∀ h i s → Checkable.Err layersᶜ h i s → String
  layerMsg (inj₂ a) i s e
    with side {(FFD ⊗₀ BaseNetwork) ⊗₀ VotingC} {(FFD ⊗₀ BaseIO) ⊗₀ VotingC}
              {(FFD ⊗₀ BaseIO) ⊗₀ VotingC} {IO ⊗₀ Adv} {Below} {LinearLeios}
              (app (∘σ {(FFD ⊗₀ BaseNetwork) ⊗₀ VotingC} {(FFD ⊗₀ BaseIO) ⊗₀ VotingC}
                       {IO ⊗₀ Adv} {In}) i)
  ... | inj₂ _ = errorMsg e
  ... | inj₁ _ = "wrong layer for " ◇ actionName a
  layerMsg (inj₁ (inj₁ (inj₂ h))) _ _ _ = baseMsg h
  layerMsg (inj₁ _) _ _ _ = "a wire step was rejected"

  loopMsg : ∀ {hs j s} → TrErr {A = (FFD ⊗₀ BaseNetwork) ⊗₀ VotingC} {B = IO ⊗₀ Adv}
                                {C = (FFD ⊗₀ BaseIO) ⊗₀ VotingC} layersᶜ hs j s → String
  loopMsg (here {h = h} {i = i} {s = s} e) = layerMsg h i s e
  loopMsg (there _ _ e) = loopMsg e
  loopMsg (short _ _)   = "an output is fed back, but no hint is left for its step"
  loopMsg (long _ _)    = "an output leaves the node, but hints are left over"

  traceMsg : ∀ {s es} → TraceErr s es → String
  traceMsg (here e)    = loopMsg e
  traceMsg (there _ e) = traceMsg e

------------------------------------------------------------------------------
-- Running a trace read off a log

-- An input with the action Leios takes on it, a batch of blocks for the base
-- machine with the hint of its step there, or the ranking-block step of the
-- given slot.
data Item : Type where
  entry   : Action → StackInput → Item
  deliver : Checkable.Hint baseᶜ → List BaseMsg → Item
  base    : ℕ → Item

-- The ranking-block step of a slot is 'Base₁' when the tip calls for no
-- certificate, else 'Base₂' answered by 'CERT nothing' (see
-- 'LinearLeiosTrace', which does the same for Leios alone).
baseEntries : LeiosState → ℕ → Trace
baseEntries s n = case certRequest s of λ where
  nothing  → ⟨ hintsFor (Base₁-Action n) , ffdᵢ FFDT.SLOT ⟩ ∷ []
  (just _) → ⟨ hintsFor (Base₂-Action n) , ffdᵢ FFDT.SLOT ⟩
           ∷ ⟨ hintsFor (Cert₁-Action n) , voteᵢ (CERT nothing) ⟩
           ∷ []

toEntry : Action → StackInput → Entry
toEntry a m = ⟨ hintsFor a , m ⟩

-- Verify the items from the given state, returning the final state or the
-- message of the first error.
verifyItems : ⦃ Show Hash ⦄ → Machine.State Stack → List Item → String ⊎ Machine.State Stack
verifyItems s = go s []
  where
    flush : Machine.State Stack → Trace → String ⊎ Machine.State Stack
    flush s es = case verifyTrace s es of λ where
      (inj₁ err)      → inj₁ (traceMsg err)
      (inj₂ (s′ , _)) → inj₂ s′

    -- The entries not yet verified are kept in reverse.
    go : Machine.State Stack → Trace → List Item → String ⊎ Machine.State Stack
    go s pending []                  = flush s (L.reverse pending)
    go s pending (entry a m ∷ items) = go s (toEntry a m ∷ pending) items
    go s pending (deliver h bs ∷ items) = go s (⟨ deliverᴴ h ∷ [] , netᵢ bs ⟩ ∷ pending) items
    go s pending (base n ∷ items)    = case flush s (L.reverse pending) of λ where
      (inj₁ err) → inj₁ err
      (inj₂ s′)  → go s′ (L.reverse (baseEntries (leiosState s′) n)) items
