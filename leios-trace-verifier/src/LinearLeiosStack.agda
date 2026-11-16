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

   Beside it runs the validation functionality ('Leios.Ledger.Validation'),
   which answers whether an EB is 'Valid', 'Invalid', 'InProgress' or
   'Unknown':

      ┌───────────────────────────────┐   ┌────────────┐
      │      LinearLeios ∘ Below      │ ⊗ │ validation │
      └───────────────────────────────┘   └────────────┘

   The pinned spec's Linear Leios has no port to it: its vote rule asks the
   static oracle 'isValidityChecked' instead.  So the log stands in for
   Leios on the validation port: it submits the EBs the node acquires,
   advances the clock with every slot, and queries the EB of every vote,
   which must be 'Valid', and of every abstention the node puts down to late
   validation, which must still be in progress.  Once the spec's Linear
   Leios has the port, the validation machine moves under it, into 'Below',
   and these queries become Leios's own.
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

open import Leios.Ledger.Validation

module LinearLeiosStack
  (⋯ : SpecStructure) (let open SpecStructure ⋯) (params : Params)
  (BaseM : Machine (BaseAbstract.BaseNetwork B') (BaseAbstract.BaseIO B'))
  (baseᶜ : Checker BaseM)
  -- The hint of the base machine's steps on requests of Leios; a delivery
  -- of blocks names its own (see 'deliver').
  (baseH : Checkable.Hint baseᶜ)
  -- Why the base machine rejects a step with the given hint.
  (baseMsg : Checkable.Hint baseᶜ → String)
  -- The ledger that validates EBs, and how long validation may stay in
  -- progress after an EB is submitted.
  (valBackend : Backend (SpecStructure.EndorserBlock ⋯)) (Δ : ℕ)
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

Core : Machine ((FFD ⊗₀ BaseNetwork) ⊗₀ VotingC) (IO ⊗₀ Adv)
Core = LinearLeios CC.∘ Below

coreᶜ : Checker Core
coreᶜ = leiosᶜ ∘ᶜ belowᶜ

-- The validation functionality, on EBs by their hash.
module VF = Functionality EndorserBlock EBRef getEBRef valBackend Δ
open VF public using (ValM; valᶜ; ValState; ValHint; initValState; SUBMIT; QUERY; TICK; DONE)

Stack : Machine (((FFD ⊗₀ BaseNetwork) ⊗₀ VotingC) ⊗₀ VF.ValObs) ((IO ⊗₀ Adv) ⊗₀ VF.ValIO)
Stack = Core ⊗₁ ValM

stackᶜ : Checker Stack
stackᶜ = coreᶜ ⊗ᶜ valᶜ

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
-- And the inputs of the validation machine: what the environment reports
-- of validation, and the requests the log makes in Leios's stead.
data StackInput : Type where
  ffdᵢ  : FFDT Out → StackInput
  netᵢ  : List BaseMsg → StackInput
  voteᵢ : VotingT In → StackInput
  ioᵢ   : IOT In → StackInput
  obsᵢ  : VF.ValObsF In → StackInput
  valᵢ  : VF.ValIOF Out → StackInput

-- The inputs of the two machines, as inputs of the stack.
opaque
  unfolding _⊗₀_

  liftCore : MT.Input Core → MT.Input Stack
  liftCore (inj₁ a) = inj₁ (inj₁ a)
  liftCore (inj₂ b) = inj₂ (inj₁ b)

  liftVal : MT.Input ValM → MT.Input Stack
  liftVal (inj₁ c) = inj₁ (inj₂ c)
  liftVal (inj₂ d) = inj₂ (inj₂ d)

toStackInput : StackInput → MT.Input Stack
toStackInput (ffdᵢ i)  = liftCore (((ϵ ⊗R) ⊗R) ⊗R ↑ᵢ i)
toStackInput (netᵢ bs) = liftCore (((L⊗ ϵ) ⊗R) ⊗R ↑ᵢ bs)
toStackInput (ioᵢ i)   = liftCore (L⊗ (ϵ ᵗ¹ ⊗R) ᵗ¹ ↑ᵢ i)
toStackInput (voteᵢ i) = liftCore ((L⊗ ϵ) ⊗R ↑ᵢ i)
toStackInput (obsᵢ o)  = liftVal (VF.obsInput o)
toStackInput (valᵢ r)  = liftVal (VF.reqInput r)

stack : MT.Checkable Stack toStackInput
stack = record
  { Hint      = Checkable.Hint stackᶜ
  ; hintOf    = Checkable.hintOf stackᶜ
  ; Err       = λ h m → Checkable.Err stackᶜ h (toStackInput m)
  ; checkStep = λ h m → Checkable.checkStep stackᶜ h (toStackInput m)
  }

open MT.Verifier Stack stack public

leiosState : Machine.State Stack → LeiosState
leiosState = proj₂ ∘ proj₁

-- The stack with the given state of the core, and the validation machine's
-- clock at the given slot.
initStack : Machine.State Core → ℕ → Machine.State Stack
initStack c n = c , initValState n

------------------------------------------------------------------------------
-- Error messages

-- The checker of the two layers side by side, whose loop is 'coreᶜ'.
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

  showResult : ValidationResult → String
  showResult Valid      = "Valid"
  showResult Invalid    = "Invalid"
  showResult InProgress = "InProgress"
  showResult Unknown    = "Unknown"

  -- Why the validation machine rejects a step: the log implies another
  -- answer to a query than the machine gives.
  submittedMsg : Maybe ℕ → String
  submittedMsg nothing  = " (the EB was never submitted)"
  submittedMsg (just m) = " (submitted at slot " ◇ show m ◇ ", validation is bounded by "
                            ◇ show Δ ◇ " slots)"

  valMsg : ∀ h i s → Checkable.Err valᶜ h i s → String
  valMsg h i s _ = case VF.queried i of λ where
    nothing  → "the validation machine rejects a step"
    (just r) → "validation of EB " ◇ show r ◇ " at slot " ◇ show (ValState.clock s)
                 ◇ ": the log implies " ◇ maybe showResult "no answer" h
                 ◇ ", but the validation machine answers " ◇ showResult (VF.status s r)
                 ◇ submittedMsg (VF.submittedAt s r)

  -- Either machine of the stack rejects a step.
  stepMsg : ∀ h i s → Checkable.Err stackᶜ h i s → String
  stepMsg (inj₁ _) i s e
    with side {(FFD ⊗₀ BaseNetwork) ⊗₀ VotingC} {IO ⊗₀ Adv} {VF.ValObs} {VF.ValIO} {Core} {ValM} i
  ... | inj₁ _ = loopMsg e
  ... | inj₂ _ = "a step of the validation machine with a hint for Leios and its base"
  stepMsg (inj₂ h) i s e
    with side {(FFD ⊗₀ BaseNetwork) ⊗₀ VotingC} {IO ⊗₀ Adv} {VF.ValObs} {VF.ValIO} {Core} {ValM} i
  ... | inj₂ (m , _) = valMsg h m (proj₂ s) e
  ... | inj₁ _       = "a step of Leios and its base with a hint for the validation machine"

  traceMsg : ∀ {s es} → TraceErr s es → String
  traceMsg {s} (here {h = h} {m = m} e) = stepMsg h (toStackInput m) s e
  traceMsg (there _ e) = traceMsg e

------------------------------------------------------------------------------
-- Running a trace read off a log

-- An input with the action Leios takes on it, a batch of blocks for the base
-- machine with the hint of its step there, the ranking-block step of the
-- given slot, or an input of the validation machine with the answer the log
-- implies, if it is a query.
data Item : Type where
  entry   : Action → StackInput → Item
  deliver : Checkable.Hint baseᶜ → List BaseMsg → Item
  base    : ℕ → Item
  val     : ValHint → StackInput → Item

-- The log's requests to the validation machine, in Leios's stead, and its
-- reports of completed validation.
submitᵥ : EndorserBlock → Item
submitᵥ eb = val nothing (valᵢ (SUBMIT eb))

tickᵥ : Item
tickᵥ = val nothing (obsᵢ TICK)

doneᵥ : EBRef → Item
doneᵥ h = val nothing (obsᵢ (DONE h))

-- A query, to which the log implies the given answer.
expectᵥ : ValidationResult → EBRef → Item
expectᵥ r h = val (just r) (valᵢ (QUERY h))

-- The ranking-block step of a slot is 'Base₁' when the tip calls for no
-- certificate, else 'Base₂' answered by 'CERT nothing' (see
-- 'LinearLeiosTrace', which does the same for Leios alone).
baseEntries : LeiosState → ℕ → Trace
baseEntries s n = case certRequest s of λ where
  nothing  → ⟨ inj₁ (hintsFor (Base₁-Action n)) , ffdᵢ FFDT.SLOT ⟩ ∷ []
  (just _) → ⟨ inj₁ (hintsFor (Base₂-Action n)) , ffdᵢ FFDT.SLOT ⟩
           ∷ ⟨ inj₁ (hintsFor (Cert₁-Action n)) , voteᵢ (CERT nothing) ⟩
           ∷ []

toEntry : Action → StackInput → Entry
toEntry a m = ⟨ inj₁ (hintsFor a) , m ⟩

-- A verification in progress: the state reached, and the entries read since
-- the last ranking-block step, which are verified together at the next one.
-- Kept in reverse.
record Cursor : Type where
  constructor cursor
  field state   : Machine.State Stack
        pending : Trace

flushItems : ⦃ Show Hash ⦄ → Machine.State Stack → Trace → String ⊎ Machine.State Stack
flushItems s es = case verifyTrace s es of λ where
  (inj₁ err)      → inj₁ (traceMsg err)
  (inj₂ (s′ , _)) → inj₂ s′

-- Read further items, verifying at each ranking-block step.  Reading a list
-- in pieces verifies exactly what reading it whole does, which is what lets a
-- stream be verified as it arrives rather than by re-reading its prefix.
stepItems : ⦃ Show Hash ⦄ → Cursor → List Item → String ⊎ Cursor
stepItems c []                                 = inj₂ c
stepItems (cursor s pending) (entry a m ∷ items) =
  stepItems (cursor s (toEntry a m ∷ pending)) items
stepItems (cursor s pending) (deliver h bs ∷ items) =
  stepItems (cursor s (⟨ inj₁ (deliverᴴ h ∷ []) , netᵢ bs ⟩ ∷ pending)) items
stepItems (cursor s pending) (val h m ∷ items) =
  stepItems (cursor s (⟨ inj₂ h , m ⟩ ∷ pending)) items
stepItems (cursor s pending) (base n ∷ items) = case flushItems s (L.reverse pending) of λ where
  (inj₁ err) → inj₁ err
  (inj₂ s′)  → stepItems (cursor s′ (L.reverse (baseEntries (leiosState s′) n))) items

-- Verify the entries still pending, at the end of the input.
finishItems : ⦃ Show Hash ⦄ → Cursor → String ⊎ Machine.State Stack
finishItems (cursor s pending) = flushItems s (L.reverse pending)

-- Verify the items from the given state, returning the final state or the
-- message of the first error.
verifyItems : ⦃ Show Hash ⦄ → Machine.State Stack → List Item → String ⊎ Machine.State Stack
verifyItems s items = case stepItems (cursor s []) items of λ where
  (inj₁ err) → inj₁ err
  (inj₂ c)   → finishItems c
