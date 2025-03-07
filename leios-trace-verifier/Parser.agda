open import Leios.Prelude hiding (id)

module Parser where

{-# FOREIGN GHC
  {-# LANGUAGE OverloadedStrings #-}
#-}

{-# FOREIGN GHC
  import Data.Word
  import Data.Fixed
  import Data.Map
  import qualified Data.ByteString.Lazy.Char8 as BSL8
  import LeiosEvents
#-}

postulate
  Int : Set
  Word64 : Set
  Micro : Set
  Map : Set → Set → Set

{-# COMPILE GHC Word64 = type Data.Word.Word64 #-}
{-# COMPILE GHC Micro = type Data.Fixed.Micro #-}
{-# COMPILE GHC Map = type Data.Map.Map #-}
{-# COMPILE GHC Int = type Int #-}

Bytes = Word64
SlotNo = Word64
Time = Micro

data NetworkAction : Type where
  Sent Received : NetworkAction

{-# COMPILE GHC NetworkAction = data NetworkAction (Sent | Received) #-}

data BlockKind : Type where
  IB EB VT RB : BlockKind

{-# COMPILE GHC BlockKind = data BlockKind (IB | EB | VT | RB) #-}

Node = String

record BlockRef : Type where
  field id : String

{-# COMPILE GHC BlockRef = data BlockRef (BlockRef) #-}

record Endorsement : Type where
  field eb : BlockRef

{-# COMPILE GHC Endorsement = data Endorsement (Endorsement) #-}

data Event : Type where
  Cpu : String → Time → String → Event
  IBSent EBSent VTBundleSent RBSent IBReceived EBReceived VTBundleReceived RBReceived : Maybe Node → Node → Maybe Bytes → Maybe Time → Maybe String → Maybe (List String) → Event
  IBEnteredState EBEnteredState VTBundleEnteredState RBEnteredState : String → String → Word64 → Event
  IBGenerated : String → String → SlotNo → Maybe Bytes → Maybe Bytes → Maybe String → Event
  EBGenerated : String → String → Word64 → Word64 → List BlockRef → Event
  RBGenerated : String → Maybe String → Maybe Int → Word64 → Maybe Word64 → Maybe Endorsement → Maybe (List Endorsement) → Maybe Word64 → Event
  VTBundleGenerated : String → String → Word64 → Word64 → Map String Word64 → Event

{-# COMPILE GHC Event = data Event (Cpu | IBSent | EBSent | VTBundleSent | RBSent | IBReceived | EBReceived | VTBundleReceived | RBReceived
  | IBEnteredState | EBEnteredState | VTBundleEnteredState | RBEnteredState | IBGenerated | EBGenerated | RBGenerated | VTBundleGenerated) #-}

record TraceEvent : Type where
  field time_s : Time
        message : Event

{-# COMPILE GHC TraceEvent = data TraceEvent (TraceEvent) #-}

open import Leios.SpecStructure using (SpecStructure)
open import Leios.Defaults 2 fzero using (st; sd; LeiosState; initLeiosState) -- TODO: variables
open import Leios.Trace.Verifier st
open SpecStructure st

EventLog = List TraceEvent

data Action : Type where

  IBGenerated : InputBlock → Action

traceEvent→action : TraceEvent → Maybe Action
traceEvent→action record { message = Cpu x x₁ x₂ } = nothing
traceEvent→action record { message = IBSent x x₁ x₂ x₃ x₄ x₅ } = {!!}
traceEvent→action record { message = EBSent x x₁ x₂ x₃ x₄ x₅ } = {!!}
traceEvent→action record { message = VTBundleSent x x₁ x₂ x₃ x₄ x₅ } = {!!}
traceEvent→action record { message = RBSent x x₁ x₂ x₃ x₄ x₅ } = {!!}
traceEvent→action record { message = IBReceived x x₁ x₂ x₃ x₄ x₅ } = {!!}
traceEvent→action record { message = EBReceived x x₁ x₂ x₃ x₄ x₅ } = {!!}
traceEvent→action record { message = VTBundleReceived x x₁ x₂ x₃ x₄ x₅ } = {!!}
traceEvent→action record { message = RBReceived x x₁ x₂ x₃ x₄ x₅ } = {!!}
traceEvent→action record { message = IBEnteredState x x₁ x₂ } = {!!}
traceEvent→action record { message = EBEnteredState x x₁ x₂ } = {!!}
traceEvent→action record { message = VTBundleEnteredState x x₁ x₂ } = {!!}
traceEvent→action record { message = RBEnteredState x x₁ x₂ } = {!!}
traceEvent→action record { message = IBGenerated x x₁ x₂ x₃ x₄ x₅ } = just (IBGenerated {!!})
traceEvent→action record { message = EBGenerated x x₁ x₂ x₃ x₄ } = {!!}
traceEvent→action record { message = RBGenerated x x₁ x₂ x₃ x₄ x₅ x₆ x₇ } = {!!}
traceEvent→action record { message = VTBundleGenerated x x₁ x₂ x₃ x₄ } = {!!}

Actions = List Action

data ValidAction : Action → LeiosState → Type where

instance
  Dec-ValidAction : ValidAction ⁇²
  Dec-ValidAction {IBGenerated x} {y} .dec = yes {!!}

⟦_⟧ : ∀ {α s} → ValidAction α s → LeiosState
⟦_⟧ {α} {s} = {!!} -- λ where

mutual
  data ValidTrace : Actions → Type where
    [] :
      ─────────────
      ValidTrace []

    _∷_⊣_ : ∀ α {αs} →
      ∀ (tr : ValidTrace αs) →
      ∙ ValidAction α ⟦ tr ⟧∗
        ───────────────────
        ValidTrace (α ∷ αs)

  ⟦_⟧∗ : ∀ {αs : Actions} → ValidTrace αs → LeiosState
  ⟦_⟧∗ [] = initLeiosState tt sd tt
  ⟦_⟧∗ (_ ∷ _ ⊣ vα) = ⟦ vα ⟧

Irr-ValidTrace : ∀ {αs} → Irrelevant (ValidTrace αs)
Irr-ValidTrace = {!!}

instance
  Dec-ValidTrace : ValidTrace ⁇¹
  Dec-ValidTrace {tr} .dec with tr
  ... | [] = yes []
  ... | α ∷ αs
    with ¿ ValidTrace αs ¿
  ... | no ¬vαs = no λ where (_ ∷ vαs ⊣ _) → ¬vαs vαs
  ... | yes vαs
    with ¿ ValidAction α ⟦ vαs ⟧∗ ¿
  ... | no ¬vα = no λ where
    (_ ∷ tr ⊣ vα) → ¬vα
                  $ subst (ValidAction α) (cong ⟦_⟧∗ $ Irr-ValidTrace tr vαs) vα
  ... | yes vα = yes $ _ ∷ vαs ⊣ vα

verifyTrace : EventLog → Bool
verifyTrace l =
  let αs = L.catMaybes $ L.map traceEvent→action l
  in ¿ ValidTrace αs ¿ᵇ

{-# COMPILE GHC verifyTrace as verifyTrace #-}
