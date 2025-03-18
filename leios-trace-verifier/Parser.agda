open import Leios.Prelude hiding (id)
open import Data.Bool using (if_then_else_)

open import Agda.Builtin.Word using (Word64; primWord64ToNat)

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
  Micro : Set
  Map : Set → Set → Set

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
open import Leios.Trace.Verifier

open import Leios.Defaults 2 fzero using (st)
open import Leios.Short st

blockRefToString : BlockRef → String
blockRefToString record { id = ref } = ref

EventLog = List TraceEvent

traceEvent→action : TraceEvent → Maybe (Action × LeiosInput)
traceEvent→action record { message = Cpu x x₁ x₂ } = nothing
traceEvent→action record { message = IBSent x x₁ x₂ x₃ x₄ x₅ } = nothing
traceEvent→action record { message = EBSent x x₁ x₂ x₃ x₄ x₅ } = nothing
traceEvent→action record { message = VTBundleSent x x₁ x₂ x₃ x₄ x₅ } = nothing
traceEvent→action record { message = RBSent x x₁ x₂ x₃ x₄ x₅ } = nothing
traceEvent→action record { message = IBReceived x x₁ x₂ x₃ x₄ x₅ } = nothing
traceEvent→action record { message = EBReceived x x₁ x₂ x₃ x₄ x₅ } = nothing
traceEvent→action record { message = VTBundleReceived x x₁ x₂ x₃ x₄ x₅ } = nothing
traceEvent→action record { message = RBReceived x x₁ x₂ x₃ x₄ x₅ } = nothing
traceEvent→action record { message = IBEnteredState x x₁ x₂ } = nothing
traceEvent→action record { message = EBEnteredState x x₁ x₂ } = nothing
traceEvent→action record { message = VTBundleEnteredState x x₁ x₂ } = nothing
traceEvent→action record { message = RBEnteredState x x₁ x₂ } = nothing
traceEvent→action record { message = IBGenerated p _ s _ _ _ } = just (IB-Role-Action (primWord64ToNat s) , SLOT)
traceEvent→action record { message = EBGenerated p _ s _ ibs } = just (EB-Role-Action (primWord64ToNat s) (map blockRefToString ibs) , SLOT)
traceEvent→action record { message = RBGenerated x x₁ x₂ x₃ x₄ x₅ x₆ x₇ } = nothing
traceEvent→action record { message = VTBundleGenerated p _ s _ _ } = just (VT-Role-Action (primWord64ToNat s) , SLOT)


opaque
  unfolding List-Model

  verifyTrace : EventLog → ℕ
  verifyTrace l =
    let αs = L.catMaybes $ L.map traceEvent→action l
    in if ¿ ValidTrace αs ¿ᵇ then L.length l else 0

  {-# COMPILE GHC verifyTrace as verifyTrace #-}

  test : Bool
  test = ¿ ValidTrace ((IB-Role-Action 0 , SLOT) ∷ []) ¿ᵇ

  _ : test ≡ true
  _ = refl
