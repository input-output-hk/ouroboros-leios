open import Leios.Prelude hiding (id)
open import Agda.Builtin.Word using (Word64; primWord64ToNat)

module Parser where

{-# FOREIGN GHC
  {-# LANGUAGE OverloadedStrings #-}
#-}

postulate
  Int   : Set
  Micro : Set
  Map   : Set → Set → Set
  elems : ∀ {k v} → Map k v → List v
  trunc : Micro → ℕ

{-# FOREIGN GHC
  import Data.Word
  import Data.Fixed
  import qualified Data.Map as M
  import qualified Data.ByteString.Lazy.Char8 as BSL8
  import LeiosEvents

  elems' :: () -> () -> M.Map k v -> [v]
  elems' _ _ = M.elems

  trunc' :: Micro -> Integer
  trunc' = floor
#-}

{-# COMPILE GHC Micro = type Data.Fixed.Micro #-}
{-# COMPILE GHC Map   = type M.Map #-}
{-# COMPILE GHC Int   = type Int #-}
{-# COMPILE GHC elems = elems' #-}
{-# COMPILE GHC trunc = trunc' #-}

Bytes      = Word64
SlotNo     = Word64
PipelineNo = Word64
Time       = Micro

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

postulate
  Nullable : Type → Type
  unwrap : ∀ {a} → Nullable a → Maybe a

{-# COMPILE GHC Nullable = type Nullable #-}
{-# FOREIGN GHC
  unwrap' :: () -> Nullable a -> Maybe a
  unwrap' _ (Nullable x) = x
#-}
{-# COMPILE GHC unwrap = unwrap' #-}

data Event : Type where
  Slot : String → SlotNo → Event
  Cpu : String → Time → String → String → Event
  NoIBGenerated NoEBGenerated NoVTBundleGenerated : String → SlotNo → Event
  IBSent EBSent VTBundleSent RBSent IBReceived EBReceived VTBundleReceived : Maybe Node → Node → Maybe Bytes → Maybe Time → String → Maybe (List String) → Event
  RBReceived : Maybe Node → Node → Maybe Bytes → Maybe Time → String → Maybe (List String) → Event
  IBEnteredState EBEnteredState VTBundleEnteredState RBEnteredState : String → String → Word64 → Event
  IBGenerated : String → String → SlotNo → PipelineNo → Bytes → Bytes → Maybe String → Event
  EBGenerated : String → String → Word64 → PipelineNo → Word64 → List BlockRef → List BlockRef → List Word64 → Event
  RBGenerated : String → String → Word64 → Word64 → Nullable Endorsement → Maybe (List Endorsement) → Word64 → Nullable BlockRef → Event
  VTBundleGenerated : String → String → Word64 → PipelineNo → Word64 → Map String Word64 → Event

{-# COMPILE GHC Event = data Event (Slot | Cpu | NoIBGenerated | NoEBGenerated | NoVTBundleGenerated | IBSent | EBSent | VTBundleSent | RBSent | IBReceived | EBReceived | VTBundleReceived | RBReceived | IBEnteredState | EBEnteredState | VTBundleEnteredState | RBEnteredState | IBGenerated | EBGenerated | RBGenerated | VTBundleGenerated) #-}

record TraceEvent : Type where
  field time_s : Time
        message : Event

{-# COMPILE GHC TraceEvent = data TraceEvent (TraceEvent) #-}
