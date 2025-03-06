open import Leios.Prelude hiding (id)

module Parser where

{-# FOREIGN GHC
  {-# LANGUAGE OverloadedStrings #-}
#-}

open import Leios.Foreign.Defaults 2 fzero
open import Leios.Foreign.Types hiding (EndorserBlock)

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

  IBSent EBSent VTBundleSent RBSent IBReceived EBReceived VTBundleReceived RBReceived :
    Maybe Node → Node → Maybe Bytes → Maybe Time → Maybe String → Maybe (List String) → Event

  IBEnteredState EBEnteredState VTBundleEnteredState RBEnteredState : String → String → Word64 → Event

  IBGenerated : String → String → SlotNo → Maybe Bytes → Maybe Bytes → Maybe String → Event

  EBGenerated : String → String → Word64 → Word64 → List BlockRef → Event

  RBGenerated : String → Maybe String → Maybe Int → Word64 → Maybe Word64 → Maybe Endorsement → Maybe (List Endorsement) → Maybe Word64 → Event

  VTBundleGenerated : String → String → Word64 → Word64 → Map String Word64 → Event

{-# COMPILE GHC Event = data Event (Cpu | IBSent | EBSent | VTBundleSent | RBSent | IBReceived | EBReceived | VTBundleReceived | RBReceived
                                        | IBEnteredState | EBEnteredState | VTBundleEnteredState | RBEnteredState
                                        | IBGenerated | EBGenerated | RBGenerated | VTBundleGenerated) #-}

record TraceEvent : Type where
  field time_s : Time
        message : Event

{-# COMPILE GHC TraceEvent = data TraceEvent (TraceEvent) #-}

-- FIXME: Impplementation
verifyTrace : List TraceEvent → Bool
verifyTrace [] = false
verifyTrace (_ ∷ _) = true

{-# COMPILE GHC verifyTrace as verifyTrace #-}
