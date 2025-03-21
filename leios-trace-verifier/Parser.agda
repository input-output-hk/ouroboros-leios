open import Prelude.AssocList
open import Leios.Prelude hiding (id)
open import Leios.Foreign.Util

open import Data.Bool using (if_then_else_)
open import Agda.Builtin.Word using (Word64; primWord64ToNat)

module Parser where

{-# FOREIGN GHC
  {-# LANGUAGE OverloadedStrings #-}
#-}

postulate
  Int : Set
  Micro : Set
  Map : Set → Set → Set
  elems : ∀ {k v} → Map k v → List v

{-# COMPILE GHC Micro = type Data.Fixed.Micro #-}
{-# COMPILE GHC Map = type Data.Map.Map #-}
{-# COMPILE GHC Int = type Int #-}

{-# FOREIGN GHC
  import Data.Word
  import Data.Fixed
  import Data.Map as M
  import qualified Data.ByteString.Lazy.Char8 as BSL8
  import LeiosEvents

elems :: Map k v -> [v]
elems = M.elems
#-}

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
  RBGenerated : String → Maybe String → Maybe Int → Word64 → Maybe Word64 → Maybe Endorsement → Maybe (List Endorsement) → Maybe Word64 → Maybe BlockRef → Event
  VTBundleGenerated : String → String → Word64 → Word64 → Map String Word64 → Event

{-# COMPILE GHC Event = data Event (Cpu | IBSent | EBSent | VTBundleSent | RBSent | IBReceived | EBReceived | VTBundleReceived | RBReceived
  | IBEnteredState | EBEnteredState | VTBundleEnteredState | RBEnteredState | IBGenerated | EBGenerated | RBGenerated | VTBundleGenerated) #-}

record TraceEvent : Type where
  field time_s : Time
        message : Event

{-# COMPILE GHC TraceEvent = data TraceEvent (TraceEvent) #-}

open import Leios.SpecStructure using (SpecStructure)

open import Leios.Defaults 10 fzero hiding (LeiosInput; LeiosOutput; SLOT)
open import Leios.Trace.Verifier 10 fzero
open import Leios.Short st
import Data.String as S

nodeId : String → Fin 10
nodeId "node-0" = fzero
nodeId "node-1" = fsuc fzero
nodeId "node-2" = fsuc $ fsuc fzero
nodeId "node-3" = fsuc $ fsuc $ fsuc $ fzero
nodeId "node-4" = fsuc $ fsuc $ fsuc $ fsuc $ fzero
nodeId "node-5" = fsuc $ fsuc $ fsuc $ fsuc $ fsuc $ fzero
nodeId "node-6" = fsuc $ fsuc $ fsuc $ fsuc $ fsuc $ fsuc $ fzero
nodeId "node-7" = fsuc $ fsuc $ fsuc $ fsuc $ fsuc $ fsuc $ fsuc $ fzero
nodeId "node-8" = fsuc $ fsuc $ fsuc $ fsuc $ fsuc $ fsuc $ fsuc $ fsuc $ fzero
nodeId "node-9" = fsuc $ fsuc $ fsuc $ fsuc $ fsuc $ fsuc $ fsuc $ fsuc $ fsuc $ fzero
nodeId s        = error ("Unknown node: " S.++ s)

SUT : String
SUT = "node-0"

blockRefToString : BlockRef → String
blockRefToString record { id = ref } = ref

EventLog = List TraceEvent

data Blk : Type where
  IB-Blk : InputBlock → Blk
  EB-Blk : EndorserBlock → Blk
  VT-Blk : List Vote → Blk

traceEvent→action : AssocList String Blk → TraceEvent → AssocList String Blk × Maybe ((Action × LeiosInput) ⊎ FFDUpdate)
traceEvent→action l record { message = Cpu _ _ _ } = l , nothing
traceEvent→action l record { message = IBSent _ _ _ _ _ _ } = l , nothing
traceEvent→action l record { message = EBSent _ _ _ _ _ _ } = l , nothing
traceEvent→action l record { message = VTBundleSent _ _ _ _ _ _ } = l , nothing
traceEvent→action l record { message = RBSent _ _ _ _ _ _ } = l , nothing
traceEvent→action l record { message = IBReceived _ p _ _ (just i) _ }
  with p ≟ SUT | l ⁉ i
... | yes _ | just (IB-Blk ib) = l ,  just (inj₂ (IB-Recv-Update ib))
... | _ | _ = l , nothing
traceEvent→action l record { message = IBReceived _ _ _ _ nothing _ } = l , nothing
traceEvent→action l record { message = EBReceived _ p _ _ (just i) _ }
  with p ≟ SUT | l ⁉ i
... | yes _ | just (EB-Blk eb) = l ,  just (inj₂ (EB-Recv-Update eb))
... | _ | _ = l , nothing
traceEvent→action l record { message = EBReceived _ _ _ _ nothing _ } = l , nothing
traceEvent→action l record { message = VTBundleReceived _ p _ _ (just i) _ }
  with p ≟ SUT | l ⁉ i
... | yes _ | just (VT-Blk vt) = l ,  just (inj₂ (VT-Recv-Update vt))
... | _ | _ = l , nothing
traceEvent→action l record { message = VTBundleReceived _ _ _ _ nothing _ } = l , nothing
traceEvent→action l record { message = RBReceived _ _ _ _ _ _ } = l , nothing
traceEvent→action l record { message = IBEnteredState _ _ _ } = l , nothing
traceEvent→action l record { message = EBEnteredState _ _ _ } = l , nothing
traceEvent→action l record { message = VTBundleEnteredState _ _ _ } = l , nothing
traceEvent→action l record { message = RBEnteredState _ _ _ } = l , nothing
traceEvent→action l record { message = IBGenerated p i s _ _ _ }
  with p ≟ SUT
... | yes _ = l , just (inj₁ (IB-Role-Action (primWord64ToNat s) , SLOT))
... | no _  = let ib = record { header =
                         record { slotNumber = primWord64ToNat s
                                ; producerID = nodeId p
                                ; lotteryPf  = tt
                                ; bodyHash   = ""
                                ; signature  = tt
                                }
                              ; body = record { txs = [] } } -- TODO: add transactions
              in (i , IB-Blk ib) ∷ l , nothing
traceEvent→action l record { message = EBGenerated p i s _ ibs }
  with p ≟ SUT
... | yes _ = l , just (inj₁ (EB-Role-Action (primWord64ToNat s) (map blockRefToString ibs) , SLOT))
... | no _ = let eb = record
                        { slotNumber = primWord64ToNat s
                        ; producerID = nodeId p
                        ; lotteryPf  = tt
                        ; ibRefs     = map blockRefToString ibs
                        ; ebRefs     = []
                        ; signature  = tt
                        }
             in (i , EB-Blk eb) ∷ l , nothing
traceEvent→action l record { message = VTBundleGenerated p i s _ vts }
  with p ≟ SUT
... | yes _ = l , just (inj₁ (VT-Role-Action (primWord64ToNat s) , SLOT))
... | no _ = let vt = map (const tt) (elems vts)
             in (i , VT-Blk vt) ∷ l , nothing
traceEvent→action l record { message = RBGenerated _ _ _ _ _ _ _ _ _ } = l , nothing

mapAccuml : {A B S : Set} → (S → A → S × B) → S → List A → S × List B
mapAccuml f s []       = s , []
mapAccuml f s (x ∷ xs) =
  let (s' , y)   = f s x
      (s'' , ys) = mapAccuml f s' xs
  in s'' , y ∷ ys

opaque
  unfolding List-Model

  verifyTrace : EventLog → ℕ
  verifyTrace l =
    let αs = L.catMaybes $ proj₂ (mapAccuml traceEvent→action [] l)
    in if ¿ ValidTrace αs ¿ᵇ then L.length l else 0

  {-# COMPILE GHC verifyTrace as verifyTrace #-}
