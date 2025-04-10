open import Prelude.AssocList

open import Leios.Config
open import Leios.Prelude hiding (id)
open import Leios.Foreign.Util

open import Data.Bool using (if_then_else_)
import Data.Nat.Show as S
import Data.String as S
open import Agda.Builtin.Word using (Word64; primWord64ToNat)
open import Foreign.Haskell.Pair

module Parser where

{-# FOREIGN GHC
  {-# LANGUAGE OverloadedStrings #-}
#-}

postulate
  Int : Set
  Micro : Set
  Map : Set → Set → Set
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
{-# COMPILE GHC Map = type M.Map #-}
{-# COMPILE GHC Int = type Int #-}
{-# COMPILE GHC elems = elems' #-}
{-# COMPILE GHC trunc = trunc' #-}

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

module _ (numberOfParties : ℕ) (sutId : ℕ) (stakeDistr : List (Pair String ℕ)) (sl : ℕ) where

  from-id : ℕ → Fin numberOfParties
  from-id n =
    case n <? numberOfParties of λ where
      (yes p) → #_ n {numberOfParties} {fromWitness p}
      (no _) → error "Conversion to Fin not possible!"

  nodePrefix : String
  nodePrefix = "node-"

  SUT-id : Fin numberOfParties
  SUT-id = from-id sutId

  instance
    sl-NonZero : NonZero sl
    sl-NonZero with sl ≟ 0
    ... | yes _ = error "Stage length is 0"
    ... | no ¬p = ≢-nonZero ¬p

  nodeId : String → Fin numberOfParties
  nodeId s with S.readMaybe 10 (S.fromList (drop (S.length nodePrefix) $ S.toList s))
  ... | nothing = error ("Unknown node: " S.++ s)
  ... | just n = from-id n

  open FunTot (completeFin numberOfParties) (maximalFin numberOfParties)

  sd : TotalMap (Fin numberOfParties) ℕ
  sd =
    let (r , l) = fromListᵐ (L.map (λ (x , y) → (nodeId x , y)) stakeDistr)
    in case (¿ total r ¿) of λ where
         (yes p) → record { rel = r ; left-unique-rel = l ; total-rel = p }
         (no _)  → error "Expected total map"

  params : Params
  params =
    record
      { numberOfParties = numberOfParties
      ; sutId = SUT-id
      ; stakeDistribution = sd
      ; stageLength = sl
      }

  open import Leios.Short.Trace.Verifier params

  to-nodeId : ℕ → String
  to-nodeId n = nodePrefix S.++ show n

  SUT : String
  SUT = to-nodeId sutId

  EventLog = List TraceEvent

  data Blk : Type where
    IB-Blk : InputBlock → Blk
    EB-Blk : EndorserBlock → Blk
    VT-Blk : List Vote → Blk

  record State : Type where
    field refs : AssocList String Blk
          currentSlot : ℕ

  instance
    hhx : Hashable InputBlock (List ℕ)
    hhx .hash record { header = h } = hash h

  blockRefToNat : AssocList String Blk → String → IBRef
  blockRefToNat refs r with refs ⁉ r
  ... | just (IB-Blk ib) = hash ib
  ... | just (EB-Blk _) = error "IB expected"
  ... | just (VT-Blk _) = error "IB expected"
  ... | nothing = error "IB expected"

  open State

  traceEvent→action : State → TraceEvent → State × List ((Action × LeiosInput) ⊎ FFDUpdate)
  traceEvent→action l record { message = Cpu _ _ _ ; time_s = t }
    with trunc t ≟ suc (currentSlot l)
  ... | yes p =
    record l { currentSlot = suc (currentSlot l) }
      , (inj₁ (Base₂b-Action , SLOT)) ∷ (inj₁ (Slot-Action (currentSlot l) , SLOT)) ∷ []
  ... | no _ = l , []
  traceEvent→action l record { message = IBSent _ _ _ _ _ _ } = l , []
  traceEvent→action l record { message = EBSent _ _ _ _ _ _ } = l , []
  traceEvent→action l record { message = VTBundleSent _ _ _ _ _ _ } = l , []
  traceEvent→action l record { message = RBSent _ _ _ _ _ _ } = l , []
  traceEvent→action l record { message = IBReceived _ p _ _ (just i) _ }
    with p ≟ SUT | refs l ⁉ i
  ... | yes _ | just (IB-Blk ib) = l , inj₂ (IB-Recv-Update ib) ∷ []
  ... | _ | _ = l , []
  traceEvent→action l record { message = IBReceived _ _ _ _ nothing _ } = l , []
  traceEvent→action l record { message = EBReceived _ p _ _ (just i) _ }
    with p ≟ SUT | refs l ⁉ i
  ... | yes _ | just (EB-Blk eb) = l , inj₂ (EB-Recv-Update eb) ∷ []
  ... | _ | _ = l , []
  traceEvent→action l record { message = EBReceived _ _ _ _ nothing _ } = l , []
  traceEvent→action l record { message = VTBundleReceived _ p _ _ (just i) _ }
    with p ≟ SUT | refs l ⁉ i
  ... | yes _ | just (VT-Blk vt) = l , inj₂ (VT-Recv-Update vt) ∷ []
  ... | _ | _ = l , []
  traceEvent→action l record { message = VTBundleReceived _ _ _ _ nothing _ } = l , []
  traceEvent→action l record { message = RBReceived _ _ _ _ _ _ } = l , []
  traceEvent→action l record { message = IBEnteredState _ _ _ } = l , []
  traceEvent→action l record { message = EBEnteredState _ _ _ } = l , []
  traceEvent→action l record { message = VTBundleEnteredState _ _ _ } = l , []
  traceEvent→action l record { message = RBEnteredState _ _ _ } = l , []
  traceEvent→action l record { message = IBGenerated p i s _ _ _ }
    with p ≟ SUT
  ... | yes _ = l , (inj₁ (IB-Role-Action (primWord64ToNat s) , SLOT)) ∷ []
  ... | no _  = let ib = record { header =
                           record { slotNumber = primWord64ToNat s
                                  ; producerID = nodeId p
                                  ; lotteryPf  = tt
                                  ; bodyHash   = [] -- TODO: txs
                                  ; signature  = tt
                                  }
                                ; body = record { txs = [] } } -- TODO: add transactions
                in record l { refs = (i , IB-Blk ib) ∷ refs l } , []
  traceEvent→action l record { message = EBGenerated p i s _ ibs }
    with p ≟ SUT
  ... | yes _ = l , (inj₁ (EB-Role-Action (primWord64ToNat s) [] , SLOT)) ∷ []
  ... | no _ = let eb = record
                          { slotNumber = primWord64ToNat s
                          ; producerID = nodeId p
                          ; lotteryPf  = tt
                          ; ibRefs     = map (blockRefToNat (refs l) ∘ BlockRef.id) ibs
                          ; ebRefs     = []
                          ; signature  = tt
                          }
               in record l { refs = (i , EB-Blk eb) ∷ refs l } , []
  traceEvent→action l record { message = VTBundleGenerated p i s _ vts }
    with p ≟ SUT
  ... | yes _ = l , (inj₁ (VT-Role-Action (primWord64ToNat s) , SLOT)) ∷ []
  ... | no _ = let vt = map (const tt) (elems vts)
               in record l { refs = (i , VT-Blk vt) ∷ refs l } , []
  traceEvent→action l record { message = RBGenerated _ _ _ _ _ _ _ _ _ } = l , []

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
      let s₀ = record { refs = [] ; currentSlot = 0 }
          αs = L.reverse $ L.concat $ proj₂ (mapAccuml traceEvent→action s₀ l)
      in if ¿ ValidTrace αs ¿ᵇ then L.length l else 0

    {-# COMPILE GHC verifyTrace as verifyTrace #-}
