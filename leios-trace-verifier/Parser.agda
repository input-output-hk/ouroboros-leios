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
{-# COMPILE GHC Map   = type M.Map #-}
{-# COMPILE GHC Int   = type Int #-}
{-# COMPILE GHC elems = elems' #-}
{-# COMPILE GHC trunc = trunc' #-}

Bytes = Word64
SlotNo = Word64
PipelineNo = Word64
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

postulate
  Nullable : Type → Type

{-# COMPILE GHC Nullable = type Nullable #-}

data Event : Type where
  Slot : String → SlotNo → Event
  Cpu : String → Time → String → String → Event
  NoIBGenerated NoEBGenerated NoVTBundleGenerated : String → SlotNo → Event
  IBSent EBSent VTBundleSent RBSent IBReceived EBReceived VTBundleReceived : Maybe Node → Node → Maybe Bytes → Maybe Time → String → Maybe (List String) → Event
  RBReceived : Maybe Node → Node → Maybe Bytes → Maybe Time → String → Maybe (List String) → Event
  IBEnteredState EBEnteredState VTBundleEnteredState RBEnteredState : String → String → Word64 → Event
  IBGenerated : String → String → SlotNo → PipelineNo → Bytes → Bytes → Maybe String → Event
  EBGenerated : String → String → Word64 → PipelineNo → Word64 → List BlockRef → Event
  RBGenerated : String → String → Word64 → Word64 → Nullable Endorsement → Maybe (List Endorsement) → Word64 → Nullable BlockRef → Event
  VTBundleGenerated : String → String → Word64 → PipelineNo → Word64 → Map String Word64 → Event

{-# COMPILE GHC Event = data Event (Slot | Cpu | NoIBGenerated | NoEBGenerated | NoVTBundleGenerated | IBSent | EBSent | VTBundleSent | RBSent | IBReceived | EBReceived | VTBundleReceived | RBReceived | IBEnteredState | EBEnteredState | VTBundleEnteredState | RBEnteredState | IBGenerated | EBGenerated | RBGenerated | VTBundleGenerated) #-}

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
  ... | just n  = from-id n

  open FunTot (completeFin numberOfParties) (maximalFin numberOfParties)

  sd : TotalMap (Fin numberOfParties) ℕ
  sd =
    let (r , l) = fromListᵐ (L.map (λ (x , y) → (nodeId x , y)) stakeDistr)
    in case (¿ total r ¿) of λ where
         (yes p) → record { rel = r ; left-unique-rel = l ; total-rel = p }
         (no _)  → error "Expected total map"

  to-nodeId : ℕ → String
  to-nodeId n = nodePrefix S.++ show n

  SUT : String
  SUT = to-nodeId sutId

  winningSlot : TraceEvent → Maybe (BlockType × ℕ)
  winningSlot record { message = Slot _ _ }                     = nothing
  winningSlot record { message = Cpu _ _ _ _ }                  = nothing
  winningSlot record { message = NoIBGenerated _ _ }            = nothing
  winningSlot record { message = NoEBGenerated _ _ }            = nothing
  winningSlot record { message = NoVTBundleGenerated p _ }      = nothing
  winningSlot record { message = IBSent _ _ _ _ _ _ }           = nothing
  winningSlot record { message = EBSent _ _ _ _ _ _ }           = nothing
  winningSlot record { message = VTBundleSent _ _ _ _ _ _ }     = nothing
  winningSlot record { message = RBSent _ _ _ _ _ _ }           = nothing
  winningSlot record { message = IBReceived _ _ _ _ _ _ }       = nothing
  winningSlot record { message = EBReceived _ _ _ _ _ _ }       = nothing
  winningSlot record { message = VTBundleReceived _ _ _ _ _ _ } = nothing
  winningSlot record { message = RBReceived _ _ _ _ _ _ }       = nothing
  winningSlot record { message = IBEnteredState _ _ _ }         = nothing
  winningSlot record { message = EBEnteredState _ _ _ }         = nothing
  winningSlot record { message = VTBundleEnteredState _ _ _ }   = nothing
  winningSlot record { message = RBEnteredState _ _ _ }         = nothing
  winningSlot record { message = IBGenerated p _ s _ _ _ _}
    with p ≟ SUT
  ... | yes _ = just (IB , primWord64ToNat s)
  ... | no _  = nothing
  winningSlot record { message = EBGenerated p _ s _ _ ibs }
    with p ≟ SUT
  ... | yes _ = just (EB , primWord64ToNat s)
  ... | no _  = nothing
  winningSlot record { message = VTBundleGenerated p i s _ _ vts }
    with p ≟ SUT
  ... | yes _ = just (VT , primWord64ToNat s)
  ... | no _  = nothing
  winningSlot record { message = RBGenerated _ _ _ _ _ _ _ _ }  = nothing

  EventLog = List TraceEvent

  module _ (l : EventLog) where

    params : Params
    params =
      record
        { numberOfParties   = numberOfParties
        ; sutId             = SUT-id
        ; stakeDistribution = sd
        ; stageLength       = sl
        ; winning-slots     = fromList (L.catMaybes $ L.map winningSlot l)
        }

    open import Leios.Short.Trace.Verifier params

    data Blk : Type where
      IB-Blk : InputBlock → Blk
      EB-Blk : EndorserBlock → Blk
      VT-Blk : List Vote → Blk

    record State : Type where
      field refs : AssocList String Blk
            ib-lottery : List ℕ
            eb-lottery : List ℕ
            vt-lottery : List ℕ

    instance
      hhx : Hashable InputBlock (List ℕ)
      hhx .hash record { header = h } = hash h

    blockRefToNat : AssocList String Blk → String → IBRef
    blockRefToNat refs r with refs ⁉ r
    ... | just (IB-Blk ib) = hash ib
    ... | just (EB-Blk _)  = error "IB expected"
    ... | just (VT-Blk _)  = error "IB expected"
    ... | nothing          = error "IB expected"

    open State

    traceEvent→action : State → TraceEvent → State × List ((Action × LeiosInput) ⊎ FFDUpdate)
    traceEvent→action l record { message = Slot p s }
      with p ≟ SUT
    ... | yes _ = l , (inj₁ (Base₂b-Action , SLOT)) ∷ (inj₁ (Slot-Action (primWord64ToNat s) , SLOT)) ∷ []
    ... | no _  = l , []
    traceEvent→action l record { message = Cpu _ _ _ _ } = l , []
    traceEvent→action l record { message = NoIBGenerated p _ }
      with p ≟ SUT
    ... | yes _ = l , (inj₁ (No-IB-Role-Action , SLOT) ∷ [])
    ... | no _  = l , []
    traceEvent→action l record { message = NoEBGenerated p _ }
      with p ≟ SUT
    ... | yes _ = l , (inj₁ (No-EB-Role-Action , SLOT) ∷ [])
    ... | no _  = l , []
    traceEvent→action l record { message = NoVTBundleGenerated p _ }
      with p ≟ SUT
    ... | yes _ = l , (inj₁ (No-VT-Role-Action , SLOT) ∷ [])
    ... | no _  = l , []
    traceEvent→action l record { message = IBSent _ _ _ _ _ _ } = l , []
    traceEvent→action l record { message = EBSent _ _ _ _ _ _ } = l , []
    traceEvent→action l record { message = VTBundleSent _ _ _ _ _ _ } = l , []
    traceEvent→action l record { message = RBSent _ _ _ _ _ _ } = l , []
    traceEvent→action l record { message = IBReceived _ p _ _ i _ }
      with p ≟ SUT | refs l ⁉ i
    ... | yes _ | just (IB-Blk ib) = l , inj₂ (IB-Recv-Update ib) ∷ []
    ... | _ | _ = l , []
    traceEvent→action l record { message = EBReceived _ p _ _ i _ }
      with p ≟ SUT | refs l ⁉ i
    ... | yes _ | just (EB-Blk eb) = l , inj₂ (EB-Recv-Update eb) ∷ []
    ... | _ | _ = l , []
    traceEvent→action l record { message = VTBundleReceived _ p _ _ i _ }
      with p ≟ SUT | refs l ⁉ i
    ... | yes _ | just (VT-Blk vt) = l , inj₂ (VT-Recv-Update vt) ∷ []
    ... | _ | _ = l , []
    traceEvent→action l record { message = RBReceived _ _ _ _ _ _ } = l , []
    traceEvent→action l record { message = IBEnteredState _ _ _ } = l , []
    traceEvent→action l record { message = EBEnteredState _ _ _ } = l , []
    traceEvent→action l record { message = VTBundleEnteredState _ _ _ } = l , []
    traceEvent→action l record { message = RBEnteredState _ _ _ } = l , []
    traceEvent→action l record { message = IBGenerated p i s _ _ _ _}
      with p ≟ SUT
    ... | yes _ = record l { ib-lottery = (primWord64ToNat s) ∷ ib-lottery l } , (inj₁ (IB-Role-Action (primWord64ToNat s) , SLOT)) ∷ []
    ... | no _  = let ib = record { header =
                             record { slotNumber = primWord64ToNat s
                                    ; producerID = nodeId p
                                    ; lotteryPf  = tt
                                    ; bodyHash   = [] -- TODO: txs
                                    ; signature  = tt
                                    }
                                  ; body = record { txs = [] } } -- TODO: add transactions
                  in record l { refs = (i , IB-Blk ib) ∷ refs l } , []
    traceEvent→action l record { message = EBGenerated p i s _ _ ibs }
      with p ≟ SUT
    ... | yes _ = l , (inj₁ (EB-Role-Action (primWord64ToNat s) [] , SLOT)) ∷ []
    ... | no _  = let eb = record
                             { slotNumber = primWord64ToNat s
                             ; producerID = nodeId p
                             ; lotteryPf  = tt
                             ; ibRefs     = map (blockRefToNat (refs l) ∘ BlockRef.id) ibs
                             ; ebRefs     = []
                             ; signature  = tt
                             }
                  in record l { refs = (i , EB-Blk eb) ∷ refs l } , []
    traceEvent→action l record { message = VTBundleGenerated p i s _ _ vts }
      with p ≟ SUT
    ... | yes _ = l , (inj₁ (VT-Role-Action (primWord64ToNat s) , SLOT)) ∷ []
    ... | no _  = let vt = map (const tt) (elems vts)
                  in record l { refs = (i , VT-Blk vt) ∷ refs l } , []
    traceEvent→action l record { message = RBGenerated _ _ _ _ _ _ _ _ } = l , []

    mapAccuml : {A B S : Set} → (S → A → S × B) → S → List A → S × List B
    mapAccuml f s []       = s , []
    mapAccuml f s (x ∷ xs) =
      let (s' , y)   = f s x
          (s'' , ys) = mapAccuml f s' xs
      in s'' , y ∷ ys

    opaque
      unfolding List-Model

      verifyTrace : ℕ
      verifyTrace =
        let s₀ = record { refs = [] ; ib-lottery = [] ; eb-lottery = []  ; vt-lottery = [] }
            l' = proj₂ $ mapAccuml traceEvent→action s₀ l
            αs = L.reverse (L.concat l')
        in if ¿ ValidTrace αs ¿ᵇ then L.length l else 0

      {-# COMPILE GHC verifyTrace as verifyTrace #-}
