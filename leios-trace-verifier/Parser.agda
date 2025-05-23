open import Prelude.AssocList

open import Leios.Config
open import Leios.Prelude hiding (id)
open import Leios.Foreign.Util

open import Data.Bool using (if_then_else_)
import Data.Nat.Show as S
import Data.String as S
open import Agda.Builtin.Word using (Word64; primWord64ToNat)
open import Foreign.Haskell.Pair

open import Tactic.Defaults
open import Tactic.Derive.Show

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
  ... | nothing = error ("Unknown node: " ◇ s)
  ... | just n  = from-id n

  open FunTot (completeFin numberOfParties) (maximalFin numberOfParties)

  sd : TotalMap (Fin numberOfParties) ℕ
  sd =
    let (r , l) = fromListᵐ (L.map (λ (x , y) → (nodeId x , y)) stakeDistr)
    in case (¿ total r ¿) of λ where
         (yes p) → record { rel = r ; left-unique-rel = l ; total-rel = p }
         (no _)  → error "Expected total map"

  to-nodeId : ℕ → String
  to-nodeId n = nodePrefix ◇ show n

  SUT : String
  SUT = to-nodeId sutId

  winningSlot : TraceEvent → Maybe (BlockType × ℕ)
  winningSlot record { message = Slot _ _ }                     = nothing
  winningSlot record { message = Cpu _ _ _ _ }                  = nothing
  winningSlot record { message = NoIBGenerated _ _ }            = nothing
  winningSlot record { message = NoEBGenerated _ _ }            = nothing
  winningSlot record { message = NoVTBundleGenerated _ _ }      = nothing
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
  winningSlot record { message = EBGenerated p _ s _ _ _ }
    with p ≟ SUT
  ... | yes _ = just (EB , primWord64ToNat s)
  ... | no _  = nothing
  winningSlot record { message = VTBundleGenerated p _ s _ _ _ }
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

    open import Leios.Short.Trace.Verifier params renaming (verifyTrace to checkTrace)

    data Blk : Type where
      IB-Blk : InputBlock → Blk
      EB-Blk : EndorserBlock → Blk
      VT-Blk : List Vote → Blk

    record State : Type where
      field refs : AssocList String Blk

    instance
      hhx : Hashable InputBlock (List ℕ)
      hhx .hash record { header = h } = hash h

      _ = Show-List
      _ = Show-×

    unquoteDecl Show-IBHeaderOSig Show-IBBody Show-InputBlock = derive-Show $
        (quote IBHeaderOSig , Show-IBHeaderOSig)
      ∷ (quote IBBody , Show-IBBody)
      ∷ (quote InputBlock , Show-InputBlock)
      ∷ []

    unquoteDecl Show-EndorserBlockOSig = derive-Show [ (quote EndorserBlockOSig , Show-EndorserBlockOSig) ]
    unquoteDecl Show-Blk = derive-Show [ (quote Blk , Show-Blk) ]

    del : String
    del = ", "

    nl : String
    nl = "\n"

    blockRefToNat : AssocList String Blk → String → IBRef
    blockRefToNat refs r with refs ⁉ r
    ... | just (IB-Blk ib) = hash ib
    ... | just (EB-Blk eb) = error $ "IB expected, got EB instead, " ◇ show eb
    ... | just (VT-Blk vt) = error $ "IB expected, got VT instead"
    ... | nothing          = error $ "IB expected, got nothing (" ◇ r ◇ " / " ◇ show refs ◇ ")"

    open State

    traceEvent→action : State → TraceEvent → State × List ((Action × LeiosInput) ⊎ FFDUpdate)
    traceEvent→action l record { message = Slot p s }
      with p ≟ SUT
    ... | yes _ = l , (inj₁ (Base₂b-Action (primWord64ToNat s) , SLOT)) ∷ (inj₁ (Slot-Action (primWord64ToNat s) , SLOT)) ∷ []
    ... | no _  = l , []
    traceEvent→action l record { message = Cpu _ _ _ _ } = l , []
    traceEvent→action l record { message = NoIBGenerated p s }
      with p ≟ SUT
    ... | yes _ = l , (inj₁ (No-IB-Role-Action (primWord64ToNat s), SLOT) ∷ [])
    ... | no _  = l , []
    traceEvent→action l record { message = NoEBGenerated p s }
      with p ≟ SUT | stage (primWord64ToNat s) ≤? 2 -- ignore bootstrapping events from Rust simulation
    ... | yes _ | no _ = l , (inj₁ (No-EB-Role-Action (primWord64ToNat s), SLOT) ∷ [])
    ... | _     | _    = l , []
    traceEvent→action l record { message = NoVTBundleGenerated p s }
      with p ≟ SUT | stage (primWord64ToNat s) ≤? 3 -- ignore bootstrapping events from Rust simulation
    ... | yes _ | no _ = l , (inj₁ (No-VT-Role-Action (primWord64ToNat s), SLOT) ∷ [])
    ... | _     | _    = l , []
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
    traceEvent→action l record { message = IBGenerated p i s _ _ _ _} =
      let ib = record { header =
                 record { slotNumber = primWord64ToNat s
                        ; producerID = nodeId p
                        ; lotteryPf  = tt
                        ; bodyHash   = [] -- TODO: txs
                        ; signature  = tt
                        }
                      ; body = record { txs = [] } } -- TODO: add transactions
      in record l { refs = (i , IB-Blk ib) ∷ refs l } , actions
      where
        actions : List (Action × LeiosInput ⊎ FFDUpdate)
        actions with p ≟ SUT
        ... | yes _ = (inj₁ (IB-Role-Action (primWord64ToNat s) , SLOT)) ∷ []
        ... | no _ = []
    traceEvent→action l record { message = EBGenerated p i s _ _ ibs } =
      let eb = record
                 { slotNumber = primWord64ToNat s
                 ; producerID = nodeId p
                 ; lotteryPf  = tt
                 ; ibRefs     = map (blockRefToNat (refs l) ∘ BlockRef.id) ibs
                 ; ebRefs     = []
                 ; signature  = tt
                 }
      in record l { refs = (i , EB-Blk eb) ∷ refs l } , actions
      where
        actions : List (Action × LeiosInput ⊎ FFDUpdate)
        actions with p ≟ SUT | stage (primWord64ToNat s) ≤? 2 -- ignore bootstrapping events from Rust simulation
        ... | yes _ | no _ = (inj₁ (EB-Role-Action (primWord64ToNat s) [] , SLOT)) ∷ []
        ... | _     | _    = []
    traceEvent→action l record { message = VTBundleGenerated p i s _ _ vts } =
      let vt = map (const tt) (elems vts)
      in record l { refs = (i , VT-Blk vt) ∷ refs l } , actions
      where
        actions : List (Action × LeiosInput ⊎ FFDUpdate)
        actions with p ≟ SUT | stage (primWord64ToNat s) ≤? 3 -- ignore bootstrapping events from Rust simulation
        ... | yes _ | no _ = (inj₁ (VT-Role-Action (primWord64ToNat s) , SLOT)) ∷ []
        ... | _     | _    = []
    traceEvent→action l record { message = RBGenerated _ _ _ _ _ _ _ _ } = l , []

    mapAccuml : {A B S : Set} → (S → A → S × B) → S → List A → S × List B
    mapAccuml f s []       = s , []
    mapAccuml f s (x ∷ xs) =
      let (s' , y)   = f s x
          (s'' , ys) = mapAccuml f s' xs
      in s'' , y ∷ ys

    result : ∀ {E A : Type} → (f : A → String) → (g : E → String) → Result E A → String
    result f g (Ok x) = f x
    result f g (Err x) = g x

{-
    unquoteDecl Show-FFDBuffers = derive-Show [ (quote FFDBuffers , Show-FFDBuffers) ]
    unquoteDecl Show-Action = derive-Show [ (quote Action , Show-Action) ]
-}

    instance
      Show-FFDBuffers : Show FFDBuffers
      Show-FFDBuffers .show _ = "ffd buffers"

      Show-Action : Show Action
      Show-Action .show (IB-Role-Action x)    = "IB-Role-Action " ◇ show x
      Show-Action .show (EB-Role-Action x _)  = "EB-Role-Action " ◇ show x
      Show-Action .show (VT-Role-Action x)    = "VT-Role-Action " ◇ show x
      Show-Action .show (No-IB-Role-Action x) = "No-IB-Role-Action " ◇ show x
      Show-Action .show (No-EB-Role-Action x) = "No-EB-Role-Action " ◇ show x
      Show-Action .show (No-VT-Role-Action x) = "No-VT-Role-Action " ◇ show x
      Show-Action .show (Ftch-Action x)       = "Ftch-Action " ◇ show x
      Show-Action .show (Slot-Action x)       = "Slot-Action " ◇ show x
      Show-Action .show (Base₁-Action x)      = "Base₁-Action " ◇ show x
      Show-Action .show (Base₂a-Action x _)   = "Base₂a-Action " ◇ show x
      Show-Action .show (Base₂b-Action x)     = "Base₂b-Action " ◇ show x

    instance
      Show-NonZero : ∀ {n : ℕ} → Show (NonZero n)
      Show-NonZero .show record { nonZero = _ } = "NonZero"

      Show-SD : ∀ {n : ℕ} → Show (TotalMap (Fin n) ℕ)
      Show-SD .show _ = "stake distribution"

    unquoteDecl Show-BlockType = derive-Show [ (quote BlockType , Show-BlockType) ]

    instance
      Show-sum : Show (EndorserBlock ⊎ List Tx)
      Show-sum .show (inj₁ x) = show x
      Show-sum .show (inj₂ y) = show y

    unquoteDecl Show-FFDUpdate    = derive-Show [ (quote FFDUpdate , Show-FFDUpdate) ]
    unquoteDecl Show-Params       = derive-Show [ (quote Params , Show-Params) ]
    unquoteDecl Show-Upkeep       = derive-Show [ (quote SlotUpkeep , Show-Upkeep) ]
    unquoteDecl Show-Upkeep-Stage = derive-Show [ (quote StageUpkeep , Show-Upkeep-Stage) ]
    unquoteDecl Show-LeiosState   = derive-Show [ (quote LeiosState , Show-LeiosState) ]
    unquoteDecl Show-LeiosInput   = derive-Show [ (quote LeiosInput , Show-LeiosInput) ]

    s₀ : LeiosState
    s₀ = initLeiosState tt sd tt ((SUT-id , tt) ∷ [])

    format-Err-verifyAction :  ∀ {α i s} → Err-verifyAction α i s → String
    format-Err-verifyAction {α} {i} {s} (E-Err e) =
        "Invalid Action: Slot " ◇ show α ◇ nl
      ◇ "Parameters: " ◇ show params ◇ nl
      ◇ "Input: " ◇ show i ◇ nl
      ◇ "LeiosState: " ◇ show s

    format-Err-verifyUpdate : ∀ {μ s} → Err-verifyUpdate μ s → String
    format-Err-verifyUpdate {μ} (E-Err _) = "Invalid Update: " ◇ show μ

    format-error : ∀ {αs s} → Err-verifyTrace αs s → String
    format-error {inj₁ (α , i) ∷ []} {s} (Err-StepOk x) = "error step: " ◇ show α
    format-error {inj₁ (α , i) ∷ αs} {s} (Err-StepOk x) = format-error x
    format-error {inj₂ μ ∷ []} {s} (Err-UpdateOk x)     = "error update: " ◇ show μ
    format-error {inj₂ μ ∷ αs} {s} (Err-UpdateOk x)     = format-error x
    format-error {inj₁ (α , i) ∷ []} {s} (Err-Action x) = format-Err-verifyAction x
    format-error {inj₁ (α , i) ∷ αs} {s} (Err-Action x) = format-Err-verifyAction x
    format-error {inj₂ μ ∷ []} {s} (Err-Update x)       = format-Err-verifyUpdate x
    format-error {inj₂ μ ∷ αs} {s} (Err-Update x)       = format-Err-verifyUpdate x

    opaque
      unfolding List-Model

      verifyTrace : Pair ℕ String
      verifyTrace =
        let n₀ = record { refs = [] }
            l' = proj₂ $ mapAccuml traceEvent→action n₀ l
            αs = L.reverse (L.concat l')
            tr = checkTrace αs s₀
        in L.length αs , result (λ _ → "ok") format-error tr

      {-# COMPILE GHC verifyTrace as verifyTrace #-}
