open import Prelude.AssocList
open import Prelude.Result

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

open import Parser

module LinearLeiosVerifier
  (numberOfParties : ℕ)
  (sutId : ℕ)
  (stakeDistr : List (Pair String ℕ))
  (Lhdr Lvote Ldiff validityCheckTimeValue : ℕ)
  where

  from-id : ℕ → Fin numberOfParties
  from-id n =
    case n <? numberOfParties of λ where
      (yes p) → #_ n {numberOfParties} {fromWitness p}
      (no _) → error $ "Conversion to Fin not possible! " ◇ show n ◇ " / " ◇ show numberOfParties

  nodePrefix : String
  nodePrefix = "node-"

  SUT-id : Fin numberOfParties
  SUT-id = from-id sutId

  instance
    numberOfParties-NonZero : NonZero numberOfParties
    numberOfParties-NonZero with numberOfParties ≟ 0
    ... | yes _ = error "Number of parties is 0"
    ... | no ¬p = ≢-nonZero ¬p

  nodeId : String → Fin numberOfParties
  nodeId s with S.readMaybe 10 (S.fromList (drop (S.length nodePrefix) $ S.toList s))
  ... | nothing = error ("Unknown node: " ◇ s)
  ... | just n  = from-id n

  open FunTot (completeFin numberOfParties) (maximalFin numberOfParties)

  stakeDistribution : TotalMap (Fin numberOfParties) ℕ
  stakeDistribution =
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
  winningSlot record { message = EBGenerated p _ s _ _ _ _ _ }
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
        { networkParams =
            record
              { numberOfParties   = numberOfParties
              ; ledgerQuality     = 1 -- n/a in Linear Leios
              ; stakeDistribution = stakeDistribution
              ; stageLength       = 1 -- n/a in Linear Leios
              ; lateIBInclusion   = false -- n/a in Linear Leios
              }
        ; sutId         = SUT-id
        ; winning-slots = fromList ∘ L.catMaybes $ L.map winningSlot l
        }

    open import Leios.Linear.Trace.Verifier params

    splitTxs : List Tx → List Tx × List Tx
    splitTxs l = [] , l

    validityCheckTime : EndorserBlock → ℕ
    validityCheckTime eb = validityCheckTimeValue

    open Defaults Lhdr Lvote Ldiff splitTxs validityCheckTime renaming (verifyTrace to checkTrace)

    data Blk : Type where
      IB-Blk : InputBlock → Blk
      EB-Blk : ℕ × EndorserBlock → Blk
      VT-Blk : List Vote → Blk
      RB-Blk : EndorserBlock → Blk

    record State : Type where
      field refs : AssocList String Blk
            blks : List Blk

    instance
      _ = Show-List
      _ = Show-×

    unquoteDecl Show-IBHeaderOSig Show-IBBody Show-InputBlock = derive-Show $
        (quote IBHeaderOSig , Show-IBHeaderOSig)
      ∷ (quote IBBody , Show-IBBody)
      ∷ (quote InputBlock , Show-InputBlock)
      ∷ []

    unquoteDecl Show-EndorserBlockOSig = derive-Show [ (quote EndorserBlockOSig , Show-EndorserBlockOSig) ]
    unquoteDecl Show-Blk = derive-Show [ (quote Blk , Show-Blk) ]


    open State
    open Types params
    open import CategoricalCrypto hiding (_∘_)
    open import Leios.Defaults params using (isb; FFDBuffers)

    blksToHeaderAndBodyList : List Blk → List (FFDA.Header ⊎ FFDA.Body)
    blksToHeaderAndBodyList [] = []
    blksToHeaderAndBodyList (IB-Blk ib ∷ l) = inj₁ (GenFFD.ibHeader (InputBlock.header ib)) ∷ inj₂ (GenFFD.ibBody (InputBlock.body ib)) ∷ blksToHeaderAndBodyList l
    blksToHeaderAndBodyList (EB-Blk (_ , eb) ∷ l) = inj₁ (GenFFD.ebHeader eb) ∷ blksToHeaderAndBodyList l
    blksToHeaderAndBodyList (VT-Blk vt ∷ l) = inj₁ (GenFFD.vtHeader vt) ∷ blksToHeaderAndBodyList l
    blksToHeaderAndBodyList (RB-Blk vt ∷ l) = blksToHeaderAndBodyList l


    traceEvent→action : State → TraceEvent → State × List (Action × (FFDT Out ⊎ BaseT Out ⊎ IOT In))
    traceEvent→action l record { message = Slot p s }
      with p ≟ SUT
    ... | yes _ = record l { blks = [] } , (Base₂-Action (primWord64ToNat s) , inj₁ FFDT.SLOT) ∷ (Slot₂-Action (primWord64ToNat s) , inj₁ (FFDT.FFD-OUT (blksToHeaderAndBodyList (blks l)))) ∷ []
    ... | no _  = l , []
    traceEvent→action l record { message = Cpu _ _ _ _ } = l , []
    traceEvent→action l record { message = NoIBGenerated p s } = l , []
    traceEvent→action l record { message = NoEBGenerated p s }
      with p ≟ SUT
    ... | yes _ = l , (No-EB-Role-Action (primWord64ToNat s), inj₁ FFDT.SLOT) ∷ []
    ... | no _  = l , []
    traceEvent→action l record { message = NoVTBundleGenerated p s }
      with p ≟ SUT
    ... | yes _ = l , (No-VT-Role-Action (primWord64ToNat s), inj₁ FFDT.SLOT) ∷ []
    ... | no _  = l , []
    traceEvent→action l record { message = IBSent _ _ _ _ _ _ } = l , []
    traceEvent→action l record { message = EBSent _ _ _ _ _ _ } = l , []
    traceEvent→action l record { message = VTBundleSent _ _ _ _ _ _ } = l , []
    traceEvent→action l record { message = RBSent _ _ _ _ _ _ } = l , []
    traceEvent→action l record { message = IBReceived _ p _ _ i _ }
      with p ≟ SUT | refs l ⁉ i
    ... | yes _ | just ib = record l { blks = ib ∷ blks l } , []
    ... | _ | _ = l , []
    traceEvent→action l record { message = EBReceived s p _ _ i _ }
      with p ≟ SUT | refs l ⁉ i
    ... | yes _ | just eb = record l { blks = eb ∷ blks l } , []
    ... | _ | _ = l , []
    traceEvent→action l record { message = VTBundleReceived _ p _ _ i _ }
      with p ≟ SUT | refs l ⁉ i
    ... | yes _ | just vt = record l { blks = vt ∷ blks l } , []
    ... | _ | _ = l , []
    traceEvent→action l record { message = RBReceived _ _ _ _ _ _ } = l , []
    traceEvent→action l record { message = IBEnteredState _ _ _ } = l , []
    traceEvent→action l record { message = EBEnteredState _ _ _ } = l , []
    traceEvent→action l record { message = VTBundleEnteredState _ _ _ } = l , []
    traceEvent→action l record { message = RBEnteredState _ _ _ } = l , []
    traceEvent→action l record { message = IBGenerated p i s _ _ _ _} = l , []
    traceEvent→action l record { message = EBGenerated p i s _ _ ibs ebs transactions } =
      let eb = record
                 { slotNumber = primWord64ToNat s
                 ; producerID = nodeId p
                 ; lotteryPf  = tt
                 ; txs        = map primWord64ToNat transactions
                 ; ibRefs     = []
                 ; ebRefs     = []
                 ; signature  = tt
                 }
      in record l { refs = (i , EB-Blk (primWord64ToNat s , eb)) ∷ refs l } , actions eb
      where
        actions : EndorserBlock → List (Action × (FFDT Out ⊎ BaseT Out ⊎ IOT In))
        actions eb with p ≟ SUT
        ... | yes _ = (EB-Role-Action (primWord64ToNat s) eb , inj₁ FFDT.SLOT) ∷ []
        ... | no _  = []
    traceEvent→action l record { message = VTBundleGenerated p i s _ _ vts } =
      let vt = map (const tt) (elems vts)
      in record l { refs = (i , VT-Blk vt) ∷ refs l } , actions
      where
        actions : List (Action × (FFDT Out ⊎ BaseT Out ⊎ IOT In))
        actions with p ≟ SUT | refs l ⁉ i
        ... | yes _ | just (EB-Blk (slot' , eb)) = (VT-Role-Action (primWord64ToNat s) eb slot' , inj₁ FFDT.SLOT) ∷ []
        ... | _ | _ = []
    traceEvent→action l record { message = RBGenerated p i s _ eb _ _ _ }
      with (unwrap eb)
    ... | nothing = l , []
    ... | just b
      with refs l ⁉ BlockRef.id (Endorsement.eb b)
    ... | nothing = l , []
    ... | just e = record l { refs = (i , e) ∷ refs l } , []

    mapAccuml : {A B S : Set} → (S → A → S × B) → S → List A → S × List B
    mapAccuml f s []       = s , []
    mapAccuml f s (x ∷ xs) =
      let (s' , y)   = f s x
          (s'' , ys) = mapAccuml f s' xs
      in s'' , y ∷ ys

    result : ∀ {E A S : Type} → (f : A → S) → (g : E → S) → Result E A → S
    result f g (Ok x) = f x
    result f g (Err x) = g x

    instance
      Show-FFDBuffers : Show FFDBuffers
      Show-FFDBuffers .show _ = "ffd buffers"

      Show-Action : Show Action
      Show-Action .show (EB-Role-Action x _)     = "EB-Role-Action " ◇ show x
      Show-Action .show (VT-Role-Action x _ _)   = "VT-Role-Action " ◇ show x
      Show-Action .show (No-EB-Role-Action x)    = "No-EB-Role-Action " ◇ show x
      Show-Action .show (No-VT-Role-Action x)    = "No-VT-Role-Action " ◇ show x
      Show-Action .show (Ftch-Action x)          = "Ftch-Action " ◇ show x
      Show-Action .show (Slot₁-Action x)         = "Slot₁-Action " ◇ show x
      Show-Action .show (Slot₂-Action x)         = "Slot₂-Action " ◇ show x
      Show-Action .show (Base₁-Action x)         = "Base₁-Action " ◇ show x
      Show-Action .show (Base₂-Action x)         = "Base₂-Action " ◇ show x

    instance
      Show-NonZero : ∀ {n : ℕ} → Show (NonZero n)
      Show-NonZero .show record { nonZero = _ } = "NonZero"

      Show-SD : ∀ {n : ℕ} → Show (TotalMap (Fin n) ℕ)
      Show-SD .show _ = "stake distribution"

    unquoteDecl Show-BlockType = derive-Show [ (quote BlockType , Show-BlockType) ]

    instance
      Show-⊎ : ∀ {ℓ} {A B : Type ℓ} → ⦃ Show A ⦄ → ⦃ Show B ⦄ → Show (A ⊎ B)
      Show-⊎ .show (inj₁ x) = show x
      Show-⊎ .show (inj₂ y) = show y

      Show-⊥ : Show ⊥
      Show-⊥ .show _ = "⊥"

      Show-RB : Show RankingBlock
      Show-RB .show _ = "RB" -- TODO

      Show-BaseT-Out : Show (BaseT Out)
      Show-BaseT-Out .show _ = "BaseT-Out" -- TODO

      Show-IOT-In : Show (IOT In)
      Show-IOT-In .show _ = "IOT-In" -- TODO

    unquoteDecl Show-NetworkParams = derive-Show [ (quote NetworkParams , Show-NetworkParams) ]
    unquoteDecl Show-Params        = derive-Show [ (quote Params , Show-Params) ]
    unquoteDecl Show-Upkeep        = derive-Show [ (quote SlotUpkeep , Show-Upkeep) ]
    unquoteDecl Show-LeiosState    = derive-Show [ (quote LeiosState , Show-LeiosState) ]

    instance
      Show-FFDT-Out : Show (FFDT Out)
      Show-FFDT-Out .show (FFDT.FFD-OUT l) = "FFD-OUT, length " ◇ show (length l)
      Show-FFDT-Out .show FFDT.SLOT        = "SLOT"
      Show-FFDT-Out .show FFDT.FTCH        = "FTCH"

    s₀ : LeiosState
    s₀ = initLeiosState tt stakeDistribution ((SUT-id , tt) ∷ [])

    format-Err-verifyAction :  ∀ {α i s} → Err-verifyAction α i s → Pair String String
    format-Err-verifyAction {α} {i} {s} (E-Err-Slot _)         = "Invalid Slot", "Parameters: " ◇ show params ◇ " Input: " ◇ show i ◇ " LeiosState: " ◇ show s
    format-Err-verifyAction {α} {i} {s} (E-Err-CanProduceIB _) = "Can not produce IB", "Parameters: " ◇ show params ◇ " Input: " ◇ show i ◇ " LeiosState: " ◇ show s
    format-Err-verifyAction {α} {i} {s} dummyErr               = "Transition Error", "Action: " ◇ show α ◇ " Parameters: " ◇ show params ◇ " Input: " ◇ show i ◇ " LeiosState: " ◇ show s

    format-error : ∀ {αs s} → Err-verifyTrace αs s → Pair String String
    format-error {(α , i) ∷ []} {s} (Err-StepOk x) = "Error step" , show α
    format-error {(α , i) ∷ αs} {s} (Err-StepOk x) = format-error x
    format-error {(α , i) ∷ []} {s} (Err-Action x) = format-Err-verifyAction x
    format-error {(α , i) ∷ αs} {s} (Err-Action x) = format-Err-verifyAction x

    opaque
      unfolding List-Model

      verifyTrace' : LeiosState → Pair ℕ (Pair String String)
      verifyTrace' s =
        let n₀ = record { refs = [] ; blks = [] }
            l' = proj₂ $ mapAccuml traceEvent→action n₀ l
            αs = L.reverse (L.concat l')
            tr = checkTrace αs s
        in L.length αs , result (λ _ → ("ok" , "")) format-error tr

      verifyTrace : Pair ℕ (Pair String String)
      verifyTrace = verifyTrace' s₀
      {-# COMPILE GHC verifyTrace as verifyTrace #-}

      verifyTraceFromSlot : ℕ → Pair ℕ (Pair String String)
      verifyTraceFromSlot n = verifyTrace' (record s₀ { slot = n })
      {-# COMPILE GHC verifyTraceFromSlot as verifyTraceFromSlot #-}
