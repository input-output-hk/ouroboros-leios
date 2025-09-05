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

module ShortLeiosVerifier
  (numberOfParties : ℕ)
  (sutId : ℕ)
  (stakeDistr : List (Pair String ℕ))
  (stageLength : ℕ)
  (ledgerQuality : ℕ)
  (lateIBInclusion : Bool) -- TODO: Pass config and topology instead
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
    stageLength-NonZero : NonZero stageLength
    stageLength-NonZero with stageLength ≟ 0
    ... | yes _ = error "Stage length is 0"
    ... | no ¬p = ≢-nonZero ¬p

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
              ; ledgerQuality     = ledgerQuality
              ; stakeDistribution = stakeDistribution
              ; stageLength       = stageLength
              ; lateIBInclusion   = lateIBInclusion
              }
        ; sutId         = SUT-id
        ; winning-slots = fromList ∘ L.catMaybes $ L.map winningSlot l
        }

    open import Leios.Short.Trace.Verifier params renaming (verifyTrace to checkTrace)

    data Blk : Type where
      IB-Blk : InputBlock → Blk
      EB-Blk : EndorserBlock → Blk
      VT-Blk : List Vote → Blk
      RB-Blk : EndorserBlock → Blk

    record State : Type where
      field refs : AssocList String Blk
            blks : List Blk

    instance
      Hashable-InputBlock : Hashable InputBlock (List ℕ)
      Hashable-InputBlock .hash record { header = h } = hash h

      _ = Show-List
      _ = Show-×

    unquoteDecl Show-IBHeaderOSig Show-IBBody Show-InputBlock = derive-Show $
        (quote IBHeaderOSig , Show-IBHeaderOSig)
      ∷ (quote IBBody , Show-IBBody)
      ∷ (quote InputBlock , Show-InputBlock)
      ∷ []

    instance
      Show-EBCert : Show (Maybe EBCert)
      Show-EBCert .show (just _) = "EBCert"
      Show-EBCert .show nothing = "no EBCert"

    unquoteDecl Show-EndorserBlockOSig = derive-Show [ (quote EndorserBlockOSig , Show-EndorserBlockOSig) ]
    unquoteDecl Show-RankingBlock = derive-Show [ (quote RankingBlock , Show-RankingBlock) ]
    unquoteDecl Show-Blk = derive-Show [ (quote Blk , Show-Blk) ]

    blockRefToNat : AssocList String Blk → String → IBRef
    blockRefToNat refs r with refs ⁉ r
    ... | just (IB-Blk ib) = hash ib
    ... | just (EB-Blk eb) = error $ "IB expected, got EB instead, " ◇ show eb
    ... | just (VT-Blk vt) = error $ "IB expected, got VT instead"
    ... | just (RB-Blk eb) = error $ "IB expected, got RB instead"
    ... | nothing          = error $ "IB expected, got nothing (" ◇ r ◇ " / " ◇ show refs ◇ ")"

    open State
    open Types params
    open import CategoricalCrypto hiding (_∘_)

    blksToHeaderAndBodyList : List Blk → List (FFDA.Header ⊎ FFDA.Body)
    blksToHeaderAndBodyList [] = []
    blksToHeaderAndBodyList (IB-Blk ib ∷ l) = inj₁ (GenFFD.ibHeader (InputBlock.header ib)) ∷ inj₂ (GenFFD.ibBody (InputBlock.body ib)) ∷ blksToHeaderAndBodyList l
    blksToHeaderAndBodyList (EB-Blk eb ∷ l) = inj₁ (GenFFD.ebHeader eb) ∷ blksToHeaderAndBodyList l
    blksToHeaderAndBodyList (VT-Blk vt ∷ l) = inj₁ (GenFFD.vtHeader vt) ∷ blksToHeaderAndBodyList l
    blksToHeaderAndBodyList (RB-Blk vt ∷ l) = blksToHeaderAndBodyList l

    traceEvent→action : State → TraceEvent → State × List (Action × FFDT Out)
    traceEvent→action l record { message = Slot p s }
      with p ≟ SUT
    ... | yes _ = record l { blks = [] } , (Base₂b-Action (primWord64ToNat s) , FFDT.SLOT) ∷ (Slot-Action (primWord64ToNat s) , FFDT.FFD-OUT (blksToHeaderAndBodyList (blks l))) ∷ []
    ... | no _  = l , []
    traceEvent→action l record { message = Cpu _ _ _ _ } = l , []
    traceEvent→action l record { message = NoIBGenerated p s }
      with p ≟ SUT
    ... | yes _ = l , (No-IB-Role-Action (primWord64ToNat s), FFDT.SLOT) ∷ []
    ... | no _  = l , []
    traceEvent→action l record { message = NoEBGenerated p s }
      with p ≟ SUT
    ... | yes _ = l , (No-EB-Role-Action (primWord64ToNat s), FFDT.SLOT) ∷ []
    ... | no _  = l , []
    traceEvent→action l record { message = NoVTBundleGenerated p s }
      with p ≟ SUT
    ... | yes _ = l , (No-VT-Role-Action (primWord64ToNat s), FFDT.SLOT) ∷ []
    ... | no _  = l , []
    traceEvent→action l record { message = IBSent _ _ _ _ _ _ } = l , []
    traceEvent→action l record { message = EBSent _ _ _ _ _ _ } = l , []
    traceEvent→action l record { message = VTBundleSent _ _ _ _ _ _ } = l , []
    traceEvent→action l record { message = RBSent _ _ _ _ _ _ } = l , []
    traceEvent→action l record { message = IBReceived _ p _ _ i _ }
      with p ≟ SUT | refs l ⁉ i
    ... | yes _ | just ib = record l { blks = ib ∷ blks l } , []
    ... | _ | _ = l , []
    traceEvent→action l record { message = EBReceived _ p _ _ i _ }
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
        actions : List (Action × FFDT Out)
        actions with p ≟ SUT
        ... | yes _ = (IB-Role-Action (primWord64ToNat s) , FFDT.SLOT) ∷ []
        ... | no _ = []
    traceEvent→action l record { message = EBGenerated p i s _ _ ibs ebs _ } =
      let eb = record
                 { slotNumber = primWord64ToNat s
                 ; producerID = nodeId p
                 ; lotteryPf  = tt
                 ; ibRefs     = map (blockRefToNat (refs l) ∘ BlockRef.id) ibs
                 ; ebRefs     = map (blockRefToNat (refs l) ∘ BlockRef.id) ebs
                 ; txs        = []
                 ; signature  = tt
                 }
      in record l { refs = (i , EB-Blk eb) ∷ refs l } , actions
      where
        actions : List (Action × FFDT Out)
        actions with p ≟ SUT
        ... | yes _ = (EB-Role-Action (primWord64ToNat s) [] [] , FFDT.SLOT) ∷ []
        ... | no _  = []
    traceEvent→action l record { message = VTBundleGenerated p i s _ _ vts } =
      let vt = map (const tt) (elems vts)
      in record l { refs = (i , VT-Blk vt) ∷ refs l } , actions
      where
        actions : List (Action × FFDT Out)
        actions with p ≟ SUT
        ... | yes _ = (VT-Role-Action (primWord64ToNat s) , FFDT.SLOT) ∷ []
        ... | no _  = []
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
      Show-Action .show (IB-Role-Action x)     = "IB-Role-Action " ◇ show x
      Show-Action .show (EB-Role-Action x _ _) = "EB-Role-Action " ◇ show x
      Show-Action .show (VT-Role-Action x)     = "VT-Role-Action " ◇ show x
      Show-Action .show (No-IB-Role-Action x)  = "No-IB-Role-Action " ◇ show x
      Show-Action .show (No-EB-Role-Action x)  = "No-EB-Role-Action " ◇ show x
      Show-Action .show (No-VT-Role-Action x)  = "No-VT-Role-Action " ◇ show x
      Show-Action .show (Ftch-Action x)        = "Ftch-Action " ◇ show x
      Show-Action .show (Slot-Action x)        = "Slot-Action " ◇ show x
      Show-Action .show (Base₁-Action x)       = "Base₁-Action " ◇ show x
      Show-Action .show (Base₂a-Action x _)    = "Base₂a-Action " ◇ show x
      Show-Action .show (Base₂b-Action x)      = "Base₂b-Action " ◇ show x

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

    unquoteDecl Show-NetworkParams = derive-Show [ (quote NetworkParams , Show-NetworkParams) ]
    unquoteDecl Show-Params        = derive-Show [ (quote Params , Show-Params) ]
    unquoteDecl Show-Upkeep        = derive-Show [ (quote SlotUpkeep , Show-Upkeep) ]
    unquoteDecl Show-Upkeep-Stage  = derive-Show [ (quote StageUpkeep , Show-Upkeep-Stage) ]
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
