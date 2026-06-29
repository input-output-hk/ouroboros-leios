open import Prelude.AssocList
open import Prelude.Result
open import Prelude.Errors

open import Leios.Config
open import Leios.SpecStructure using (SpecStructure)
open import Leios.Prelude hiding (id)

open import Data.Bool using (if_then_else_)
import Data.Nat.Show as S
import Data.String as S
open import Agda.Builtin.Word using (Word64; primWord64ToNat)
open import Agda.Builtin.Char using (primCharToNat)
open import Foreign.Haskell.Pair

open import Tactic.Defaults
open import Tactic.Derive.Show

open import Parser

module LinearLeiosVerifier where

  postulate
    error : {A : Set} → String → A
  {-# FOREIGN GHC import Data.Text #-}
  {-# COMPILE GHC error = \ _ s -> error (unpack s) #-}

  -- The SUT's leadership schedule (winning slots), supplied by the Haskell
  -- runtime: 'Main.hs' queries it via the cardano-api and installs it through
  -- 'LeadershipSchedule.setLeadershipSchedule' before verification.  It is
  -- postulated here so the spec treats it as an abstract oracle rather than
  -- threading it through as data.  An empty schedule means "not provided",
  -- in which case the verifier falls back to harvesting from the trace.
  postulate leadershipSchedule : List ℕ
  {-# FOREIGN GHC import qualified LeadershipSchedule #-}
  {-# COMPILE GHC leadershipSchedule = LeadershipSchedule.leadershipScheduleSlots #-}

  module _
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

    exampleDistr : TotalMap (Fin numberOfParties) ℕ
    exampleDistr =
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
    winningSlot record { message = IBGenerated _ _ _ _ _ _ _}     = nothing
    winningSlot record { message = TXReceived _ _ _ }             = nothing
    winningSlot record { message = TXGenerated _ _ }              = nothing
    winningSlot record { message = EBGenerated p _ s _ _ _ _ _ }
      with p ≟ SUT
    ... | yes _ = just (EB , primWord64ToNat s)
    ... | no _  = nothing
    winningSlot record { message = VTBundleGenerated p _ s _ _ _ }
      with p ≟ SUT
    ... | yes _ = just (VT , primWord64ToNat s)
    ... | no _  = nothing
    winningSlot record { message = RBGenerated _ _ _ _ _ _ _ _ _ }  = nothing

    EventLog = List TraceEvent

    module _ (l : EventLog) where

      params : Params
      params =
        record
          { networkParams =
              record
                { numberOfParties   = numberOfParties
                ; stakeDistribution = exampleDistr
                }
          }

      -- Eligibility ("winning") slots for the SUT.  When a leadership schedule
      -- is supplied (e.g. from `cardano-cli query leadership-schedule`), each
      -- scheduled slot counts as a winning slot for both EB and VT production;
      -- this is authoritative and non-circular.  When no schedule is given the
      -- legacy behaviour is used: harvest the winning slots from the trace.
      winning-slots-of : ℙ (BlockType × ℕ)
      winning-slots-of =
        if L.null leadershipSchedule
          then fromList (L.catMaybes (L.map winningSlot l))
          else fromList (L.concatMap (λ s → (EB , s) ∷ (VT , s) ∷ []) leadershipSchedule)

      testParams : TestParams params
      testParams =
        record
          { sutId         = SUT-id
          ; winning-slots = winning-slots-of
          }

      open import Test.Defaults params testParams using (d-SpecStructure; FFDBuffers; isb; hpe)
      open SpecStructure d-SpecStructure hiding (Hashable-EndorserBlock)

      splitTxs : List Tx → List Tx × List Tx
      splitTxs l = [] , l

      validityCheckTime : EndorserBlock → ℕ
      validityCheckTime eb = validityCheckTimeValue

      open import Leios.Linear.Trace.Verifier d-SpecStructure params Lhdr Lvote Ldiff splitTxs validityCheckTime renaming (verifyTrace to checkTrace)

      open Params params
      open Types params
      open FFD hiding (_-⟦_/_⟧⇀_)
      open GenFFD
      open import CategoricalCrypto hiding (_∘_)

      data Blk : Type where
        EB-Blk : EndorserBlock → Blk
        VT-Blk : List Vote → Blk
        RB-Blk : RankingBlock → Blk

      record Accumulator : Type where
        field EB-refs : AssocList String EndorserBlock
              EB-received : AssocList String ℕ
              VT-refs : AssocList String (List Vote)
              RB-refs : AssocList String RankingBlock
              FFD-blks : List Blk
              currentSlot : ℕ

      open Accumulator

      instance
        _ = Show-List
        _ = Show-×

      instance
        Show-EBCert : Show (Maybe EBCert)
        Show-EBCert .show nothing  = "No EBCert"
        Show-EBCert .show (just c) = show c

      unquoteDecl Show-EndorserBlockOSig = derive-Show [ (quote EndorserBlockOSig , Show-EndorserBlockOSig) ]
      unquoteDecl Show-RankingBlock = derive-Show [ (quote RankingBlock , Show-RankingBlock) ]
      unquoteDecl Show-Blk = derive-Show [ (quote Blk , Show-Blk) ]

      blksToHeaderAndBodyList : List Blk → List (FFDA.Header ⊎ FFDA.Body)
      blksToHeaderAndBodyList []              = []
      blksToHeaderAndBodyList (EB-Blk eb ∷ l) = inj₁ (GenFFD.ebHeader eb) ∷ blksToHeaderAndBodyList l
      blksToHeaderAndBodyList (VT-Blk vt ∷ l) = inj₁ (GenFFD.vtHeader vt) ∷ blksToHeaderAndBodyList l
      blksToHeaderAndBodyList (RB-Blk _ ∷ l)  = blksToHeaderAndBodyList l

      isEB : Blk → Type
      isEB (EB-Blk x) = ⊤
      isEB (VT-Blk x) = ⊥
      isEB (RB-Blk x) = ⊥

      isEB? : ∀ b → Dec (isEB b)
      isEB? (EB-Blk x) = yes tt
      isEB? (VT-Blk x) = no λ ()
      isEB? (RB-Blk x) = no λ ()

      isVT : Blk → Type
      isVT (EB-Blk x) = ⊥
      isVT (VT-Blk x) = ⊤
      isVT (RB-Blk x) = ⊥

      isVT? : ∀ b → Dec (isVT b)
      isVT? (EB-Blk x) = no λ ()
      isVT? (VT-Blk x) = yes tt
      isVT? (RB-Blk x) = no λ ()

      concatList : List ℕ → ℕ
      concatList = foldl addDigit 0
        where
          addDigit : ℕ → ℕ → ℕ
          addDigit n d = 10 * n + d

      private
        test₁ : concatList (1 ∷ 7 ∷ 3 ∷ []) ≡ 173
        test₁ = refl

      -- Negative {EB,VT} event, if there is no {EB,VT}Generated event
      negative-events-EB : List Blk → Word64 → List (Action × (FFDT Out ⊎ BaseT Out ⊎ IOT In))
      negative-events-EB l s
        with Any.any? isEB? l
      ... | yes _ = []
      ... | no  _ = (No-EB-Role-Action (primWord64ToNat s), inj₁ FFDT.SLOT) ∷ []

      negative-events-VT : List Blk → Word64 → List (Action × (FFDT Out ⊎ BaseT Out ⊎ IOT In))
      negative-events-VT l s
        with Any.any? isVT? l
      ... | yes _ = []
      ... | no  _ = (No-VT-Role-Action (primWord64ToNat s), inj₁ FFDT.SLOT) ∷ []

      traceEvent→action : Accumulator → TraceEvent → Accumulator × List (Action × (FFDT Out ⊎ BaseT Out ⊎ IOT In))
      traceEvent→action l record { message = Slot p s }
        with p ≟ SUT
      ... | yes _ =
        record l { FFD-blks = [] ; currentSlot = suc (currentSlot l) } ,
          negative-events-EB (FFD-blks l) s ++ negative-events-VT (FFD-blks l) s ++
            (Base₂-Action (primWord64ToNat s) , inj₁ FFDT.SLOT)
          ∷ (Slot₁-Action (primWord64ToNat s) , inj₁ (FFDT.FFD-OUT (blksToHeaderAndBodyList (FFD-blks l))))
          ∷ []
      ... | no _  = l , []

      -- EBs
      traceEvent→action l record { message = EBGenerated p i s _ _ ibs ebs transactions }
        with (RB-refs l) ⁉ i
      ... | nothing = l , [] -- Assumption: the log respects the order RBGenerated, EBGenerated !
      ... | just rb =
        let eb = record
                   { slotNumber = primWord64ToNat s
                   ; producerID = nodeId p
                   ; lotteryPf  = tt
                   ; txs        = map primWord64ToNat transactions
                   ; signature  = tt
                   }
        in record l
          { EB-refs = (i , eb) ∷ EB-refs l
          ; RB-refs = (i , record rb { announcedEB = just (hash eb) }) ∷ RB-refs l -- Correct RB with EB hash
          } , []
      traceEvent→action l record { message = EBReceived s p _ _ i _ }
        with p ≟ SUT | EB-refs l ⁉ i | RB-refs l ⁉ i
      ... | yes _ | just eb | just rb =
        record l { FFD-blks = EB-Blk eb ∷ FFD-blks l ; EB-received = (i , currentSlot l) ∷ (EB-received l) } , (EB-Role-Action (currentSlot l) eb , inj₁ FFDT.SLOT) ∷ []
      ... | _ | _ | _ = l , []

      -- VTs
      traceEvent→action l record { message = VTBundleGenerated p i s _ _ vts } =
        let vt = map (const tt) (elems vts)
        in record l { VT-refs = (i , vt) ∷ VT-refs l } , []
      traceEvent→action l record { message = VTBundleReceived _ p _ _ i _ }
        with p ≟ SUT | VT-refs l ⁉ i | EB-refs l ⁉ i | EB-received l ⁉ i
      ... | yes _ | just vt | just eb | just slot' = record l { FFD-blks = VT-Blk vt ∷ FFD-blks l } , (VT-Role-Action (currentSlot l) eb slot' , inj₁ FFDT.SLOT) ∷ []
      ... | _ | _ | _ | _ = l , []

      -- RBs
      traceEvent→action l record { message = RBGenerated p i s _ eb _ _ _ txs } =
        let rb = record
                   { txs = map primWord64ToNat txs
                   ; announcedEB = nothing -- this is set in EBReceived
                   ; ebCert = unwrap eb >>= λ b → EB-refs l ⁉ BlockRef.id (Endorsement.eb b) >>= λ eb' → return (hash eb')
                   }
        in record l { RB-refs = (i , rb) ∷ RB-refs l } , []

      traceEvent→action l record { message = RBReceived s p _ _ i _ }
        with p ≟ SUT | RB-refs l ⁉ i
      ... | yes _ | just rb = l , (Slot₂-Action (currentSlot l) , inj₂ (inj₁ (BaseT.BASE-LDG (rb ∷ [])))) ∷ []
      ... | _ | _ = l , []

      -- TXs
      traceEvent→action l record { message = TXGenerated _ _ } = l , []
      traceEvent→action l record { message = TXReceived i _ p }
        with p ≟ SUT
      ... | yes _ = l , (Base₁-Action (currentSlot l) , inj₂ (inj₂ (SubmitTxs (concatList (map primCharToNat (S.toList i)) ∷ [])))) ∷ []
      ... | _     = l , []

      traceEvent→action l record { message = Cpu _ _ _ _ }                = l , []
      traceEvent→action l record { message = IBReceived _ _ _ _ _ _ }     = l , []
      traceEvent→action l record { message = IBGenerated _ _ _ _ _ _ _}   = l , []
      traceEvent→action l record { message = NoIBGenerated _ _ }          = l , []
      traceEvent→action l record { message = NoEBGenerated _ _ }          = l , []
      traceEvent→action l record { message = NoVTBundleGenerated _ _ }    = l , []
      traceEvent→action l record { message = IBSent _ _ _ _ _ _ }         = l , []
      traceEvent→action l record { message = EBSent _ _ _ _ _ _ }         = l , []
      traceEvent→action l record { message = VTBundleSent _ _ _ _ _ _ }   = l , []
      traceEvent→action l record { message = RBSent _ _ _ _ _ _ }         = l , []
      traceEvent→action l record { message = IBEnteredState _ _ _ }       = l , []
      traceEvent→action l record { message = EBEnteredState _ _ _ }       = l , []
      traceEvent→action l record { message = VTBundleEnteredState _ _ _ } = l , []
      traceEvent→action l record { message = RBEnteredState _ _ _ }       = l , []

      s₀ : LeiosState
      s₀ = initLeiosState tt exampleDistr ((SUT-id , tt) ∷ [])

      format-error : ∀ {αs s} → Err-verifyTrace αs s → Pair String String
      format-error x = errorMsg x , "error verifyTrace"

      opaque
        unfolding List-Model

        verifyTrace' : LeiosState → Pair ℕ (Pair String String)
        verifyTrace' s =
          let n₀ = record { EB-refs = [] ; EB-received = [] ; VT-refs = [] ; RB-refs = [] ; FFD-blks = [] ; currentSlot = LeiosState.slot s }
              l' = proj₂ $ mapAccuml traceEvent→action n₀ l
              αs = L.reverse (L.concat l')
              tr = checkTrace αs s
          in L.length αs , result (λ _ → ("ok" , "")) format-error tr
          where
            mapAccuml : {A B S : Set} → (S → A → S × B) → S → List A → S × List B
            mapAccuml f s []       = s , []
            mapAccuml f s (x ∷ xs) =
              let (s' , y)   = f s x
                  (s'' , ys) = mapAccuml f s' xs
              in s'' , y ∷ ys

            result : ∀ {E A S : Type} → (f : A → S) → (g : E → S) → Result E A → S
            result f g (Ok x) = f x
            result f g (Err x) = g x

        verifyTrace : Pair ℕ (Pair String String)
        verifyTrace = verifyTrace' s₀
        {-# COMPILE GHC verifyTrace as verifyTrace #-}

        verifyTraceFromSlot : ℕ → Pair ℕ (Pair String String)
        verifyTraceFromSlot n = verifyTrace' (record s₀ { slot = n })
        {-# COMPILE GHC verifyTraceFromSlot as verifyTraceFromSlot #-}
