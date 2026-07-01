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
open import Foreign.Haskell.Pair

open import Tactic.Defaults
open import Tactic.Derive.Show

module LinearLeiosVerifierChain where

  postulate
    error : {A : Set} → String → A
  {-# FOREIGN GHC import Data.Text #-}
  {-# COMPILE GHC error = \ _ s -> error (unpack s) #-}

  postulate leadershipSchedule : List ℕ
  {-# FOREIGN GHC import qualified LeadershipSchedule #-}
  {-# COMPILE GHC leadershipSchedule = LeadershipSchedule.leadershipScheduleSlots #-}

  -- | A Leios event extracted from a cardano-node tracing log (node.log), keyed
  --   by the EB hash. Mirrors 'ChainEvents.ChainEvent' on the Haskell side.
  data ChainEvent : Type where
    CSlot        : Word64 → ChainEvent
    CEBForged    : String → Word64 → ChainEvent
    CEBAcquired  : String → Word64 → ChainEvent
    CVoted       : String → Word64 → ChainEvent
    CVoteAcquired : String → Word64 → ChainEvent
    CRBForged    : String → Word64 → ChainEvent

  {-# FOREIGN GHC import qualified ChainEvents #-}
  {-# COMPILE GHC ChainEvent = data ChainEvents.ChainEvent
        ( ChainEvents.CSlot
        | ChainEvents.CEBForged
        | ChainEvents.CEBAcquired
        | ChainEvents.CVoted
        | ChainEvents.CVoteAcquired
        | ChainEvents.CRBForged
        ) #-}

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

    SUT-id : Fin numberOfParties
    SUT-id = from-id sutId

    instance
      numberOfParties-NonZero : NonZero numberOfParties
      numberOfParties-NonZero with numberOfParties ≟ 0
      ... | yes _ = error "Number of parties is 0"
      ... | no ¬p = ≢-nonZero ¬p

    open FunTot (completeFin numberOfParties) (maximalFin numberOfParties)

    nodeId : String → Fin numberOfParties
    nodeId _ = SUT-id

    exampleDistr : TotalMap (Fin numberOfParties) ℕ
    exampleDistr =
      let (r , l) = fromListᵐ (L.map (λ (x , y) → (from-id-of x , y)) stakeDistr)
      in case (¿ total r ¿) of λ where
           (yes p) → record { rel = r ; left-unique-rel = l ; total-rel = p }
           (no _)  → error "Expected total map"
      where
        from-id-of : String → Fin numberOfParties
        from-id-of s with S.readMaybe 10 (S.fromList (drop (S.length "node-") (S.toList s)))
        ... | nothing = error ("Unknown node: " ◇ s)
        ... | just n  = from-id n

    EventLog = List ChainEvent

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

      -- EB-production eligibility comes from the leadership schedule (queried from
      -- the node); voting eligibility is the CIP-0164 committee in Defaults.
      winning-slots-of : ℙ (BlockType × ℕ)
      winning-slots-of = fromList (L.map (λ s → EB , s) leadershipSchedule)

      testParams : TestParams params
      testParams =
        record
          { sutId         = SUT-id
          ; winning-slots = winning-slots-of
          }

      open import Defaults params testParams using (d-SpecStructure; FFDBuffers; isb; hpe)
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

      -- Synthesized non-empty transaction list (the node records only counts).
      synthTxs : List Tx
      synthTxs = 0 ∷ []

      mkEBrec : String → Word64 → EndorserBlock
      mkEBrec _ s = record
        { slotNumber = primWord64ToNat s
        ; producerID = SUT-id
        ; lotteryPf  = tt
        ; txs        = synthTxs
        ; signature  = tt
        }

      -- Accumulator threaded through the chain events. Slot obligations are
      -- flushed when the next CSlot arrives (or at end of stream).
      record Accumulator : Type where
        field EB-refs     : AssocList String EndorserBlock
              EB-received : AssocList String ℕ
              FFD-blks    : List Blk
              curSlot     : ℕ
              started     : Bool
              curEB       : Maybe String
              forgedEB    : Maybe EndorserBlock
              votedEB     : Maybe (EndorserBlock × ℕ)

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

      Step = Action × (FFDT Out ⊎ BaseT Out ⊎ IOT In)

      -- Hash of the EB registered under a given hash-string (identity on payload,
      -- see Defaults); [] if unknown.
      hashOf : Accumulator → String → Hash
      hashOf a h = case EB-refs a ⁉ h of λ where
        (just eb) → hash eb
        nothing   → []

      -- Emit the obligations for the slot being closed, chronologically.
      closeSlot : Accumulator → List Step
      closeSlot a =
        let s = curSlot a
            annRB : List Step
            annRB = case curEB a of λ where
              nothing  → []
              (just h) →
                (Slot₂-Action s , inj₂ (inj₁ (BaseT.BASE-LDG
                  (record { txs = [] ; announcedEB = just (hashOf a h) ; ebCert = nothing } ∷ [])))) ∷ []
            ebRole : List Step
            ebRole = case forgedEB a of λ where
              (just eb) → (EB-Role-Action s eb , inj₁ FFDT.SLOT) ∷ []
              nothing   → (No-EB-Role-Action s , inj₁ FFDT.SLOT) ∷ []
            vtRole : List Step
            vtRole = case votedEB a of λ where
              (just (eb , slot')) → (VT-Role-Action s eb slot' , inj₁ FFDT.SLOT) ∷ []
              nothing             → (No-VT-Role-Action s , inj₁ FFDT.SLOT) ∷ []
        in annRB
           ++ ((Base₂-Action s , inj₁ FFDT.SLOT) ∷ ebRole)
           ++ vtRole
           ++ ((Slot₁-Action s , inj₁ (FFDT.FFD-OUT (blksToHeaderAndBodyList (FFD-blks a)))) ∷ [])

      traceEvent→action : Accumulator → ChainEvent → Accumulator × List Step
      traceEvent→action a (CSlot s) =
        if not (started a)
          then (record a { curSlot = primWord64ToNat s ; started = true } , [])
          else
            let block = closeSlot a
            in (record a
                  { curSlot = primWord64ToNat s
                  ; FFD-blks = []
                  ; forgedEB = nothing
                  ; votedEB = nothing
                  } , block)
      traceEvent→action a (CEBForged h s) =
        let eb = mkEBrec h s
        in (record a { EB-refs = (h , eb) ∷ EB-refs a ; forgedEB = just eb } , [])
      traceEvent→action a (CEBAcquired h s) =
        let eb = mkEBrec h s
        in (record a
              { EB-refs = (h , eb) ∷ EB-refs a
              ; EB-received = (h , curSlot a) ∷ EB-received a
              ; FFD-blks = EB-Blk eb ∷ FFD-blks a
              ; curEB = just h
              } , [])
      traceEvent→action a (CVoted h s)
        with EB-refs a ⁉ h | EB-received a ⁉ h
      ... | just eb | just slot' = (record a { votedEB = just (eb , slot') ; curEB = just h } , [])
      ... | _       | _          = (a , [])
      traceEvent→action a (CVoteAcquired h s) = (a , [])
      traceEvent→action a (CRBForged h s) = (a , [])

      s₀ : LeiosState
      s₀ = initLeiosState tt exampleDistr ((SUT-id , tt) ∷ [])

      format-error : ∀ {αs s} → Err-verifyTrace αs s → Pair String String
      format-error x = errorMsg x , "error verifyChainTrace"

      n₀ : ℕ → Accumulator
      n₀ st = record
        { EB-refs = [] ; EB-received = [] ; FFD-blks = [] ; curSlot = st
        ; started = false ; curEB = nothing ; forgedEB = nothing ; votedEB = nothing }

      opaque
        unfolding List-Model

        verifyChainTrace' : LeiosState → Pair ℕ (Pair String String)
        verifyChainTrace' s =
          let (aFinal , l') = mapAccuml traceEvent→action (n₀ (LeiosState.slot s)) l
              final = if started aFinal then closeSlot aFinal else []
              αs = L.reverse (L.concat l' ++ final)
              tr = checkTrace αs s
          in L.length αs , result (λ _ → ("ok" , "")) format-error tr
          where
            mapAccuml : {A B St : Set} → (St → A → St × B) → St → List A → St × List B
            mapAccuml f st []       = st , []
            mapAccuml f st (x ∷ xs) =
              let (st' , y)   = f st x
                  (st'' , ys) = mapAccuml f st' xs
              in st'' , y ∷ ys

            result : ∀ {E A St : Type} → (f : A → St) → (g : E → St) → Result E A → St
            result f g (Ok x) = f x
            result f g (Err x) = g x

        verifyChainTraceFromSlot : ℕ → Pair ℕ (Pair String String)
        verifyChainTraceFromSlot n = verifyChainTrace' (record s₀ { slot = n })
        {-# COMPILE GHC verifyChainTraceFromSlot as verifyChainTraceFromSlot #-}
