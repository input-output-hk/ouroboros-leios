open import Prelude.AssocList
open import Prelude.Errors

open import Leios.Config
open import Leios.SpecStructure using (SpecStructure)
open import Leios.Prelude hiding (id)

open import Data.Bool using (if_then_else_)
import Data.Nat.Show as S
import Data.String as S
open import Agda.Builtin.Word using (primWord64ToNat)
open import Agda.Builtin.Char using (primCharToNat)
open import Foreign.Haskell.Pair

open import Tactic.Defaults
open import Tactic.Derive.Show

open import Parser
open import TraceTypes

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
  postulate leadershipSchedule : List SlotNumber
  {-# FOREIGN GHC import qualified LeadershipSchedule #-}
  {-# COMPILE GHC leadershipSchedule = LeadershipSchedule.leadershipScheduleSlots #-}

  module _
    (numberOfParties : ℕ)
    (sutId : ℕ)
    (stakeDistr : List (Pair String ℕ))
    (Lhdr Lvote Ldiff : ℕ)
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

    -- EB-production winning slots harvested from the trace.  Voting slots are
    -- not collected: 'winning-slots' governs EB production only, since VT
    -- eligibility is the CIP-0164 committee rather than a per-slot lottery.
    winningSlot : TraceEvent → Maybe SlotNumber
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
    ... | yes _ = just (primWord64ToNat s)
    ... | no _  = nothing
    winningSlot record { message = VTBundleGenerated _ _ _ _ _ _ }  = nothing
    winningSlot record { message = RBGenerated _ _ _ _ _ _ _ _ _ }  = nothing

    -- The slot of a ranking block the SUT mints.
    rbSlot : TraceEvent → Maybe SlotNumber
    rbSlot record { message = RBGenerated p _ s _ _ _ _ _ _ }
      with p ≟ SUT
    ... | yes _ = just (primWord64ToNat s)
    ... | no _  = nothing
    rbSlot _ = nothing

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
          ; Lhdr  = Lhdr
          ; Lvote = Lvote
          ; Ldiff = Ldiff
          -- CIP-0164 feasible value σc = 0.99 (committee stake coverage)
          ; σc-num = 99
          ; σc-den = 100
          }

      -- EB-production eligibility ("winning") slots for the SUT.  When a
      -- leadership schedule is supplied (e.g. from `cardano-cli query
      -- leadership-schedule`), each scheduled slot counts as an EB winning slot;
      -- this is authoritative and non-circular.  When no schedule is given the
      -- legacy behaviour is used: harvest the winning slots from the trace.
      --
      -- Voting (VT) eligibility is NOT taken from here: it follows the
      -- deterministic, epoch-fixed committee of CIP-0164 (see Defaults.sortition),
      -- computed from the stake distribution rather than a per-slot lottery.
      winning-slots-of : ℙ SlotNumber
      winning-slots-of =
        if L.null leadershipSchedule
          then fromList (L.catMaybes (L.map winningSlot l))
          else fromList leadershipSchedule

      -- The slots in which the SUT leads and mints a ranking block, for the
      -- Praos node.  A leadership schedule is the ranking-block lottery, so
      -- when one is supplied it gives these slots as well; otherwise they are
      -- harvested from the SUT's 'RBGenerated' events.  They are not EB
      -- winning slots: a leader may put the transactions in the ranking block
      -- and announce no EB.
      rb-slots-of : ℙ SlotNumber
      rb-slots-of =
        if L.null leadershipSchedule
          then fromList (L.catMaybes (L.map rbSlot l))
          else fromList leadershipSchedule

      testParams : TestParams params
      testParams =
        record
          { sutId         = SUT-id
          ; winning-slots = winning-slots-of
          }

      open import Defaults params testParams rb-slots-of using
        (d-SpecStructure; FFDBuffers; isb; hpe;
         module PraosNode; mkPraosBlock; praosBlockHash; genesisHash;
         node⁻; module Check; praosHeader; initNodeState)
      open SpecStructure d-SpecStructure hiding (Hashable-EndorserBlock)

      open import Leios.Linear.Trace.Verifier d-SpecStructure params hiding (verifyTrace)

      open Params params
      open Types params
      open FFD hiding (_-⟦_/_⟧⇀_)
      open GenFFD
      open import CategoricalCrypto hiding (_∘_)

      Party : Type
      Party = Fin (Params.numberOfParties params)

      data Blk : Type where
        EB-Blk : EndorserBlock → Blk
        VT-Blk : List Vote → Blk
        RB-Blk : RankingBlock → Blk

      record Accumulator : Type where
        field EB-refs : AssocList EBId EndorserBlock
              EB-received : AssocList EBId SlotNumber
              VT-refs : AssocList VTBundleId (List Vote)
              RB-refs : AssocList RBId RankingBlock
              -- Praos-header data per RB (prev-hash, slot, producer); the
              -- payload lives in RB-refs and may still be corrected by a
              -- later EBGenerated, so blocks are materialized on demand.
              RB-meta : AssocList RBId (Hash × SlotNumber × Party)
              -- the blocks the SUT received in the current slot, latest
              -- first, for the next delivery to the Praos node
              inbox : List PraosNode.Block
              FFD-blks : List Blk
              currentSlot : SlotNumber

      open Accumulator

      -- ── Blocks for the Praos node, built from trace events ──

      buildBlk : Accumulator → RBId → Maybe PraosNode.Block
      buildBlk l i with RB-meta l ⁉ i | RB-refs l ⁉ i
      ... | just (ph , sl , pid) | just rb = just (mkPraosBlock ph sl rb pid)
      ... | _ | _ = nothing

      parentHash : Accumulator → Nullable BlockRef → Hash
      parentHash l p with unwrap p
      ... | nothing  = genesisHash
      ... | just ref = maybe praosBlockHash genesisHash (buildBlk l (BlockRef.id ref))

      instance
        _ = Show-List
        _ = Show-×

      -- The trace records the blocks the SUT mints, by parent and slot, but
      -- not its selected chain.
      open Check praosHeader (λ _ → tt) using (NodeHint; nodeᶜ)

      -- Why the Praos node rejects a step: in the round of a slot, it mints
      -- other blocks than the SUT's 'RBGenerated' events of the slot, given
      -- by parent and slot.
      nodeMsg : NodeHint → String
      nodeMsg nothing = "the Praos node rejects a request of Leios"
      nodeMsg (just (n , bs , _)) =
        "the Praos node's round of slot " ◇ show n ◇ " does not match the trace, in which the SUT "
          ◇ minted bs
        where
          minted : List (Hash × SlotNumber) → String
          minted [] = "mints no block"
          minted bs = "mints (parent, slot) " ◇ show bs

      -- Linear Leios stacked on the Praos node: the node, not the trace,
      -- answers Leios's requests for the ledger and takes its blocks, and
      -- the trace's record of the blocks it mints is checked.
      open import LinearLeiosStack d-SpecStructure params node⁻ nodeᶜ nothing nodeMsg using
        (Stack; Item; entry; deliver; base; ffdᵢ; voteᵢ; ioᵢ; verifyItems)

      instance
        Show-EBCert : Show (Maybe EBCert)
        Show-EBCert .show nothing  = "No EBCert"
        Show-EBCert .show (just c) = show c

        Show-TxsOrEBCert : Show (List Tx ⊎ EBCert)
        Show-TxsOrEBCert .show (inj₁ txs)  = "Txs " S.++ show txs
        Show-TxsOrEBCert .show (inj₂ cert) = "EBCert " S.++ show cert

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
      negative-events-EB : List Blk → SlotNo → List Item
      negative-events-EB l s
        with Any.any? isEB? l
      ... | yes _ = []
      ... | no  _ = entry (No-EB-Role-Action (primWord64ToNat s)) (ffdᵢ FFDT.SLOT) ∷ []

      negative-events-VT : List Blk → SlotNo → List Item
      negative-events-VT l s
        with Any.any? isVT? l
      ... | yes _ = []
      ... | no  _ = entry (No-VT-Role-Action (primWord64ToNat s)) (ffdᵢ FFDT.SLOT) ∷ []

      -- The blocks the SUT minted in slot 'n', by parent and slot, in the
      -- order of the log.  A slot's 'RBGenerated' precedes its 'Slot' event.
      mintedAt : Accumulator → SlotNumber → List (Hash × SlotNumber)
      mintedAt l n = L.reverse (L.mapMaybe sut (RB-meta l))
        where
          sut : RBId × (Hash × SlotNumber × Party) → Maybe (Hash × SlotNumber)
          sut (_ , ph , sl , p) with p ≟ SUT-id | sl ≟ n
          ... | yes _ | yes _ = just (ph , sl)
          ... | _     | _     = nothing

      -- The Praos node's round of slot 'n', after Leios submitted its block
      -- for it: the blocks the SUT received in the slot, and minting, which
      -- must give the blocks the SUT minted in the slot.  The node adds the
      -- blocks of a delivery from the last to the first, so the inbox, which
      -- holds the latest first, is delivered as it stands.  The node's clock
      -- trails the Leios slot by one, so it has no round for slot 0, whose
      -- blocks wait for slot 1.
      delivery : Accumulator → SlotNumber → Accumulator × List Item
      delivery l zero    = l , []
      delivery l (suc n) =
        record l { inbox = [] } ,
          deliver (just (suc n , mintedAt l (suc n) , tt)) (inbox l) ∷ []

      traceEvent→action : Accumulator → TraceEvent → Accumulator × List Item
      traceEvent→action l record { message = Slot p s }
        with p ≟ SUT
      ... | yes _ =
        let (l' , delivered) = delivery l (primWord64ToNat s)
        in record l' { FFD-blks = [] ; currentSlot = suc (currentSlot l) } ,
          negative-events-EB (FFD-blks l) s ++ negative-events-VT (FFD-blks l) s ++
            base (primWord64ToNat s)
          ∷ delivered
          ++ entry (Slot-Action (primWord64ToNat s)) (ffdᵢ (FFDT.FFD-OUT (blksToHeaderAndBodyList (FFD-blks l))))
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
        record l { FFD-blks = EB-Blk eb ∷ FFD-blks l ; EB-received = (i , currentSlot l) ∷ (EB-received l) } , entry (EB-Role-Action (currentSlot l) eb) (ffdᵢ FFDT.SLOT) ∷ []
      ... | _ | _ | _ = l , []

      -- VTs
      -- The spec does not inspect vote contents, so the voted EB's hash is left empty.
      traceEvent→action l record { message = VTBundleGenerated p i s _ _ vts } =
        let vt = map (const (nodeId p , [])) (elems vts)
        in record l { VT-refs = (i , vt) ∷ VT-refs l } , []
      traceEvent→action l record { message = VTBundleReceived _ p _ _ i _ }
        with p ≟ SUT | VT-refs l ⁉ i | EB-refs l ⁉ i | EB-received l ⁉ i
      ... | yes _ | just vt | just eb | just slot' = record l { FFD-blks = VT-Blk vt ∷ FFD-blks l } , entry (VT-Role-Action (currentSlot l) eb slot') (ffdᵢ FFDT.SLOT) ∷ []
      ... | _ | _ | _ | _ = l , []

      -- RBs
      traceEvent→action l record { message = RBGenerated p i s _ eb _ _ parent txs } =
        let ebCert = unwrap eb >>= λ b → EB-refs l ⁉ BlockRef.id (Endorsement.eb b) >>= λ eb' → return (hash eb')
            rb = record
                   { announcedEB = nothing -- this is set in EBReceived
                   -- An RB carries either a certificate or transactions, never both.
                   ; txsOrEbCert = maybe inj₂ (inj₁ (map primWord64ToNat txs)) ebCert
                   }
            l' = record l
                   { RB-refs = (i , rb) ∷ RB-refs l
                   ; RB-meta = (i , (parentHash l parent , primWord64ToNat s , nodeId p)) ∷ RB-meta l
                   }
        -- The SUT's own blocks are minted by the Praos node; the log's
        -- record of them only serves as parents of blocks it receives.
        in l' , []

      traceEvent→action l record { message = RBReceived s p _ _ i _ }
        with p ≟ SUT | buildBlk l i
      ... | yes _ | just blk = record l { inbox = blk ∷ inbox l } , []
      ... | _ | _ = l , []

      -- TXs
      traceEvent→action l record { message = TXGenerated _ _ } = l , []
      traceEvent→action l record { message = TXReceived i _ p }
        with p ≟ SUT
      ... | yes _ = l , entry (Mempool-Action (currentSlot l)) (ioᵢ (SubmitTxs (concatList (map primCharToNat (S.toList i)) ∷ []))) ∷ []
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
      -- Register a key for every party: acquired EBs carry (fake) non-SUT
      -- producer IDs, and 'isValid' resolves the producer's key from this
      -- list — with only the SUT registered, every acquired EB header would
      -- be dropped as invalid and never reach EBs'.
      s₀ = initLeiosState tt exampleDistr (L.tabulate (λ i → (i , tt)))

      -- The stack in Leios state 's', with the Praos node's clock one slot
      -- behind (see 'delivery').
      stack₀ : LeiosState → Machine.State Stack
      stack₀ s = ((tt , record initNodeState { clock = LeiosState.slot s ∸ 1 }) , tt) , s

      check : LeiosState → List Item → Pair String String
      check s αs = [ (λ e → (e , "error verifyTrace")) , (λ _ → ("ok" , "")) ]′ (verifyItems (stack₀ s) αs)

      opaque
        unfolding List-Model

        verifyTrace' : LeiosState → Pair ℕ (Pair String String)
        verifyTrace' s =
          let n₀ = record { EB-refs = [] ; EB-received = [] ; VT-refs = [] ; RB-refs = [] ; RB-meta = [] ; inbox = [] ; FFD-blks = [] ; currentSlot = LeiosState.slot s }
              l' = proj₂ $ mapAccuml traceEvent→action n₀ l
              αs = L.concat l'
          in L.length αs , check s αs
          where
            mapAccuml : {A B S : Set} → (S → A → S × B) → S → List A → S × List B
            mapAccuml f s []       = s , []
            mapAccuml f s (x ∷ xs) =
              let (s' , y)   = f s x
                  (s'' , ys) = mapAccuml f s' xs
              in s'' , y ∷ ys

        verifyTrace : Pair ℕ (Pair String String)
        verifyTrace = verifyTrace' s₀
        {-# COMPILE GHC verifyTrace as verifyTrace #-}

        verifyTraceFromSlot : SlotNumber → Pair ℕ (Pair String String)
        verifyTraceFromSlot n = verifyTrace' (record s₀ { slot = n })
        {-# COMPILE GHC verifyTraceFromSlot as verifyTraceFromSlot #-}
