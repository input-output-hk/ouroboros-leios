open import Prelude.AssocList
open import Prelude.Errors

open import Leios.Config
open import Leios.SpecStructure using (SpecStructure)
open import Leios.Prelude hiding (id)

open import Data.Bool using (if_then_else_)
import Data.Char as C
import Data.Nat as N
import Data.String as S
open import Agda.Builtin.Word using (primWord64ToNat; primWord64FromNat)
open import Agda.Builtin.Char using (primCharToNat)
open import Foreign.Haskell.Pair

open import Parser using (SlotNo; Bytes)
open import TraceTypes

open import Tactic.Defaults
open import Tactic.Derive.Show

module LinearLeiosVerifierChain where

  postulate
    error : {A : Set} → String → A
  {-# FOREIGN GHC import Data.Text #-}
  {-# COMPILE GHC error = \ _ s -> error (unpack s) #-}

  -- | A Leios event extracted from a cardano-node tracing log (node.log), keyed
  --   by the EB hash. Mirrors 'ChainEvents.ChainEvent' on the Haskell side.
  data ChainEvent : Type where
    CSlot                 : SlotNo → ChainEvent
    CEBForged             : EBId → SlotNo → ChainEvent
    CEBAcquired           : EBId → SlotNo → ChainEvent
    CVoted                : EBId → SlotNo → ChainEvent
    CVoteAcquired         : EBId → SlotNo → ChainEvent
    CRBForged             : RBId → SlotNo → ChainEvent
    CNodeIsLeader         : SlotNo → ChainEvent
    CAnnouncementAccepted : EBId → SlotNo → ChainEvent
    CNotVoted             : EBId → SlotNo → String → ChainEvent
    CAdopted              : RBId → SlotNo → Maybe RBId → ChainEvent
    CNewTip               : RBId → SlotNo → ChainEvent
    CMempoolRange         : Bytes → Bytes → ChainEvent
    CUndetailed           : ChainEvent

  {-# FOREIGN GHC import qualified ChainEvents #-}
  {-# COMPILE GHC ChainEvent = data ChainEvents.ChainEvent
        ( ChainEvents.CSlot
        | ChainEvents.CEBForged
        | ChainEvents.CEBAcquired
        | ChainEvents.CVoted
        | ChainEvents.CVoteAcquired
        | ChainEvents.CRBForged
        | ChainEvents.CNodeIsLeader
        | ChainEvents.CAnnouncementAccepted
        | ChainEvents.CNotVoted
        | ChainEvents.CAdopted
        | ChainEvents.CNewTip
        | ChainEvents.CMempoolRange
        | ChainEvents.CUndetailed
        ) #-}

  module _
    (numberOfParties : ℕ)
    (sutId : ℕ)
    -- Each party's stake, by party index. Pool names are arbitrary, so the caller
    -- numbers the pools; the SUT is party 'sutId'.
    (stakeDistr : List ℕ)
    (Lhdr Lvote Ldiff : ℕ)
    -- The SUT's EB-production eligibility, as queried from the node, together with
    -- whether that answer is authoritative for the epoch about to be verified.
    -- Passed in per call rather than read from a mutable global: the caller chooses
    -- a different source per segment, and a top-level binding would be a CAF, fixed
    -- after its first evaluation.
    (winningSlots : List SlotNumber)
    (scheduleAuthoritative : Bool)
    -- The ranking block's body capacity in bytes ('maxBlockBodySize'). An EB is owed
    -- only when the mempool does not fit in the RB, so this is what separates a forge
    -- without an EB that is a violation from one that is ordinary behaviour.
    (maxRBBody : ByteCount)
    where

    from-id : ℕ → Fin numberOfParties
    from-id n =
      case n <? numberOfParties of λ where
        (yes p) → #_ n {numberOfParties} {fromWitness p}
        (no _) → error $ "Conversion to Fin not possible! " ◇ show n ◇ " / " ◇ show numberOfParties

    Party : Type
    Party = Fin numberOfParties

    SUT-id : Party
    SUT-id = from-id sutId

    instance
      numberOfParties-NonZero : NonZero numberOfParties
      numberOfParties-NonZero with numberOfParties ≟ 0
      ... | yes _ = error "Number of parties is 0"
      ... | no ¬p = ≢-nonZero ¬p

    open FunTot (completeFin numberOfParties) (maximalFin numberOfParties)

    nodeId : String → Fin numberOfParties
    nodeId _ = SUT-id

    stakeDistribution' : TotalMap (Fin numberOfParties) ℕ
    stakeDistribution' =
      if L.length stakeDistr N.≡ᵇ numberOfParties
        then Fun⇒TotalMap (λ i → maybe (λ x → x) 0 (L.head (L.drop (toℕ i) stakeDistr)))
        else error ("Expected a stake for each of the " ◇ show numberOfParties
                     ◇ " parties, got " ◇ show (L.length stakeDistr))

    EventLog = List ChainEvent

    module _ (l : EventLog) where

      params : Params
      params =
        record
          { networkParams =
              record
                { numberOfParties   = numberOfParties
                ; stakeDistribution = stakeDistribution'
                }
          ; Lhdr  = Lhdr
          ; Lvote = Lvote
          ; Ldiff = Ldiff
          -- CIP-0164 feasible value σc = 0.99 (committee stake coverage)
          ; σc-num = 99
          ; σc-den = 100
          }

      -- Slots at which the log shows the Leios subsystem itself doing something.
      -- Praos events — NodeIsLeader, RBForged — deliberately do not count.
      leiosActivitySlots : EventLog → List SlotNumber
      leiosActivitySlots []                               = []
      leiosActivitySlots (CEBForged _ s ∷ es)             = primWord64ToNat s ∷ leiosActivitySlots es
      leiosActivitySlots (CEBAcquired _ s ∷ es)           = primWord64ToNat s ∷ leiosActivitySlots es
      leiosActivitySlots (CAnnouncementAccepted _ s ∷ es) = primWord64ToNat s ∷ leiosActivitySlots es
      leiosActivitySlots (CVoted _ s ∷ es)                = primWord64ToNat s ∷ leiosActivitySlots es
      leiosActivitySlots (CVoteAcquired _ s ∷ es)         = primWord64ToNat s ∷ leiosActivitySlots es
      leiosActivitySlots (_ ∷ es)                         = leiosActivitySlots es

      minSlot : SlotNumber → List SlotNumber → SlotNumber
      minSlot m []       = m
      minSlot m (x ∷ xs) = minSlot (if x N.<ᵇ m then x else m) xs

      -- Leader slots at or after the first slot where Leios did anything.
      leaderSlotsFrom : SlotNumber → EventLog → List SlotNumber
      leaderSlotsFrom from []                     = []
      leaderSlotsFrom from (CNodeIsLeader s ∷ es) =
        let n = primWord64ToNat s
        in if n N.<ᵇ from
             then leaderSlotsFrom from es
             else n ∷ leaderSlotsFrom from es
      leaderSlotsFrom from (_ ∷ es)               = leaderSlotsFrom from es

      -- Slots in which the node won the Praos lottery, gated on Leios having shown
      -- signs of life.
      --
      -- NodeIsLeader is a Praos event. Treating it as EB-production eligibility rests
      -- on the spec assuming canProduceEB holds exactly when the node can make a
      -- ranking block, and that only holds while Leios is actually running. Observed
      -- against a devnet: 31 slots in, with no EB forged, acquired, announced or voted
      -- anywhere in the log, the node was Praos leader at slot 9 and forged a plain
      -- ranking block — and No-EB-Role was rejected, because eligibility had been
      -- inferred from a Praos event alone while the subsystem was still warming up.
      --
      -- Only the negative inference is gated. A forged EB is still verified wherever
      -- it appears, since accepting one needs no assumption about the subsystem being
      -- up; and because the gate compares slot numbers rather than log positions, a
      -- leader slot whose own EB forge is the first Leios activity still qualifies.
      --
      -- The node emits no positive readiness event, and its "wait for leios ready"
      -- message recurs a dozen times in runs that do forge EBs, so that cannot serve
      -- as the gate.
      leaderSlots : EventLog → List SlotNumber
      leaderSlots es = case leiosActivitySlots es of λ where
        []       → []
        (a ∷ as) → leaderSlotsFrom (minSlot a as) es

      -- EB-production eligibility. The queried leadership schedule is authoritative
      -- and is used whenever it applies to the epoch under test. It does not always:
      -- pool stake takes two epochs to activate, and a node answers only for its own
      -- current epoch, which in practice trails the epoch being verified. In those
      -- gaps fall back to the node's own leadership record from the log, which covers
      -- every epoch the log spans and is not circular with the EB events being
      -- checked. Note an authoritative schedule may legitimately be empty, so that
      -- case must not be mistaken for an absent one — hence the explicit flag.
      --
      -- Voting eligibility is unaffected: it follows the CIP-0164 committee in
      -- Defaults, computed from the stake distribution rather than a per-slot lottery.
      winning-slots-of : ℙ SlotNumber
      winning-slots-of =
        if scheduleAuthoritative
          then fromList winningSlots
          else fromList (leaderSlots l)

      testParams : TestParams params
      testParams =
        record
          { sutId         = SUT-id
          ; winning-slots = winning-slots-of
          }

      -- Every slot in which the node led, for the Praos node, which mints in
      -- exactly these.  Unlike 'leaderSlots' it is not gated on Leios activity:
      -- that gate guards EB obligations, and a ranking block is forged whether
      -- or not Leios is running.
      allLeaderSlots : EventLog → List SlotNumber
      allLeaderSlots []                     = []
      allLeaderSlots (CNodeIsLeader s ∷ es) = primWord64ToNat s ∷ allLeaderSlots es
      allLeaderSlots (_ ∷ es)               = allLeaderSlots es

      rb-slots-of : ℙ SlotNumber
      rb-slots-of =
        if scheduleAuthoritative
          then fromList winningSlots
          else fromList (allLeaderSlots l)

      open import Defaults params testParams rb-slots-of using
        (d-SpecStructure; FFDBuffers; isb; hpe; d-blockHash;
         module PraosNode; mkPraosBlock; genesisHash; tipHash;
         node⁻; module Check; praosHeader; initNodeState)
      open SpecStructure d-SpecStructure hiding (Hashable-EndorserBlock)

      open import Leios.Linear.Trace.Verifier d-SpecStructure params hiding (verifyTrace)

      open Params params
      open Types params
      open FFD hiding (_-⟦_/_⟧⇀_)
      open GenFFD
      open import CategoricalCrypto hiding (_∘_)

      data Blk : Type where
        EB-Blk : EndorserBlock → Blk
        VT-Blk : List Vote → Blk
        RB-Blk : RankingBlock → Blk

      -- Marker proposal set for a slot in which the node forged nothing but an EB
      -- was owed (the log records mempool sizes, never contents). Needs only to be
      -- non-empty, so that 'toProposeEB' returns 'just' and a failing EB-Role is
      -- attributable to 'canProduceEB' alone. Where no EB was owed the proposal set
      -- is empty instead — see 'ebOwed'.
      placeholderTxs : List Tx
      placeholderTxs = 0 ∷ []

      -- EB payload, derived injectively from the EB hash string. 'Defaults' hashes
      -- an EB to its transaction list, so a constant payload collapses every EB to
      -- a single spec-level hash: 'getCurrentEBHash' then matches whichever EB
      -- happens to come first in 'EBs'', and the second vote of a run is rejected
      -- as 'Already voted' because 'VotedEBs' already holds that hash. The leading
      -- zero keeps the list non-empty, EBs being non-empty per the CIP.
      synthTxs : EBId → List Tx
      synthTxs h = 0 ∷ L.map C.toℕ (S.toList h)

      mkEBrec : Party → EBId → SlotNo → EndorserBlock
      mkEBrec p h s = record
        { slotNumber = primWord64ToNat s
        ; producerID = p
        ; lotteryPf  = tt
        ; txs        = synthTxs h
        ; signature  = tt
        }

      -- The spec-level hash of the EB with this hash string.  It is fixed by the
      -- string alone, so a ranking block can announce an EB the node has not
      -- acquired yet.
      ebHash : EBId → Hash
      ebHash h = hash (mkEBrec SUT-id h (primWord64FromNat 0))

      -- Accumulator threaded through the chain events. Slot obligations are
      -- flushed when the next CSlot arrives (or at end of stream).
      record Accumulator : Type where
        field EB-refs     : AssocList EBId EndorserBlock
              EB-received : AssocList EBId SlotNumber
              FFD-blks    : List Blk
              curSlot     : SlotNumber
              started     : Bool
              -- (min , max) mempool bytes observed during the slot being accumulated.
              memRange    : Maybe (ByteCount × ByteCount)
              forgedEB    : Maybe EndorserBlock
              votedEB     : Maybe (EndorserBlock × SlotNumber)
              -- ── The Praos node ──
              -- Each ranking block of the log, by its hash: its slot and the
              -- party it is minted as.  The log names no producers, so the
              -- blocks of a slot other than the SUT's are numbered, skipping
              -- the SUT, which keeps them apart in the block tree.
              ids         : AssocList RBId (SlotNumber × Party)
              -- The blocks the node adopted before the SUT forged in this slot,
              -- latest first: the node forges at the start of a slot, so these
              -- are what the Praos node absorbs in this slot's round.
              inbox       : List PraosNode.Block
              -- The blocks it adopted after the SUT forged, which wait for the
              -- next round.
              late        : List PraosNode.Block
              -- The ranking block the SUT forged in this slot, with the hash of
              -- the tip it extended.
              forgedRB    : Maybe (RBId × SlotNumber × Hash)
              -- The tip of the node's selected chain.
              tipNow      : Maybe RBId
              -- The EB each ranking block announces, by its election slot.
              annBySlot   : AssocList SlotNumber EBId
              -- The EB the chain head announced when the slot opened: the one a
              -- vote of the slot can be for.
              headEB      : Maybe EBId

      open Accumulator

      instance
        _ = Show-List
        _ = Show-×

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

      -- The log names the blocks the SUT forges, and the tip of its selected
      -- chain; it records the blocks it adopts by hash, slot and parent.
      open Check praosHeader tipHash using (NodeHint; nodeᶜ)

      -- Why the Praos node rejects a step: in the round of a slot, it mints
      -- other blocks than the SUT forged, or selects another chain.
      nodeMsg : NodeHint → String
      nodeMsg nothing = "the Praos node rejects a request of Leios"
      nodeMsg (just (n , bs , t)) =
        "the Praos node's round of slot " ◇ show n ◇ " does not match the log, in which the SUT "
          ◇ minted bs ◇ " and its chain ends in " ◇ show t
        where
          minted : List (Hash × SlotNumber) → String
          minted [] = "mints no block"
          minted bs = "mints (parent, slot) " ◇ show bs

      open import LinearLeiosStack d-SpecStructure params node⁻ nodeᶜ nothing nodeMsg using
        (Stack; Item; entry; deliver; base; ffdᵢ; voteᵢ; ioᵢ; verifyItems)

      blksToHeaderAndBodyList : List Blk → List (FFDA.Header ⊎ FFDA.Body)
      blksToHeaderAndBodyList []              = []
      blksToHeaderAndBodyList (EB-Blk eb ∷ l) = inj₁ (GenFFD.ebHeader eb) ∷ blksToHeaderAndBodyList l
      blksToHeaderAndBodyList (VT-Blk vt ∷ l) = inj₁ (GenFFD.vtHeader vt) ∷ blksToHeaderAndBodyList l
      blksToHeaderAndBodyList (RB-Blk _ ∷ l)  = blksToHeaderAndBodyList l

      -- ── Blocks for the Praos node ──

      -- The hash of a ranking block in the block tree, from the slot and the
      -- party it is minted as (see 'd-blockHash').
      rbHash : SlotNumber → Party → Hash
      rbHash sl p = d-blockHash sl p (record { announcedEB = nothing ; txsOrEbCert = inj₁ [] })

      -- The tree hash of the block with this log hash.  A block the log has
      -- not shown, such as the parent of the first block of a segment, is
      -- genesis: the segment's chain is rooted there.
      treeHash : Accumulator → RBId → Hash
      treeHash a h = case ids a ⁉ h of λ where
        (just (sl , p)) → rbHash sl p
        nothing         → genesisHash

      tipTreeHash : Accumulator → Hash
      tipTreeHash a = maybe (treeHash a) genesisHash (tipNow a)

      -- The ranking block of a slot: it announces the EB of its election slot,
      -- if any.  The log does not say what else it carries.
      rbAt : Accumulator → SlotNumber → RankingBlock
      rbAt a sl = record
        { announcedEB = ebHash <$> annBySlot a ⁉ sl
        ; txsOrEbCert = inj₁ [] }

      -- The party the next block of a slot is minted as: the blocks of the slot
      -- seen so far are numbered, skipping the SUT.
      nextParty : Accumulator → SlotNumber → Party
      nextParty a sl =
        let n = L.length (L.filter (λ (_ , (sl′ , _)) → sl′ ≟ sl) (ids a))
        in from-id (if n N.<ᵇ sutId then n else suc n)

      isCurrentHead : EBId → Maybe EBId → Bool
      isCurrentHead h (just h′) = case h ≟ h′ of λ where
        (yes _) → true
        (no  _) → false
      isCurrentHead _ nothing = false

      -- Emit the obligations for the slot being closed, chronologically.
      closeSlot : Accumulator → List Item
      closeSlot a =
        let s = curSlot a
            -- node.log carries no mempool contents, so re-establish a proposal set
            -- at the head of every slot. Without it 'ToPropose' stays empty,
            -- 'toProposeEB' is always 'nothing', and EB-Role's first premise is
            -- unsatisfiable — leaving every forged EB unverifiable. In a slot with
            -- a forge the payload has to be that of the forged EB itself, since
            -- EB-Role checks 'toProposeEB s π ≡ just eb'. 'Mempool' has no premises,
            -- records no upkeep and only overwrites 'ToPropose', so re-emitting it
            -- each slot is idempotent.
            --
            -- In a slot with no forge the proposal set says whether an EB was OWED.
            -- 'EB-Role' needs 'toProposeEB ≡ just eb', which holds exactly when the
            -- set is non-empty, so an empty one makes the rule inapplicable and
            -- 'No-EB-Role' licenses the abstention — the spec's own account of a node
            -- with nothing to put in an EB.
            --
            -- Owed iff the mempool could not have fitted in the ranking block. The
            -- reading is a range, and which end of it corresponds to the node's
            -- decision depends on whether the node forged here.
            --
            -- No forge: the snapshot instant is unobservable, so take the MINIMUM.
            -- That makes the test one-sided — a range straddling the capacity is
            -- treated as not owed, so an indeterminate slot is excused rather than
            -- flagged. A false violation ends the whole verification session, while a
            -- missed one costs only that slot's coverage.
            --
            -- Forge: the node's own block drained the mempool, and that drain is
            -- causally after the decision, so the minimum is the post-decision state
            -- and the MAXIMUM is what the node actually saw. Taking the minimum here
            -- would excuse a leader slot precisely because its own block emptied the
            -- mempool — the very case this rule exists to catch. The maximum is the
            -- slot's opening value, which the parser seeds the range with.
            --
            -- No reading at all (a log without the Mempool traces) is likewise not
            -- owed: EB-role enforcement then lapses rather than firing on a guess.
            forged = maybe (λ _ → true) false (forgedRB a)
            ebOwed : Bool
            ebOwed = case memRange a of λ where
              nothing           → false
              (just (mn , mx))  →
                maxRBBody N.<ᵇ (if forged then mx else mn)
            submit : List Tx → List Item
            submit txs = entry (Mempool-Action s) (ioᵢ (SubmitTxs txs)) ∷ []
            mempool : List Item
            mempool = case forgedEB a of λ where
              (just eb) → submit (EndorserBlockOSig.txs eb)
              nothing   → submit (if ebOwed then placeholderTxs else [])
            ebRole : List Item
            ebRole = case forgedEB a of λ where
              (just eb) → entry (EB-Role-Action s eb) (ffdᵢ FFDT.SLOT) ∷ []
              nothing   → entry (No-EB-Role-Action s) (ffdᵢ FFDT.SLOT) ∷ []
            -- The Praos node's round of the slot: it absorbs the blocks adopted
            -- before the SUT forged, and mints if it leads.  It must mint the
            -- block the SUT forged, on the tip the SUT had then, and select the
            -- chain the SUT selected: ending in its own block if it forged one,
            -- and else in the tip of the log.
            --
            -- The node's clock trails the Leios slot by one, so there is no
            -- round for slot 0, whose blocks wait for slot 1.
            round : NodeHint
            round = case forgedRB a of λ where
              (just (_ , sl , parent)) → just (s , (parent , sl) ∷ [] , rbHash sl SUT-id)
              nothing                  → just (s , [] , tipTreeHash a)
            praos : List Item
            praos = if s N.≡ᵇ 0 then [] else deliver round (inbox a) ∷ []
            vtRole : List Item
            vtRole = case votedEB a of λ where
              (just (eb , slot')) → entry (VT-Role-Action s eb slot') (ffdᵢ FFDT.SLOT) ∷ []
              nothing             → entry (No-VT-Role-Action s) (ffdᵢ FFDT.SLOT) ∷ []
        -- 'ebRole' precedes the ranking-block step: 'Base₁' and 'Base₂' require the
        -- EB role to be settled for the slot ('hasUpkeep EB-Role'), so that the RB
        -- announces the EB actually diffused rather than 'nothing'.  The Praos
        -- round follows it, minting the RB Leios submitted there.  'Slot' reads
        -- the chain the round left for the next slot.
        in mempool
           ++ ebRole
           ++ base s ∷ praos
           ++ vtRole
           ++ entry (Slot-Action s) (ffdᵢ (FFDT.FFD-OUT (blksToHeaderAndBodyList (FFD-blks a)))) ∷ []

      -- Fake producer for acquired EBs: distinct for EBs sharing a slot (so an
      -- honest slot battle does not register as equivocation, which requires
      -- equal producers) and never the SUT (so acquired EBs cannot equivocate
      -- with the SUT's own forged EBs). Genuine equivocation by other pools is
      -- not detectable until the trace carries real producer identities.
      fakeProducer : Accumulator → SlotNo → Party
      fakeProducer a s =
        let slotNat = primWord64ToNat s
            n = L.length (L.filter
                  (λ (_ , eb) → EndorserBlockOSig.slotNumber eb ≟ slotNat)
                  (Accumulator.EB-refs a))
        in from-id (if n N.<ᵇ sutId then n else suc n)

      -- The EB the head of the selected chain announces.
      headOf : Accumulator → Maybe EBId
      headOf a = tipNow a >>= λ h → ids a ⁉ h >>= λ (sl , _) → annBySlot a ⁉ sl

      -- An EB reaches the spec as its header ('EB-Blk' diffuses 'ebHeader'), and
      -- Slot ingestion records it in EBs' with the current slot: the slot' that
      -- VT-Role bounds by Lhdr.  The node logs the header (the announcement) and
      -- the body separately, the body often slots later, so the EB is received
      -- at whichever comes first, and once.  This says nothing about the EB being
      -- announced on the chain: that is the ranking block's, which the Praos node
      -- selects.
      receive : Accumulator → EBId → SlotNo → Accumulator
      receive a h s = case EB-refs a ⁉ h of λ where
        (just _) → a
        nothing  →
          let eb = mkEBrec (fakeProducer a s) h s
          in record a
               { EB-refs = (h , eb) ∷ EB-refs a
               ; EB-received = (h , curSlot a) ∷ EB-received a
               ; FFD-blks = EB-Blk eb ∷ FFD-blks a
               }

      traceEvent→action : Accumulator → ChainEvent → Accumulator × List Item
      traceEvent→action a (CSlot s) =
        if not (started a)
          then (record a { curSlot = primWord64ToNat s ; started = true ; headEB = headOf a } , [])
          else
            let steps = closeSlot a
            in (record a
                  { curSlot = primWord64ToNat s
                  ; FFD-blks = []
                  ; memRange = nothing
                  ; forgedEB = nothing
                  ; votedEB = nothing
                  ; inbox = (if curSlot a N.≡ᵇ 0 then late a ++ inbox a else late a)
                  ; late = []
                  ; forgedRB = nothing
                  ; headEB = headOf a
                  } , steps)
      traceEvent→action a (CEBForged h s) =
        let eb = mkEBrec SUT-id h s
        in (record a { EB-refs = (h , eb) ∷ EB-refs a ; forgedEB = just eb } , [])
      -- The EB was received: see 'receive'.
      traceEvent→action a (CEBAcquired h s) = (receive a h s , [])
      -- The ranking block of this election slot announces the EB, and the
      -- announcement carries its header.
      traceEvent→action a (CAnnouncementAccepted h s) =
        (receive (record a { annBySlot = (primWord64ToNat s , h) ∷ annBySlot a }) h s , [])
      -- 'closeSlot' emits at most one VT-Role per slot, the spec recording VT-Role
      -- upkeep once per slot, so where a slot holds several votes only one can be
      -- adjudicated.  The one for the EB the chain head announced when the slot
      -- opened is the one the spec can discharge; the driver counts the others.
      -- Whether a vote was legal at all is for VT-Role to decide, against the
      -- chain the Praos node selected.
      traceEvent→action a (CVoted h s)
        with EB-refs a ⁉ h | EB-received a ⁉ h
      ... | just eb | just slot' =
              case votedEB a of λ where
                nothing  → (record a { votedEB = just (eb , slot') } , [])
                (just _) → if isCurrentHead h (headEB a)
                             then (record a { votedEB = just (eb , slot') } , [])
                             else (a , [])
      ... | _       | _          = (a , [])
      -- The spec does not inspect vote contents, and the log names neither the
      -- voter nor the signed RB.
      traceEvent→action a (CVoteAcquired _ _) =
        (record a { FFD-blks = VT-Blk ((SUT-id , []) ∷ []) ∷ FFD-blks a } , [])
      -- The SUT forged a ranking block on the tip it had selected.  It is the
      -- block the Praos node mints, under the SUT's identity.
      traceEvent→action a (CRBForged h s) =
        let sl = primWord64ToNat s
        in (record a
              { forgedRB = just (h , sl , tipTreeHash a)
              ; ids = (h , (sl , SUT-id)) ∷ ids a
              } , [])
      -- Consumed by 'leaderSlots' and 'allLeaderSlots', not as a step.
      traceEvent→action a (CNodeIsLeader _) = (a , [])
      -- The node adopted a ranking block into its selected chain.  The SUT's own
      -- blocks are the Praos node's to mint; any other goes to the Praos node,
      -- in this slot's round if the SUT has not forged yet, else in the next.
      traceEvent→action a (CAdopted h s mp) =
        case ids a ⁉ h of λ where
          (just _) → (a , [])
          nothing  →
            let sl  = primWord64ToNat s
                p   = nextParty a sl
                blk = mkPraosBlock (maybe (treeHash a) genesisHash mp) sl (rbAt a sl) p
                a′  = record a { ids = (h , (sl , p)) ∷ ids a }
            in case forgedRB a of λ where
                 nothing  → (record a′ { inbox = blk ∷ inbox a } , [])
                 (just _) → (record a′ { late = blk ∷ late a } , [])
      traceEvent→action a (CNewTip h _) = (record a { tipNow = just h } , [])
      -- A deliberate, protocol-legal abstention the node logged. It drives no
      -- state: VT-Role and No-VT-Role decide against the selected chain.
      traceEvent→action a (CNotVoted _ _ _) = (a , [])
      -- The mempool range for the slot now ending; the parser emits it just ahead of
      -- the tick that closes that slot, so 'closeSlot' sees the right one.
      traceEvent→action a (CMempoolRange mn mx) =
        (record a { memRange = just (primWord64ToNat mn , primWord64ToNat mx) } , [])
      -- The driver refuses a log without the adopted headers before it gets here.
      traceEvent→action a CUndetailed = (a , [])

      s₀ : LeiosState
      -- Register a key for every party: acquired EBs carry (fake) non-SUT
      -- producer IDs, and 'isValid' resolves the producer's key from this
      -- list — with only the SUT registered, every acquired EB header would
      -- be dropped as invalid and never reach EBs'.
      s₀ = initLeiosState tt stakeDistribution' (L.tabulate (λ i → (i , tt)))

      -- The stack in Leios state 's', with the Praos node's clock one slot
      -- behind (see 'LinearLeiosStack').
      stack₀ : LeiosState → Machine.State Stack
      stack₀ s = ((tt , record initNodeState { clock = LeiosState.slot s ∸ 1 }) , tt) , s

      check : LeiosState → List Item → Pair String String
      check s αs = [ (λ e → (e , "error verifyChainTrace")) , (λ _ → ("ok" , "")) ]′ (verifyItems (stack₀ s) αs)

      showAction : Action → String
      showAction (EB-Role-Action n _)     = "EB-Role@"    ◇ show n
      showAction (VT-Role-Action n eb s') = "VT-Role@"    ◇ show n ◇ " eb@" ◇ show (slotNumber eb) ◇ " recv@" ◇ show s'
      showAction (No-EB-Role-Action n)    = "No-EB-Role@" ◇ show n
      showAction (No-VT-Role-Action n)    = "No-VT-Role@" ◇ show n
      showAction (Slot-Action n)          = "Slot@"       ◇ show n
      showAction (Chain-Action n)         = "Chain@"      ◇ show n
      showAction (Mempool-Action n)       = "Mempool@"    ◇ show n
      showAction (Base₁-Action n)         = "Base1@"      ◇ show n
      showAction (Base₂-Action n)         = "Base2@"      ◇ show n
      showAction (Cert₁-Action n)         = "Cert1@"      ◇ show n
      showAction (Cert₂-Action n)         = "Cert2@"      ◇ show n
      showAction (Cert₃-Action n)         = "Cert3@"      ◇ show n
      showAction (Fetch-Action n)         = "Fetch@"      ◇ show n

      -- The ranking-block step is named by the verifier (see 'LinearLeiosStack').
      showItem : Item → String
      showItem (entry a _)   = showAction a
      showItem (deliver h _) = "Praos@" ◇ maybe (λ (n , _) → show n) "?" h
      showItem (base n)      = "Base@" ◇ show n

      n₀ : SlotNumber → Accumulator
      n₀ st = record
        { EB-refs = [] ; EB-received = [] ; FFD-blks = [] ; curSlot = st
        ; started = false ; memRange = nothing ; forgedEB = nothing ; votedEB = nothing
        ; ids = [] ; inbox = [] ; late = [] ; forgedRB = nothing ; tipNow = nothing
        ; annBySlot = [] ; headEB = nothing }

      opaque
        unfolding List-Model

        -- 'closeLast' decides whether the trailing slot is adjudicated. A slot is
        -- complete only once a later CSlot has closed it in 'traceEvent→action';
        -- the slot still in progress has not had its CEBForged/CVoted events read
        -- yet, so emitting its obligations asserts an abstention that the rest of
        -- the input may contradict. Streaming checkpoints must pass 'false'; only
        -- a caller that knows the log ends on a slot boundary may pass 'true'.
        verifyChainTrace' : Bool → LeiosState → Pair (List String) (Pair String String)
        verifyChainTrace' closeLast s =
          let (aFinal , l') = mapAccuml traceEvent→action (n₀ (LeiosState.slot s)) l
              final = if closeLast then (if started aFinal then closeSlot aFinal else []) else []
              αs = L.concat l' ++ final
          in L.map showItem αs , check s αs
          where
            mapAccuml : {A B St : Set} → (St → A → St × B) → St → List A → St × List B
            mapAccuml f st []       = st , []
            mapAccuml f st (x ∷ xs) =
              let (st' , y)   = f st x
                  (st'' , ys) = mapAccuml f st' xs
              in st'' , y ∷ ys

        -- Streaming checkpoint: adjudicate only the slots already closed by a
        -- later CSlot, leaving the in-progress one to the next checkpoint.
        verifyChainTraceFromSlot : SlotNumber → Pair (List String) (Pair String String)
        verifyChainTraceFromSlot n = verifyChainTrace' false (record s₀ { slot = n })
        {-# COMPILE GHC verifyChainTraceFromSlot as verifyChainTraceFromSlot #-}

        -- Whole-log variant: additionally adjudicate the trailing slot. Sound only
        -- for a complete capture (e.g. a fixed event list in a test); on a stream
        -- truncated mid-slot it reports a spurious abstention violation.
        verifyChainTraceFinalFromSlot : SlotNumber → Pair (List String) (Pair String String)
        verifyChainTraceFinalFromSlot n = verifyChainTrace' true (record s₀ { slot = n })
        {-# COMPILE GHC verifyChainTraceFinalFromSlot as verifyChainTraceFinalFromSlot #-}
