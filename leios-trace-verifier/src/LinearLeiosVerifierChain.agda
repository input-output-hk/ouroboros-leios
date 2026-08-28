open import Prelude.AssocList
open import Prelude.Result
open import Prelude.Errors

open import Leios.Config
open import Leios.SpecStructure using (SpecStructure)
open import Leios.Prelude hiding (id)

open import Data.Bool using (if_then_else_)
import Data.Char as C
import Data.Nat as N
import Data.Nat.Show as S
import Data.String as S
open import Agda.Builtin.Word using (Word64; primWord64ToNat)
open import Agda.Builtin.Char using (primCharToNat)
open import Foreign.Haskell.Pair

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
    CSlot        : Word64 → ChainEvent
    CEBForged    : String → Word64 → ChainEvent
    CEBAcquired  : String → Word64 → ChainEvent
    CVoted       : String → Word64 → ChainEvent
    CVoteAcquired : String → Word64 → ChainEvent
    CRBForged    : String → Word64 → ChainEvent
    CNodeIsLeader : Word64 → ChainEvent
    CAnnouncementAccepted : String → Word64 → ChainEvent
    CNotVoted    : String → Word64 → String → ChainEvent
    CChainExtended : Word64 → ChainEvent
    CMempoolRange : Word64 → Word64 → ChainEvent

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
        | ChainEvents.CChainExtended
        | ChainEvents.CMempoolRange
        ) #-}

  module _
    (numberOfParties : ℕ)
    (sutId : ℕ)
    (stakeDistr : List (Pair String ℕ))
    (Lhdr Lvote Ldiff : ℕ)
    -- The SUT's EB-production eligibility, as queried from the node, together with
    -- whether that answer is authoritative for the epoch about to be verified.
    -- Passed in per call rather than read from a mutable global: the caller chooses
    -- a different source per segment, and a top-level binding would be a CAF, fixed
    -- after its first evaluation.
    (winningSlots : List ℕ)
    (scheduleAuthoritative : Bool)
    -- The ranking block's body capacity in bytes ('maxBlockBodySize'). An EB is owed
    -- only when the mempool does not fit in the RB, so this is what separates a forge
    -- without an EB that is a violation from one that is ordinary behaviour.
    (maxRBBody : ℕ)
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
          ; Lhdr  = Lhdr
          ; Lvote = Lvote
          ; Ldiff = Ldiff
          -- CIP-0164 feasible value σc = 0.99 (committee stake coverage)
          ; σc-num = 99
          ; σc-den = 100
          }

      -- Slots at which the log shows the Leios subsystem itself doing something.
      -- Praos events — NodeIsLeader, RBForged — deliberately do not count.
      leiosActivitySlots : EventLog → List ℕ
      leiosActivitySlots []                               = []
      leiosActivitySlots (CEBForged _ s ∷ es)             = primWord64ToNat s ∷ leiosActivitySlots es
      leiosActivitySlots (CEBAcquired _ s ∷ es)           = primWord64ToNat s ∷ leiosActivitySlots es
      leiosActivitySlots (CAnnouncementAccepted _ s ∷ es) = primWord64ToNat s ∷ leiosActivitySlots es
      leiosActivitySlots (CVoted _ s ∷ es)                = primWord64ToNat s ∷ leiosActivitySlots es
      leiosActivitySlots (CVoteAcquired _ s ∷ es)         = primWord64ToNat s ∷ leiosActivitySlots es
      leiosActivitySlots (_ ∷ es)                         = leiosActivitySlots es

      minSlot : ℕ → List ℕ → ℕ
      minSlot m []       = m
      minSlot m (x ∷ xs) = minSlot (if x N.<ᵇ m then x else m) xs

      -- Leader slots at or after the first slot where Leios did anything.
      leaderSlotsFrom : ℕ → EventLog → List ℕ
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
      leaderSlots : EventLog → List ℕ
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
      winning-slots-of : ℙ (BlockType × ℕ)
      winning-slots-of =
        if scheduleAuthoritative
          then fromList (L.map (λ s → EB , s) winningSlots)
          else fromList (L.map (λ s → EB , s) (leaderSlots l))

      testParams : TestParams params
      testParams =
        record
          { sutId         = SUT-id
          ; winning-slots = winning-slots-of
          }

      open import Defaults params testParams using (d-SpecStructure; FFDBuffers; isb; hpe)
      open SpecStructure d-SpecStructure hiding (Hashable-EndorserBlock)

      open import Leios.Linear.Trace.Verifier d-SpecStructure params renaming (verifyTrace to checkTrace)

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
      synthTxs : String → List Tx
      synthTxs h = 0 ∷ L.map C.toℕ (S.toList h)

      mkEBrec : Party → String → Word64 → EndorserBlock
      mkEBrec p h s = record
        { slotNumber = primWord64ToNat s
        ; producerID = p
        ; lotteryPf  = tt
        ; txs        = synthTxs h
        ; signature  = tt
        }

      -- Status of the EB the chain currently announces, as the model tracks it
      -- across a voting window. This drives the 'Slot₂'/'BASE-LDG' ledger step
      -- ('annRB' below), which is the ONLY thing that sets the spec's
      -- 'currentRB' — and hence 'getCurrentEBHash', 'voteDeadline', and every
      -- role rule that reads them.
      --
      --   none            : no EB currently announced (default RB announces nothing)
      --   announcing h e  : the head RB announces EB 'h', whose election slot is 'e';
      --                     re-asserted each slot to keep the voting window open
      --                     until 'voteDeadline'. The election slot is carried
      --                     because it is what tells a tip advance *to* the
      --                     announcer from one *past* it — see 'CChainExtended'.
      --   superseded      : the chain has extended past the announcer (a later RB
      --                     is now the tip). The EB can no longer be certified, so
      --                     the window must close: 'closeSlot' emits ONE
      --                     non-announcing 'Slot₂' to overwrite 'currentRB', then
      --                     drops to 'none'. Merely forgetting the hash would stop
      --                     re-announcing but never reset the spec's 'currentRB',
      --                     leaving the window (wrongly) open.
      data EBStatus : Type where
        none       : EBStatus
        announcing : String → ℕ → EBStatus
        superseded : EBStatus

      -- Accumulator threaded through the chain events. Slot obligations are
      -- flushed when the next CSlot arrives (or at end of stream).
      record Accumulator : Type where
        field EB-refs     : AssocList String EndorserBlock
              EB-received : AssocList String ℕ
              FFD-blks    : List Blk
              curSlot     : ℕ
              started     : Bool
              curEB       : EBStatus
              -- Every EB the chain has announced, not only the latest. Two
              -- announcements can land inside a single slot, and closeSlot collapses
              -- a slot into one snapshot.
              announced   : List String
              -- (min , max) mempool bytes observed during the slot being accumulated.
              memRange    : Maybe (ℕ × ℕ)
              -- Whether the node forged a ranking block in this slot, which locates
              -- the mempool drain relative to its EB decision. See 'ebOwed'.
              forgedRB    : Bool
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

      Step = Action × (FFDT Out ⊎ BaseAbstract.BaseIOF B' In ⊎ IOT In)

      -- Hash of the EB registered under a given hash-string (identity on payload,
      -- see Defaults); [] if unknown.
      hashOf : Accumulator → String → Hash
      hashOf a h = case EB-refs a ⁉ h of λ where
        (just eb) → hash eb
        nothing   → []

      wasAnnounced : String → List String → Bool
      wasAnnounced h []       = false
      wasAnnounced h (x ∷ xs) = case h ≟ x of λ where
        (yes _) → true
        (no  _) → wasAnnounced h xs

      -- Emit the obligations for the slot being closed, chronologically.
      closeSlot : Accumulator → List Step
      closeSlot a =
        let s = curSlot a
            -- node.log carries no mempool contents, so re-establish a proposal set
            -- at the head of every slot. Without it 'ToPropose' stays empty,
            -- 'toProposeEB' is always 'nothing', and EB-Role's first premise is
            -- unsatisfiable — leaving every forged EB unverifiable. In a slot with
            -- a forge the payload has to be that of the forged EB itself, since
            -- EB-Role checks 'toProposeEB s π ≡ just eb'. 'Base₁' has no premises,
            -- records no upkeep and only overwrites 'ToPropose', so re-emitting it
            -- each slot is idempotent.
            --
            -- In a slot with no forge the proposal set says whether an EB was OWED.
            -- 'EB-Role' needs 'toProposeEB ≡ just eb', which holds exactly when the
            -- set is non-empty, so an empty one makes the rule inapplicable and
            -- 'Roles₂' licenses the abstention — the spec's own account of a node
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
            ebOwed : Bool
            ebOwed = case memRange a of λ where
              nothing           → false
              (just (mn , mx))  →
                maxRBBody N.<ᵇ (if forgedRB a then mx else mn)
            mempool : List Step
            mempool = case forgedEB a of λ where
              (just eb) → (Base₁-Action s , inj₂ (inj₂ (SubmitTxs (EndorserBlockOSig.txs eb)))) ∷ []
              nothing   → if ebOwed
                            then (Base₁-Action s , inj₂ (inj₂ (SubmitTxs placeholderTxs))) ∷ []
                            else (Base₁-Action s , inj₂ (inj₂ (SubmitTxs []))) ∷ []
            -- One 'Slot₂'/'BASE-LDG' step per slot, setting the spec's 'currentRB'
            -- (the head of 'RBs') — which is what 'getCurrentEBHash', and hence the
            -- voting window and every role rule reading it, is derived from.
            announceStep : Maybe Hash → List Step
            announceStep mh =
              (Slot₂-Action s , inj₂ (inj₁ (BaseAbstract.BASE-LDG
                (record { txs = [] ; announcedEB = mh ; ebCert = nothing ; slot = s } ∷ [])))) ∷ []
            -- Which EB to present as the chain head for this slot.
            --
            -- A vote cast in this slot wins over the announcement status, because
            -- closeSlot collapses a slot into one snapshot and the log timestamps
            -- only to slot granularity, so intra-slot order is unknowable. Two ways
            -- that bites:
            --
            --   * Two announcements in one slot — the node votes for an EB announced
            --     earlier, then forges its own and that is announced too, moving the
            --     head. Presenting the later one contradicts the vote emitted for the
            --     same slot: "442 : Err-VT-Role-premises: Current EB hash does not
            --     match".
            --   * The chain supersedes the announcer in the very slot the vote was
            --     cast. De-announcing here would refuse a vote we cannot show was
            --     illegal, so the de-announcement is deferred one slot ('nextEB').
            --
            -- Presenting the voted EB is not self-justifying: 'CVoted' records a vote
            -- only for an EB the chain actually announced, so a vote for an
            -- unannounced EB leaves 'votedEB' unset and no head is invented for it.
            --
            -- The residual weakening is deliberate: a vote cast in its legal slot for
            -- an EB whose announcer the chain had already superseded is accepted
            -- rather than refused. Refusing it would mean rejecting votes the log
            -- cannot prove were late, which is the false-positive class this file has
            -- been repeatedly corrected for. Votes genuinely outside the window are
            -- still caught, by VT-Role's timing premise.
            annRB : List Step
            annRB = case votedEB a of λ where
              (just (eb , _)) → announceStep (just (hash eb))
              nothing         → case curEB a of λ where
                -- No announcement to make: leave 'currentRB' as it stands.
                none             → []
                -- Re-assert the announcement so the window stays open this slot.
                (announcing h _) → announceStep (just (hashOf a h))
                -- The chain has extended past the announcer: overwrite 'currentRB'
                -- with a non-announcing RB so 'getCurrentEBHash ≡ nothing',
                -- 'voteDeadline ≡ 0', and the spec's own rules close the window
                -- (abstention becomes licensed by Roles₂, no vote is forced).
                superseded     → announceStep nothing
            ebRole : List Step
            ebRole = case forgedEB a of λ where
              (just eb) → (EB-Role-Action s eb , inj₁ FFDT.SLOT) ∷ []
              nothing   → (No-EB-Role-Action s , inj₁ FFDT.SLOT) ∷ []
            vtRole : List Step
            vtRole = case votedEB a of λ where
              (just (eb , slot')) → (VT-Role-Action s eb slot' , inj₁ FFDT.SLOT) ∷ []
              nothing             → (No-VT-Role-Action s , inj₁ FFDT.SLOT) ∷ []
        in mempool
           ++ annRB
           ++ ((Base₂-Action s , inj₁ FFDT.SLOT) ∷ ebRole)
           ++ vtRole
           ++ ((Slot₁-Action s , inj₁ (FFDT.FFD-OUT (blksToHeaderAndBodyList (FFD-blks a)))) ∷ [])

      -- Fake producer for acquired EBs: distinct for EBs sharing a slot (so an
      -- honest slot battle does not register as equivocation, which requires
      -- equal producers) and never the SUT (so acquired EBs cannot equivocate
      -- with the SUT's own forged EBs). Genuine equivocation by other pools is
      -- not detectable until the trace carries real producer identities.
      fakeProducer : Accumulator → Word64 → Party
      fakeProducer a s =
        let slotNat = primWord64ToNat s
            n = L.length (L.filter
                  (λ (_ , eb) → EndorserBlockOSig.slotNumber eb ≟ slotNat)
                  (Accumulator.EB-refs a))
        in from-id (if n N.<ᵇ sutId then n else suc n)

      traceEvent→action : Accumulator → ChainEvent → Accumulator × List Step
      traceEvent→action a (CSlot s) =
        if not (started a)
          then (record a { curSlot = primWord64ToNat s ; started = true } , [])
          else
            let steps = closeSlot a
                -- A 'superseded' de-announcement is emitted once, by the closeSlot
                -- above; the spec's 'currentRB' is then non-announcing, so drop to
                -- 'none'. 'announcing'/'none' persist across the slot.
                --
                -- Unless a vote was cast in this slot: 'annRB' presented the voted EB
                -- instead of de-announcing, so the de-announcement has not happened
                -- yet and 'superseded' must survive into the next slot to fire there.
                -- Dropping to 'none' here would retire the status without ever
                -- resetting 'currentRB', leaving the window open — the very failure
                -- the three-state status was introduced to avoid.
                nextEB = case curEB a of λ where
                  superseded → case votedEB a of λ where
                    (just _) → superseded
                    nothing  → none
                  st         → st
            in (record a
                  { curSlot = primWord64ToNat s
                  ; FFD-blks = []
                  ; curEB = nextEB
                  ; memRange = nothing
                  ; forgedRB = false
                  ; forgedEB = nothing
                  ; votedEB = nothing
                  } , steps)
      traceEvent→action a (CEBForged h s) =
        let eb = mkEBrec SUT-id h s
        in (record a { EB-refs = (h , eb) ∷ EB-refs a ; forgedEB = just eb } , [])
      -- Acquiring an EB means its body is in hand, which is what Slot₁ ingestion
      -- models. It says nothing about the EB being announced on the chain, so it must
      -- not set 'curEB': doing so made VT-Role possible for any EB the node merely
      -- fetched, and a node is right not to vote for one its chain never announced.
      traceEvent→action a (CEBAcquired h s) =
        let eb = mkEBrec (fakeProducer a s) h s
        in (record a
              { EB-refs = (h , eb) ∷ EB-refs a
              ; EB-received = (h , curSlot a) ∷ EB-received a
              ; FFD-blks = EB-Blk eb ∷ FFD-blks a
              } , [])
      -- The chain head announces this EB, which is what 'getCurrentEBHash' denotes.
      -- This, and not acquisition, is what makes the EB votable.
      traceEvent→action a (CAnnouncementAccepted h s) =
        (record a { curEB = announcing h (primWord64ToNat s) ; announced = h ∷ announced a } , [])
      -- Deliberately does not touch 'curEB': letting a vote establish its own
      -- precondition would make VT-Role self-justifying, hiding a node that voted for
      -- an EB its chain never announced.
      traceEvent→action a (CVoted h s)
        with wasAnnounced h (announced a) | EB-refs a ⁉ h | EB-received a ⁉ h
      ... | true | just eb | just slot' = (record a { votedEB = just (eb , slot') } , [])
      ... | _    | _       | _          = (a , [])
      traceEvent→action a (CVoteAcquired _ _) =
        (record a { FFD-blks = VT-Blk (tt ∷ []) ∷ FFD-blks a } , [])
      -- Not a step of its own: what it contributes is locating the mempool drain
      -- relative to the node's EB decision, which 'ebOwed' reads.
      traceEvent→action a (CRBForged h s) = (record a { forgedRB = true } , [])
      -- Consumed by 'leaderSlots' as the eligibility fallback, not as a step.
      traceEvent→action a (CNodeIsLeader _) = (a , [])
      -- The selected chain adopted a new tip. Mark the announcement 'superseded' so
      -- the next 'closeSlot' de-announces it via a non-announcing 'Slot₂', collapsing
      -- the spec's voteDeadline to 0. If nothing is currently announced, there is
      -- nothing to supersede.
      --
      -- Only a tip strictly beyond the announcer retires the EB. Adopting the
      -- announcer itself is the ordinary case — in Linear Leios the announcing RB and
      -- its EB share an election slot, and the node reports adopting its own block
      -- immediately after announcing it, so treating any tip advance as superseding
      -- closes every window in the slot it opened. Observed on a devnet as
      -- CAnnouncementAccepted at slot 20 followed by CChainExtended 20, which then
      -- retired an EB not votable until slot 23.
      traceEvent→action a (CChainExtended tip) =
        case curEB a of λ where
          (announcing h e) →
            if e N.<ᵇ primWord64ToNat tip
              then (record a { curEB = superseded } , [])
              else (record a { curEB = announcing h e } , [])
          _ → (a , [])
      -- A deliberate, protocol-legal abstention the node logged. It corroborates
      -- the retirement but drives no state itself: the window is closed by the
      -- chain extension (CChainExtended) or by the deadline, both via 'currentRB'.
      traceEvent→action a (CNotVoted _ _ _) = (a , [])
      -- The mempool range for the slot now ending; the parser emits it just ahead of
      -- the tick that closes that slot, so 'closeSlot' sees the right one.
      traceEvent→action a (CMempoolRange mn mx) =
        (record a { memRange = just (primWord64ToNat mn , primWord64ToNat mx) } , [])

      s₀ : LeiosState
      -- Register a key for every party: acquired EBs carry (fake) non-SUT
      -- producer IDs, and 'isValid' resolves the producer's key from this
      -- list — with only the SUT registered, every acquired EB header would
      -- be dropped as invalid and never reach EBs'.
      s₀ = initLeiosState tt exampleDistr (L.tabulate (λ i → (i , tt)))

      format-error : ∀ {αs s} → Err-verifyTrace αs s → Pair String String
      format-error x = errorMsg x , "error verifyChainTrace"

      showAction : Action → String
      showAction (EB-Role-Action n _)     = "EB-Role@"    ◇ show n
      showAction (VT-Role-Action n eb s') = "VT-Role@"    ◇ show n ◇ " eb@" ◇ show (slotNumber eb) ◇ " recv@" ◇ show s'
      showAction (No-EB-Role-Action n)    = "No-EB-Role@" ◇ show n
      showAction (No-VT-Role-Action n)    = "No-VT-Role@" ◇ show n
      showAction (Slot₁-Action n)         = "Slot1@"      ◇ show n
      showAction (Slot₂-Action n)         = "Slot2@"      ◇ show n
      showAction (Base₁-Action n)         = "Base1@"      ◇ show n
      showAction (Base₂-Action n)         = "Base2@"      ◇ show n
      showAction (Ftch-Action n)          = "Ftch@"       ◇ show n

      n₀ : ℕ → Accumulator
      n₀ st = record
        { EB-refs = [] ; EB-received = [] ; FFD-blks = [] ; curSlot = st
        ; started = false ; curEB = none ; announced = [] ; memRange = nothing
        ; forgedRB = false ; forgedEB = nothing ; votedEB = nothing }

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
              chron = L.concat l' ++ final
              αs = L.reverse chron
              tr = checkTrace αs s
              acts = L.map (λ a → showAction (proj₁ a)) chron
          in acts , result (λ _ → ("ok" , "")) format-error tr
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

        -- Streaming checkpoint: adjudicate only the slots already closed by a
        -- later CSlot, leaving the in-progress one to the next checkpoint.
        verifyChainTraceFromSlot : ℕ → Pair (List String) (Pair String String)
        verifyChainTraceFromSlot n = verifyChainTrace' false (record s₀ { slot = n })
        {-# COMPILE GHC verifyChainTraceFromSlot as verifyChainTraceFromSlot #-}

        -- Whole-log variant: additionally adjudicate the trailing slot. Sound only
        -- for a complete capture (e.g. a fixed event list in a test); on a stream
        -- truncated mid-slot it reports a spurious abstention violation.
        verifyChainTraceFinalFromSlot : ℕ → Pair (List String) (Pair String String)
        verifyChainTraceFinalFromSlot n = verifyChainTrace' true (record s₀ { slot = n })
        {-# COMPILE GHC verifyChainTraceFinalFromSlot as verifyChainTraceFinalFromSlot #-}
