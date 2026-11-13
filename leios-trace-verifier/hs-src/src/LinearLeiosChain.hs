{-# LANGUAGE OverloadedStrings #-}

-- | Segmented verification of a Leios node.log stream.
--
--   This is the driver: it splits the event stream at epoch boundaries, verifies each
--   segment against the Agda spec, and reports progress. It deliberately holds no
--   cardano-api dependency — the per-epoch chain data is supplied as an action, and
--   all output goes through a 'Progress' callback — so that the segmentation logic
--   can be exercised from tests with a stubbed query and a collecting reporter.
module LinearLeiosChain (
  Timings (..),
  ChainData (..),
  Segment (..),
  Progress (..),
  Carry (..),
  isCSlot,
  isLeiosActivity,
  checkpointEvery,
  overlapSlots,
  carryAcross,
  segmentAuthoritative,
  gateSuppressesAnObligation,
  surplusVotesPerSlot,
  verifySegment,
  runSegmented,
  boundaryWaitSlots,
  combinedSchedule,
  segmentInput,
) where

import ChainEvents (ChainEvent (..))
import Control.Monad (when)
import Data.List (dropWhileEnd)
import Data.Maybe (fromMaybe, isJust)
import Data.Text (Text)
import LinearLeiosLib (verifyChainStreamFromSlot, verifyChainTraceFromSlot)

-- | Protocol timings, as the spec parameterises them.
data Timings = Timings
  { tLhdr :: Integer
  , tLvote :: Integer
  , tLdiff :: Integer
  }

-- | Everything read from the chain for one epoch.
data ChainData = ChainData
  { cdWinningSlots :: Maybe [Integer]
  -- ^ The SUT's leadership schedule. 'Nothing' when the node could supply none at
  --   all — chiefly on a young network, where pool stake has not activated yet. Not
  --   fatal: eligibility then comes from the node's leadership record in the log.
  , cdNumParties :: Integer
  , cdStakeDistribution :: [Integer]
  -- ^ Per-party stake, by party index. Load-bearing beyond block production: vote
  --   eligibility is the CIP-0164 committee, computed from these figures.
  , cdSutIndex :: Integer
  , cdEpochLength :: Integer
  , cdMaxRBBody :: Integer
  -- ^ The ranking block's body capacity in bytes. Decides whether a forge without an
  --   EB was owed one: an EB is required only when the mempool could not have fitted
  --   into the RB.
  , cdNodeEpoch :: Integer
  -- ^ The epoch the node itself answered for. This is the epoch of the /chain tip/,
  --   not of the wall clock, so it lags whenever block production is sparse — which
  --   is why a queried schedule so often fails to describe the epoch under test.
  }

-- | A verification segment: one epoch, plus a carried tail of the previous one.
data Segment = Segment
  { segEpoch :: Integer
  , segStart :: Integer
  -- ^ First slot verification runs from, which is before the epoch boundary
  --   whenever a tail is carried across.
  , segCD :: ChainData
  , segAuthoritative :: Bool
  -- ^ Whether the queried schedule governs this segment. When it does not,
  --   eligibility comes from the log and the segment is still verified.
  }

-- | Everything the driver reports. Rendering, and the decision to abort on a
--   violation, belong to the caller.
data Progress
  = Saw ChainEvent
  | -- | A segment started, and whether it carries a tail of the previous epoch.
    SegmentStarted Segment Bool
  | -- | A segment verified: events in the prefix, actions adjudicated.
    Verified Int Int
  | -- | Events in the prefix, all actions, status, detail.
    Violation Int [Text] Text Text
  | -- | The input held no slot tick, so there was nothing to verify.
    NothingToVerify
  | -- | Input ended with the final check passing; the actions adjudicated.
    StreamEnded [Text]
  | -- | The segment holds slots the node led where the mempool rule would have
    --   demanded an EB, but the log shows no Leios activity at all, so EB-role
    --   enforcement is suppressed for them. Carries how many leader slots were seen.
    --   Not reported when the rule would have excused those slots anyway — the gate
    --   costs nothing then, and claiming otherwise buries the notes that matter.
    LeiosInactive Int
  | -- | The slot ticks jumped: the node emitted no leadership check for the slots
    --   between these two. Carries (last seen, next seen). Not a violation — a
    --   missing tick is usually the node being descheduled, and the verifier's own
    --   CPU load has been observed causing it, so blaming the node would be
    --   circular. Verification restarts after the gap instead.
    SlotGap Integer Integer
  | -- | Votes beyond the first within a single slot, summed over the prefix. Only
    --   one vote per slot can be adjudicated, so these went unexamined.
    SurplusVotesInSlot Int
  | -- | A slot tick that did not advance: a duplicate or out-of-order leadership
    --   check. Carries (last seen, the tick). Dropped rather than verified across.
    NonMonotonicSlot Integer Integer
  | -- | Slots whose mempool range straddled the RB capacity, so whether an EB was
    --   owed could not be settled and the slot was excused. This count is the
    --   measure of what the rule's one-sidedness costs on a given run: small means
    --   the EB-role check has teeth, large means it is mostly declining to look.
    EBOwedUndecided Int
  | -- | The prefix carried no mempool readings at all, so EB-role enforcement in
    --   non-forging slots lapsed entirely. Expected for logs predating the Mempool
    --   traces; on a current log it means the check is silently inactive.
    NoMempoolReadings
  | -- | Per epoch, whether eligibility came from the queried schedule.
    Summary [(Integer, Bool)]

-- | True iff the event is a slot tick, which is what bounds a verification step.
isCSlot :: ChainEvent -> Bool
isCSlot (CSlot _) = True
isCSlot _ = False

-- | True iff the event shows the Leios subsystem itself doing something. Praos
--   events — 'CNodeIsLeader', 'CRBForged' — deliberately do not count, since the
--   point is to tell whether Leios is running at all.
isLeiosActivity :: ChainEvent -> Bool
isLeiosActivity ev = case ev of
  CEBForged{} -> True
  CEBAcquired{} -> True
  CAnnouncementAccepted{} -> True
  CVoted{} -> True
  CVoteAcquired{} -> True
  _ -> False

-- | How many slots pass between periodic re-verifications within a segment.
--
--   A segment is re-verified from its start, so checking at every tick costs
--   O(n²) across an epoch. That is not merely slow: measured against a devnet at
--   @slotLength = 1@, by slot 370 each checkpoint was re-verifying ~2200 actions,
--   and the node — sharing the machine — began missing its own leadership checks,
--   stalling for 535 slots. The verifier was starving the node it observes and
--   then reporting the damage as a conformance violation. Checking every 20th slot
--   cuts that cost twentyfold.
--
--   Correctness is unaffected. A prefix check at tick n adjudicates every slot
--   below n, so no slot is skipped, only reported later; and the check at an epoch
--   boundary, plus the one at end of input, are never throttled. Re-verification
--   was once load-bearing, because a checkpoint's verdict on the slot still in
--   progress was provisional — but slots have been adjudicated only once complete
--   since the closeLast split, so redoing the prefix is now pure waste.
checkpointEvery :: Integer
checkpointEvery = 20

-- | How far back an obligation can reach. An EB with election slot @e@ becomes
--   votable in slot @e + (3 * Lhdr `max` validityCheckTime)@, and its acquisition may
--   lag the election by up to @Lhdr@, so carrying this many slots of the outgoing
--   epoch covers every obligation able to straddle a boundary.
--   The voting window is a range, not a single slot: it opens at
--   @ebSlot + 3 * Lhdr@ and the deadline is @ebSlot + 3 * Lhdr + Lvote@, after which
--   'VT-Defer' no longer licenses deferral and a vote is forced. So an obligation can
--   fall due as late as @3 * Lhdr + Lvote@ slots after the EB's own slot, and its
--   acquisition may lag the election by up to @Lhdr@.
--
--   Under the previous spec the window was the single slot
--   @ebSlot + (3 * Lhdr `max` validityCheckTime)@ and this was @3 * Lhdr + Lhdr@;
--   carrying that much now would drop votes falling due late in the window.
overlapSlots :: Timings -> Integer
overlapSlots ts = 3 * tLhdr ts + tLvote ts + tLhdr ts

-- | The tail of the outgoing epoch that a new segment carries across a boundary.
data Carry = Carry
  { carryEvents :: [ChainEvent]
  -- ^ Newest first, matching how the driver accumulates events.
  , carryStart :: Integer
  -- ^ Slot the new segment starts verifying from.
  , carrySpans :: Bool
  -- ^ Whether anything was carried, i.e. whether the segment spans two epochs.
  }

-- | Decide what to carry across an epoch boundary.
--
--   Without this a segment would begin on a fresh state, and an obligation raised
--   before the boundary but falling due after it would be invisible: the vote would
--   pass vacuously. The carried tail is trimmed so that it begins with a slot tick,
--   since an event ahead of the first tick would be attributed to the segment start
--   slot rather than to its own.
carryAcross :: Integer -> Integer -> [ChainEvent] -> Carry
carryAcross overlap boundary seen =
  Carry
    { carryEvents = carried
    , carryStart = earliestSlot boundary carried
    , carrySpans = not (null carried)
    }
 where
  carried = dropWhileEnd (not . isCSlot) (takeWhile notBefore seen)
  notBefore (CSlot sl) = toInteger sl >= boundary - overlap
  notBefore _ = True

-- | Earliest slot tick among a segment's events, or the given default if it has none.
earliestSlot :: Integer -> [ChainEvent] -> Integer
earliestSlot dflt es = case [toInteger sl | CSlot sl <- es] of
  [] -> dflt
  ss -> minimum ss

-- | Whether a queried schedule governs a segment: obtained at all, describing this
--   very epoch, and the segment lying wholly inside it.
--
--   A segment carrying an overlap spans two epochs, so no single epoch's schedule can
--   govern all of it — left authoritative, an EB forged in the carried tail would be
--   judged against the following epoch's lottery. An empty schedule is a legitimate
--   authoritative answer, which is why this cannot be inferred from the slot list
--   being empty.
segmentAuthoritative :: Bool -> Integer -> ChainData -> Bool
segmentAuthoritative spans ep cd =
  not spans && maybe False (const (ep == cdNodeEpoch cd)) (cdWinningSlots cd)

-- | Whether the EB-role gate actually costs anything on this prefix: some slot the
--   node led where the mempool rule would have demanded an EB.
--
--   Without this the gate reports "enforcement suppressed" whenever Leios is quiet,
--   which on a low-traffic network is every led slot — while the mempool rule had
--   already excused those same slots on its own terms, the mempool being far below
--   the ranking block's capacity. Saying "suppressed" there overstates the loss: the
--   verifier did look, and found nothing owed. The gate is only worth reporting when
--   it hides an obligation the rule would have raised.
--
--   Mirrors the translator's 'ebOwed': the maximum of the slot's mempool range where
--   the node forged (its own block drained the mempool after deciding), the minimum
--   otherwise.
gateSuppressesAnObligation :: Integer -> [ChainEvent] -> Bool
gateSuppressesAnObligation cap = any owed . slotGroups
 where
  -- A slot owns the events from its tick up to the next one, which is the grouping
  -- the translator uses — hence a mempool range emitted just ahead of a tick belongs
  -- to the slot then ending.
  slotGroups [] = []
  slotGroups (e : es) = let (g, rest) = break isCSlot es in (e : g) : slotGroups rest
  owed g =
    any isLeader g
      && case [(toInteger mn, toInteger mx) | CMempoolRange mn mx <- g] of
        [] -> False
        rs
          | any isRBForged g -> cap < maximum (map snd rs)
          | otherwise -> cap < minimum (map fst rs)
  isLeader (CNodeIsLeader _) = True
  isLeader _ = False
  isRBForged (CRBForged _ _) = True
  isRBForged _ = False

-- | How many votes beyond the first fall in the same slot, summed over the prefix.
--   Only one vote per slot can be adjudicated (VT-Role upkeep is per slot), so any
--   surplus goes unexamined; this counts it so the loss is visible rather than silent.
surplusVotesPerSlot :: [ChainEvent] -> Int
surplusVotesPerSlot = sum . map surplus . slotGroups
 where
  slotGroups [] = []
  slotGroups (e : es) = let (g, rest) = break isCSlot es in (e : g) : slotGroups rest
  surplus g = max 0 (length [() | CVoted _ _ <- g] - 1)

-- | Verify one segment's prefix against the spec.
verifySegment :: Timings -> Segment -> [ChainEvent] -> ([Text], (Text, Text))
verifySegment ts seg prefix =
  let cd = segCD seg
   in verifyChainTraceFromSlot
        (cdNumParties cd)
        (cdSutIndex cd)
        (cdStakeDistribution cd)
        (tLhdr ts)
        (tLvote ts)
        (tLdiff ts)
        (fromMaybe [] (cdWinningSlots cd))
        (segAuthoritative seg)
        (cdMaxRBBody cd)
        prefix
        (segStart seg)

-- | How long, at an epoch boundary, to wait for the node to answer for the new
--   epoch before verifying it with eligibility from the log instead.  The node
--   answers for the epoch of its chain tip, which crosses the boundary only with
--   the first block of the new epoch, so a query at the boundary tick almost always
--   describes the outgoing epoch.  Against an old log the node never catches up,
--   and this bounds what waiting costs there.
boundaryWaitSlots :: Integer
boundaryWaitSlots = 600

-- | The schedule governing a segment, if any: one obtained for its epoch and, if
--   the segment carries a tail of the previous epoch, that epoch's schedule too.
--   The carried slots are then judged against the schedule they belong to, so the
--   two schedules together govern the segment.
combinedSchedule :: Bool -> Integer -> Maybe [Integer] -> Integer -> ChainData -> Maybe [Integer]
combinedSchedule spans start prev ep cd
  | not (segmentAuthoritative False ep cd) = Nothing
  | not spans = cdWinningSlots cd
  | otherwise = do
      p <- prev
      new <- cdWinningSlots cd
      pure ([s | s <- p, s >= start] <> new)

-- | The events a streamed segment reads after its first tick: everything up to the
--   tick that ends it, which is included because it completes the segment's last
--   slot.  The rules are those of 'runSegmented', which reads the same events: a
--   tick that does not advance is dropped, and one that changes the epoch or skips
--   a slot ends the segment.  Being lazy, it is read as the log arrives.
segmentInput :: Integer -> Integer -> Integer -> [ChainEvent] -> [ChainEvent]
segmentInput epochLen ep = go
 where
  go _ [] = []
  go l (e@(CSlot sl) : es)
    | s <= l = go l es
    | s `div` epochLen /= ep || s /= l + 1 = [e]
    | otherwise = e : go s es
   where
    s = toInteger sl
  go l (e : es) = e : go l es

-- | What the streaming verifier says per slot tick read, and once at the end of
--   its input: the number of items the event yielded, and the verdict so far.
type StreamReport = (Integer, ([Text], (Text, Text)))

-- | A segment verified as it is read.
data Stream = Stream
  { stReports :: [StreamReport]
  -- ^ The verifier's reports still to be read.
  , stActions :: Int
  , stFailed :: Bool
  -- ^ A violation was reported; the verifier reads no further.
  , stSurplus :: Int
  -- ^ Votes beyond the first per slot, over the slots closed so far.
  , stVotes :: Int
  -- ^ Votes in the slot being read.
  , stStraddling :: Int
  , stRanges :: Bool
  }

-- | How the current segment is verified.
data Mode
  = -- | Eligibility from the log: re-verified from the segment start at checkpoints.
    Batch
  | -- | Eligibility from the node's schedule: verified as it is read.
    Streaming Stream
  | -- | At a boundary, waiting for the node to answer for the new epoch.  Carries
    --   the tail of the previous epoch, the previous segment's schedule if one
    --   governed it, and the boundary slot.
    Waiting Carry (Maybe [Integer]) Integer

-- | Verify a node.log event stream one epoch-segment at a time.
--
--   At each boundary the chain data is re-fetched, since the schedule and stake
--   distribution are per-epoch, and a fresh segment is started — carrying
--   'overlapSlots' of the outgoing epoch so obligations crossing the seam are still
--   checked.
--
--   A segment governed by the node's schedule is verified as it is read, each event
--   once (see 'verifyChainStream' in "LinearLeiosVerifierChain"), which is what
--   keeps up with a live node.  A segment whose eligibility comes from the log is
--   re-verified from its start at every checkpoint instead: the log-derived
--   eligibility is a parameter of the spec instance and reads the whole log, so a
--   verdict on a prefix can change as the log grows.  That is quadratic within an
--   epoch, and what checkpoint throttling exists for.
runSegmented ::
  -- | Report progress; rendering and aborting are the caller's business.
  (Progress -> IO ()) ->
  Timings ->
  -- | Fetch chain data for the epoch containing the given boundary slot.
  (Integer -> IO ChainData) ->
  [ChainEvent] ->
  IO ()
runSegmented report ts query = loop [] Nothing Nothing Batch 0 []
 where
  overlap = overlapSlots ts

  -- The state: the per-epoch tally, the current segment, the last tick, how the
  -- segment is verified, its event count, and its events newest first (in a
  -- streamed segment only the tail a boundary may carry).
  loop tally mseg _ mode n seen [] = do
    tally' <- case mode of
      Waiting carry _ boundary -> do
        -- The input ended before the node answered for the new epoch.
        (seg, tally') <- startSegment tally boundary carry Nothing
        finishSeg (Just seg) Batch n (reverse seen)
        pure tally'
      _ -> do
        finishSeg mseg mode n (reverse seen)
        pure tally
    report (Summary (reverse tally'))
  loop tally mseg mlast mode n seen (ev : rest) = do
    report (Saw ev)
    step tally mseg mlast mode n seen ev rest

  step tally mseg mlast mode n seen ev rest = case ev of
    -- A tick that does not advance — a duplicate, or out of order, as concatenated
    -- or overlapping logs produce. It is neither a continuation nor a gap, and
    -- without this it fell through to the boundary path and silently restarted a
    -- segment mid-epoch. There is nothing to verify backwards, so drop it and say
    -- so; the segment state is left exactly as it was.
    CSlot s
      | Just l <- mlast
      , toInteger s <= l -> do
          report (NonMonotonicSlot l (toInteger s))
          loop tally mseg mlast mode n seen rest
    CSlot s
      | Waiting carry prev boundary <- mode
      , Just l <- mlast
      , toInteger s == l + 1
      , toInteger s < boundary + boundaryWaitSlots -> do
          -- Still waiting: keep reading, and ask again now and then.
          let sl = toInteger s
              seen' = ev : seen
              n' = n + 1
          mcd <-
            if (sl - boundary) `mod` checkpointEvery == 0
              then Just <$> query boundary
              else pure Nothing
          case mcd >>= \cd -> (,) cd <$> combinedSchedule (carrySpans carry) (carryStart carry) prev (boundary `div` cdEpochLength cd) cd of
            Just (cd, ws) -> do
              (seg, tally') <- startSegmentWith tally boundary carry cd (Just ws)
              st <- openStream seg n' (reverse seen') (segmentInput (cdEpochLength cd) (segEpoch seg) sl rest)
              loop tally' (Just seg) (Just sl) st n' (trimSeen sl seen') rest
            Nothing -> loop tally mseg (Just sl) mode n' seen' rest
      | Waiting carry _ boundary <- mode -> do
          -- Waited long enough, or the ticks broke off: verify what was read with
          -- eligibility from the log, and take this tick as usual.
          (seg, tally') <- startSegment tally boundary carry Nothing
          step tally' (Just seg) mlast Batch n seen ev rest
    CSlot s
      | Just seg <- mseg
      , toInteger s `div` cdEpochLength (segCD seg) == segEpoch seg
      , maybe True (\l -> toInteger s == l + 1) mlast -> do
          -- Same epoch and the next slot in sequence: extend the segment.
          let sl = toInteger s
              seen' = ev : seen
              n' = n + 1
              atCheckpoint = sl `mod` checkpointEvery == 0
          case mode of
            Streaming st -> do
              st' <- advance n' (noteEvent seg ev st) 1
              when (atCheckpoint && not (stFailed st')) $ do
                reportNotes st'
                report (Verified n' (stActions st'))
              loop tally mseg (Just sl) (Streaming st') n' (trimSeen sl seen') rest
            _ -> do
              -- Periodically re-check it. Not at every tick — see 'checkpointEvery'.
              when atCheckpoint $ checkSeg seg (reverse seen')
              loop tally mseg (Just sl) mode n' seen' rest
      | otherwise -> do
          -- First segment, an epoch boundary, or a gap in the slot ticks. This tick
          -- is what completes the outgoing segment's last slot, so give that
          -- segment one final check with the tick appended; otherwise the last slot
          -- before every boundary would go unverified, a streaming check never
          -- adjudicating the slot still in progress.
          case (mseg, mode) of
            (Just old, Streaming st) -> do
              st' <- advanceAll (n + 1) (noteEvent old ev st)
              when (not (stFailed st')) $ do
                reportNotes st'
                report (Verified (n + 1) (stActions st'))
            (Just old, _) -> checkSeg old (reverse (ev : seen))
            _ -> pure ()
          -- A gap carries nothing. The spec advances one slot at a time, so a
          -- carried tail from before the gap would still contain it and the verifier
          -- would reject the jump — which is what a missing tick looked like before
          -- this: "8 : Err-Slot / Base₁-Action". Obligations straddling the gap are
          -- lost, unavoidably: there is no record of the slot to verify against.
          let sl = toInteger s
              gapped = maybe False (\l -> sl > l + 1) mlast
              carry
                -- Carrying nothing is exactly 'carryAcross' over no events.
                | gapped = carryAcross overlap sl []
                | otherwise = carryAcross overlap sl seen
              -- The outgoing segment's schedule, for the slots it hands over.
              prev = case (mseg, mode) of
                (Just old, Streaming _) | segAuthoritative old -> cdWinningSlots (segCD old)
                _ -> Nothing
              seen' = ev : carryEvents carry
              n' = length seen'
          case mlast of
            Just l | gapped -> report (SlotGap l sl)
            _ -> pure ()
          cd <- query sl
          let ep = sl `div` cdEpochLength cd
          case combinedSchedule (carrySpans carry) (carryStart carry) prev ep cd of
            -- No verdict on the new segment yet: its carried slots were just
            -- adjudicated by the outgoing one, and the boundary slot is in progress.
            Just ws -> do
              (seg, tally') <- startSegmentWith tally sl carry cd (Just ws)
              st <- openStream seg n' (reverse seen') (segmentInput (cdEpochLength cd) ep sl rest)
              loop tally' (Just seg) (Just sl) st n' (trimSeen sl seen') rest
            Nothing
              -- The node has not crossed the boundary yet, and its schedule will
              -- govern once it has: wait for it.
              | isJust (cdWinningSlots cd)
              , cdNodeEpoch cd < ep
              , not (carrySpans carry) || isJust prev ->
                  loop tally Nothing (Just sl) (Waiting carry prev sl) n' seen' rest
              | otherwise -> do
                  (seg, tally') <- startSegmentWith tally sl carry cd Nothing
                  loop tally' (Just seg) (Just sl) Batch n' seen' rest
    _ -> case mode of
      Streaming st
        | Just seg <- mseg ->
            loop tally mseg mlast (Streaming (noteEvent seg ev st)) (n + 1) (ev : seen) rest
      _ -> loop tally mseg mlast mode (n + 1) (ev : seen) rest

  -- Keep only what a boundary may carry: the events back to the tick 'overlap'
  -- slots ago.
  trimSeen sl = go
   where
    go [] = []
    go (e@(CSlot t) : es)
      | toInteger t <= sl - overlap = [e]
      | otherwise = e : go es
    go (e : es) = e : go es

  startSegment tally boundary carry ws = do
    cd <- query boundary
    startSegmentWith tally boundary carry cd ws

  -- A segment with a governing schedule ('Just') is authoritative, the schedule
  -- replacing the queried one, which covers the new epoch only.
  startSegmentWith tally boundary carry cd ws = do
    let ep = boundary `div` cdEpochLength cd
        seg =
          Segment
            { segEpoch = ep
            , segStart = carryStart carry
            , segCD = maybe cd (\s -> cd{cdWinningSlots = Just s}) ws
            , segAuthoritative = isJust ws
            }
    report (SegmentStarted seg (carrySpans carry))
    pure (seg, (ep, segAuthoritative seg) : tally)

  -- Start the streaming verifier on a segment whose events so far, oldest first,
  -- are 'already', and read its reports for the ticks among them.
  openStream seg n already more = do
    let cd = segCD seg
        reports =
          verifyChainStreamFromSlot
            (cdNumParties cd)
            (cdSutIndex cd)
            (cdStakeDistribution cd)
            (tLhdr ts)
            (tLvote ts)
            (tLdiff ts)
            (fromMaybe [] (cdWinningSlots cd))
            True
            (cdMaxRBBody cd)
            []
            (segStart seg)
            (already <> more)
        st0 =
          Stream
            { stReports = reports
            , stActions = 0
            , stFailed = False
            , stSurplus = 0
            , stVotes = 0
            , stStraddling = 0
            , stRanges = False
            }
    Streaming <$> advance n (foldl (flip (noteEvent seg)) st0 already) (length [() | CSlot _ <- already])

  -- Read the reports of the next k ticks, stopping at a violation.
  advance :: Int -> Stream -> Int -> IO Stream
  advance _ st 0 = pure st
  advance n st k
    | stFailed st = pure st
    | otherwise = case stReports st of
        [] -> pure st
        ((items, (acts, (status, detail))) : rs) -> do
          let st' = st{stReports = rs, stActions = stActions st + fromInteger items}
          if status == "ok"
            then advance n st' (k - 1)
            else do
              report (Violation n acts status detail)
              pure st'{stFailed = True}

  -- Read the reports to the end of the verifier's input.
  advanceAll n st = advance n st (length (stReports st))

  -- The notes' counts, kept as the events are read rather than over the prefix.
  noteEvent seg ev st = case ev of
    CSlot _ -> st{stSurplus = stSurplus st + max 0 (stVotes st - 1), stVotes = 0}
    CVoted _ _ -> st{stVotes = stVotes st + 1}
    CMempoolRange mn mx ->
      let cap = cdMaxRBBody (segCD seg)
          straddles = toInteger mn <= cap && cap < toInteger mx
       in st{stRanges = True, stStraddling = stStraddling st + fromEnum straddles}
    _ -> st

  reportNotes st = do
    let surplus = stSurplus st + max 0 (stVotes st - 1)
    when (surplus > 0) $ report (SurplusVotesInSlot surplus)
    if not (stRanges st)
      then report NoMempoolReadings
      else when (stStraddling st > 0) $ report (EBOwedUndecided (stStraddling st))

  -- The EB-role gate lives in the translator, which cannot report. Say so wherever a
  -- prefix is verified, rather than letting leader slots be silently exempted. Both
  -- verification sites need this: a run too short to reach a periodic checkpoint is
  -- verified only at end of input.
  --
  -- Only when the gate actually hides an obligation, though — see
  -- 'gateSuppressesAnObligation'. On a quiet network the mempool rule excuses those
  -- slots on its own terms, and reporting suppression there claims a loss that was
  -- not incurred.
  reportIfLeiosInactive seg prefix = do
    let led = length [() | CNodeIsLeader _ <- prefix]
        cap = cdMaxRBBody (segCD seg)
    when
      ( led > 0
          -- The gate only exists on the log-derived branch: where the queried
          -- schedule governs, eligibility never consults 'leaderSlots' at all, so
          -- nothing is being suppressed and saying so would be simply untrue.
          && not (segAuthoritative seg)
          && not (any isLeiosActivity prefix)
          && gateSuppressesAnObligation cap prefix
      )
      $ report (LeiosInactive led)

  -- A slot can hold more than one CVoted, but the spec records VT-Role upkeep once
  -- per slot, so only one vote per slot can ever be adjudicated. The translator keeps
  -- the first; this counts what that leaves unexamined. Purely syntactic over the
  -- event stream — it mirrors no spec rule.
  reportSurplusVotes prefix = do
    let perSlot = surplusVotesPerSlot prefix
    when (perSlot > 0) $ report (SurplusVotesInSlot perSlot)

  -- An EB is owed only when the mempool could not have fitted in the ranking block,
  -- and the reading is a range, so a range straddling the capacity leaves the
  -- question open. Those slots are excused, which is the safe direction but is also
  -- lost coverage — so say how much of it there is rather than let it go unseen.
  reportMempoolGaps seg prefix = do
    let cap = cdMaxRBBody (segCD seg)
        ranges = [(toInteger mn, toInteger mx) | CMempoolRange mn mx <- prefix]
        straddling = length [() | (mn, mx) <- ranges, mn <= cap, cap < mx]
    if null ranges
      then report NoMempoolReadings
      else when (straddling > 0) $ report (EBOwedUndecided straddling)

  checkSeg seg prefix = do
    reportIfLeiosInactive seg prefix
    reportSurplusVotes prefix
    reportMempoolGaps seg prefix
    let (acts, (status, detail)) = verifySegment ts seg prefix
    if status == "ok"
      then report (Verified (length prefix) (length acts))
      else report (Violation (length prefix) acts status detail)

  finishSeg Nothing _ _ _ = report NothingToVerify
  finishSeg (Just _) (Streaming st) n _ = do
    st' <- advanceAll n st
    when (not (stFailed st')) $ do
      reportNotes st'
      report (StreamEnded [])
  finishSeg (Just seg) _ _ prefix = do
    reportIfLeiosInactive seg prefix
    reportSurplusVotes prefix
    reportMempoolGaps seg prefix
    let (acts, (status, detail)) = verifySegment ts seg prefix
    if status == "ok"
      then report (StreamEnded acts)
      else report (Violation (length prefix) acts status detail)
