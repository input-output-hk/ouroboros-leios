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
  verifySegment,
  runSegmented,
) where

import ChainEvents (ChainEvent (..))
import Control.Monad (when)
import Data.List (dropWhileEnd)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import LinearLeiosLib (verifyChainTraceFromSlot)

-- | Protocol timings, as the spec parameterises them.
data Timings = Timings
  { tLhdr :: Integer
  , tLvote :: Integer
  , tLdiff :: Integer
  , tValidityCheckTime :: Integer
  }

-- | Everything read from the chain for one epoch.
data ChainData = ChainData
  { cdWinningSlots :: Maybe [Integer]
  -- ^ The SUT's leadership schedule. 'Nothing' when the node could supply none at
  --   all — chiefly on a young network, where pool stake has not activated yet. Not
  --   fatal: eligibility then comes from the node's leadership record in the log.
  , cdNumParties :: Integer
  , cdStakeDistribution :: [(Text, Integer)]
  -- ^ Per-party stake, keyed @node-i@. Load-bearing beyond block production: vote
  --   eligibility is the CIP-0164 committee, computed from these figures.
  , cdSutIndex :: Integer
  , cdEpochLength :: Integer
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
  | -- | The segment holds slots the node led, but the log shows no Leios activity
    --   at all, so EB-role enforcement is suppressed for them. Carries how many
    --   such leader slots were seen.
    LeiosInactive Int
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
overlapSlots :: Timings -> Integer
overlapSlots ts = max (3 * tLhdr ts) (tValidityCheckTime ts) + tLhdr ts

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
        (tValidityCheckTime ts)
        (fromMaybe [] (cdWinningSlots cd))
        (segAuthoritative seg)
        prefix
        (segStart seg)

-- | Verify a node.log event stream one epoch-segment at a time.
--
--   At each boundary the chain data is re-fetched, since the schedule and stake
--   distribution are per-epoch, and a fresh segment is started — carrying
--   'overlapSlots' of the outgoing epoch so obligations crossing the seam are still
--   checked. Re-verification cost therefore stays bounded per epoch rather than
--   growing over the whole run.
--
--   A segment is re-verified from its start at every slot tick. That is quadratic
--   within an epoch, and load-bearing: the trailing slot is still in progress at a
--   checkpoint, so a conclusion drawn about it is provisional and only corrected by
--   redoing the prefix once its events have arrived.
runSegmented ::
  -- | Report progress; rendering and aborting are the caller's business.
  (Progress -> IO ()) ->
  Timings ->
  -- | Fetch chain data for the epoch containing the given boundary slot.
  (Integer -> IO ChainData) ->
  [ChainEvent] ->
  IO ()
runSegmented report ts query = loop [] Nothing []
 where
  overlap = overlapSlots ts

  loop tally mseg seen [] = do
    finishSeg mseg (reverse seen)
    report (Summary (reverse tally))
  loop tally mseg seen (ev : rest) = do
    report (Saw ev)
    case ev of
      CSlot s
        | Just seg <- mseg
        , toInteger s `div` cdEpochLength (segCD seg) == segEpoch seg -> do
            -- Same epoch: extend the segment, and periodically re-check it. Not at
            -- every tick — see 'checkpointEvery'.
            let seen' = ev : seen
            when (toInteger s `mod` checkpointEvery == 0) $
              checkSeg seg (reverse seen')
            loop tally mseg seen' rest
        | otherwise -> do
            -- First segment, or an epoch boundary. This tick is what completes the
            -- outgoing segment's last slot, so give that segment one final check
            -- with the tick appended; otherwise the last slot of every epoch would
            -- go unverified, a streaming check never adjudicating the slot still in
            -- progress.
            case mseg of
              Just old -> checkSeg old (reverse (ev : seen))
              Nothing -> pure ()
            -- No check on the new segment yet: its carried slots were just
            -- adjudicated by the outgoing one, and the boundary slot is in progress.
            let carry = carryAcross overlap (toInteger s) seen
            (seg, tally') <- newSegment tally (toInteger s) carry
            loop tally' (Just seg) (ev : carryEvents carry) rest
      _ -> loop tally mseg (ev : seen) rest

  newSegment tally boundary carry = do
    cd <- query boundary
    let ep = boundary `div` cdEpochLength cd
        seg =
          Segment
            { segEpoch = ep
            , segStart = carryStart carry
            , segCD = cd
            , segAuthoritative = segmentAuthoritative (carrySpans carry) ep cd
            }
    report (SegmentStarted seg (carrySpans carry))
    pure (seg, (ep, segAuthoritative seg) : tally)

  -- The EB-role gate lives in the translator, which cannot report. Say so wherever
  -- a prefix is verified, rather than letting leader slots be silently exempted.
  -- Both verification sites need this: a run too short to reach a periodic
  -- checkpoint is verified only at end of input.
  reportIfLeiosInactive prefix = do
    let led = length [() | CNodeIsLeader _ <- prefix]
    when (led > 0 && not (any isLeiosActivity prefix)) $
      report (LeiosInactive led)

  checkSeg seg prefix = do
    reportIfLeiosInactive prefix
    let (acts, (status, detail)) = verifySegment ts seg prefix
    if status == "ok"
      then report (Verified (length prefix) (length acts))
      else report (Violation (length prefix) acts status detail)

  finishSeg Nothing _ = report NothingToVerify
  finishSeg (Just seg) prefix = do
    reportIfLeiosInactive prefix
    let (acts, (status, detail)) = verifySegment ts seg prefix
    if status == "ok"
      then report (StreamEnded acts)
      else report (Violation (length prefix) acts status detail)
