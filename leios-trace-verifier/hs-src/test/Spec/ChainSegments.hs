{-# LANGUAGE OverloadedStrings #-}

-- | Tests for the segmentation driver in "LinearLeiosChain": how the event stream is
--   split at epoch boundaries, and what that means for obligations crossing a seam.
--
--   These drive the same 'runSegmented' the executable does, with the chain query
--   stubbed and a collecting reporter in place of the renderer, so the segmentation
--   decisions are exercised rather than reimplemented.
module Spec.ChainSegments (
  chainSegments,
) where

import ChainEvents (ChainEvent (..))
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.Text (Text)
import LinearLeiosChain (
  Carry (..),
  ChainData (..),
  Progress (..),
  Segment (..),
  Timings (..),
  carryAcross,
  checkpointEvery,
  overlapSlots,
  runSegmented,
  segmentAuthoritative,
 )
import Test.Hspec (Spec, describe, it, shouldBe, shouldNotBe)

-- | The timings the chain app uses. An announced EB's voting window opens at
--   @ebSlot + 3 * Lhdr == ebSlot + 3@ and its deadline is
--   @ebSlot + 3 * Lhdr + Lvote == ebSlot + 7@, so the carry width is 8.
timings :: Timings
timings = Timings{tLhdr = 1, tLvote = 4, tLdiff = 7}

-- | Ten-slot epochs, so a fixture can cross a boundary in a handful of events. Three
--   equal-stake pools with the SUT last, and no obtainable schedule, which is the
--   common case against a devnet.
stubChainData :: ChainData
stubChainData =
  ChainData
    { cdWinningSlots = Nothing
    , cdNumParties = 3
    , cdStakeDistribution = [("node-0", 1000000000), ("node-1", 1000000000), ("node-2", 1000000000)]
    , cdSutIndex = 2
    , cdEpochLength = 10
    , cdMaxRBBody = 100
    , cdNodeEpoch = 0
    }

-- | Run the driver over an event list, collecting progress instead of rendering it.
--   Nothing aborts, so a violation does not stop the run and everything is observed.
collectWith :: Integer -> [ChainEvent] -> IO [Progress]
collectWith epochLen evs = do
  ref <- newIORef []
  runSegmented
    (\p -> modifyIORef' ref (p :))
    timings
    (const (pure stubChainData{cdEpochLength = epochLen}))
    evs
  reverse <$> readIORef ref

collect :: [ChainEvent] -> IO [Progress]
collect = collectWith 10

violations :: [Progress] -> [Text]
violations ps = [status | Violation _ _ status _ <- ps]

verifiedCount :: [Progress] -> Int
verifiedCount ps = length [() | Verified _ _ <- ps]

streamEndedCount :: [Progress] -> Int
streamEndedCount ps = length [() | StreamEnded _ <- ps]

segmentStarts :: [Progress] -> [Integer]
segmentStarts ps = [segStart s | SegmentStarted s _ <- ps]

-- | Slot ticks 0..n, in the order the driver sees them.
ticks :: Integer -> Integer -> [ChainEvent]
ticks from to = [CSlot (fromInteger s) | s <- [from .. to]]

-- | An EB announced in slot 8 of a ten-slot epoch: its window opens in slot 11 and
--   its deadline is slot 15, both in the next epoch. The vote is present, cast in the
--   first slot of the window.
straddlingVoted :: [ChainEvent]
straddlingVoted =
  ticks 0 7
    <> [CSlot 8, CAnnouncementAccepted "eb" 8, CEBAcquired "eb" 8]
    <> [CSlot 9, CSlot 10, CSlot 11, CVoted "eb" 8]
    <> ticks 12 16

-- | The same, with the vote withheld. Runs past the deadline at slot 15, where a vote
--   is forced; abstention before then is licensed by 'Roles₃'. The obligation is only
--   visible to a segment that carried the announcement across the boundary, so this is
--   what distinguishes an overlapping split from a clean cut.
straddlingUnvoted :: [ChainEvent]
straddlingUnvoted =
  ticks 0 7
    <> [CSlot 8, CAnnouncementAccepted "eb" 8, CEBAcquired "eb" 8]
    <> ticks 9 16

-- | Two announcements inside one slot. An EB announced at slot 2 is votable at 5;
--   the node votes there and, in the same slot, forges and announces its own EB,
--   moving the head. The slot must still be adjudicated against the EB voted for.
twoAnnouncementsInOneSlot :: [ChainEvent]
twoAnnouncementsInOneSlot =
  ticks 0 1
    <> [CSlot 2, CAnnouncementAccepted "eb2" 2, CEBAcquired "eb2" 2]
    <> [CSlot 3, CSlot 4]
    <> [ CSlot 5
       , CNodeIsLeader 5
       , CVoted "eb2" 2
       , CEBForged "eb5" 5
       , CRBForged "rb5" 5
       , CAnnouncementAccepted "eb5" 5
       ]
    <> ticks 6 9

-- | Announcements in consecutive slots. The EB announced at slot 2 is superseded as
--   the head at slot 3, before its own vote window opens at 5, so slot 5 abstains
--   legally and the only vote due is for the later EB at slot 6. Observed against a
--   devnet as announcements at 698 and 699 with a single vote at 702.
supersededBeforeVotable :: [ChainEvent]
supersededBeforeVotable =
  ticks 0 1
    <> [CSlot 2, CAnnouncementAccepted "eb2" 2, CEBAcquired "eb2" 2]
    <> [CSlot 3, CAnnouncementAccepted "eb3" 3, CEBAcquired "eb3" 3]
    <> [CSlot 4, CSlot 5]
    <> [CSlot 6, CVoted "eb3" 3]
    <> ticks 7 9

-- | A vote for an EB the chain never announced must not establish its own
--   precondition by supplying the head for its slot.
voteForUnannouncedEB :: [ChainEvent]
voteForUnannouncedEB =
  ticks 0 1
    <> [CSlot 2, CEBAcquired "eb2" 2]
    <> [CSlot 3, CSlot 4, CSlot 5, CVoted "eb2" 2]
    <> ticks 6 9

-- | A Praos leader slot with no Leios activity anywhere: the node won the lottery
--   and forged a ranking block while the subsystem had not yet done anything. The
--   mempool exceeds the ranking block's capacity, so an EB was owed and the gate is
--   what excuses the slot — which is the case worth reporting.
praosOnly :: [ChainEvent]
praosOnly =
  ticks 0 3
    <> [CSlot 4, CNodeIsLeader 4, CRBForged "rb" 4, CMempoolRange 200 200]
    <> ticks 5 9

-- | The same, but with a mempool that fits. The gate still suppresses enforcement,
--   and now costs nothing by doing so: the mempool rule would have excused the slot
--   on its own terms. Reporting suppression here would claim a loss not incurred,
--   which on a low-traffic network is every led slot.
praosOnlyMempoolFits :: [ChainEvent]
praosOnlyMempoolFits =
  ticks 0 3
    <> [CSlot 4, CNodeIsLeader 4, CRBForged "rb" 4, CMempoolRange 50 50]
    <> ticks 5 9

-- | The same leader slot, but preceded by a Leios acquisition, so the gate is open;
--   and with a mempool too large for the ranking block, so an EB really was owed and
--   forging none at slot 4 is a genuine abstention from an available role. Both
--   conditions are needed: the gate alone no longer makes a bare leader slot a
--   violation, since an EB is owed only when the mempool would not have fitted.
leiosActiveThenSilentLeader :: [ChainEvent]
leiosActiveThenSilentLeader =
  ticks 0 1
    <> [CSlot 2, CAnnouncementAccepted "eb" 2, CEBAcquired "eb" 2, CSlot 3]
    <> [CSlot 4, CNodeIsLeader 4, CRBForged "rb" 4, CMempoolRange 200 200]
    <> ticks 5 9

-- | The node logs no leadership check for slot 4. The spec advances one slot at a
--   time, so verification cannot cross the gap; it must restart after it rather than
--   reject the jump. Observed on a devnet at 30 TX/s as a single missing tick, which
--   killed the session with "8 : Err-Slot / Base₁-Action".
tickGap :: [ChainEvent]
tickGap = ticks 0 3 <> ticks 5 9

chainSegments :: Spec
chainSegments = do
  describe "carry width" $
    -- 3 * Lhdr to the window opening, plus Lvote to the deadline, plus Lhdr of
    -- acquisition lag. Under the previous spec the window was a single slot and this
    -- was 4; carrying only that much now would drop votes falling due late.
    it "spans the whole vote window plus the acquisition lead" $
      overlapSlots timings `shouldBe` 8

  describe "carrying across a boundary" $ do
    it "carries nothing for the first segment" $ do
      let c = carryAcross 4 0 []
      (carryEvents c, carryStart c, carrySpans c) `shouldBe` ([], 0, False)
    it "carries the slots within the window and starts there" $ do
      let c = carryAcross 4 10 (reverse (ticks 0 9))
      (carryStart c, carrySpans c) `shouldBe` (6, True)
    it "keeps non-tick events inside the window" $ do
      let seen = reverse (ticks 6 9 <> [CAnnouncementAccepted "eb" 9])
          c = carryAcross 4 10 seen
      length (carryEvents c) `shouldBe` 5
    it "starts at the earliest tick available when the epoch is shorter than the window" $ do
      let c = carryAcross 4 3 (reverse (ticks 1 2))
      carryStart c `shouldBe` 1
    it "trims events ahead of the first carried tick" $ do
      -- The oldest event here belongs to a slot before the cutoff; carried whole it
      -- would be attributed to the segment start rather than to its own slot.
      let seen = [CSlot 6, CEBAcquired "eb" 5]
          c = carryAcross 4 10 seen
      (length (carryEvents c), carryStart c) `shouldBe` (1, 6)

  describe "whether a queried schedule governs a segment" $ do
    it "does when it is for this epoch and the segment is wholly inside it" $
      segmentAuthoritative False 3 stubChainData{cdWinningSlots = Just [31], cdNodeEpoch = 3}
        `shouldBe` True
    it "does even when it is empty, an empty schedule being a real answer" $
      segmentAuthoritative False 3 stubChainData{cdWinningSlots = Just [], cdNodeEpoch = 3}
        `shouldBe` True
    it "does not when the node answered for another epoch" $
      segmentAuthoritative False 3 stubChainData{cdWinningSlots = Just [21], cdNodeEpoch = 2}
        `shouldBe` False
    it "does not when none was obtainable" $
      segmentAuthoritative False 3 stubChainData{cdWinningSlots = Nothing, cdNodeEpoch = 3}
        `shouldBe` False
    it "does not when the segment spans two epochs" $
      segmentAuthoritative True 3 stubChainData{cdWinningSlots = Just [31], cdNodeEpoch = 3}
        `shouldBe` False

  describe "which announced EB heads a slot" $ do
    it "adjudicates the slot against the EB that was voted for" $ do
      ps <- collectWith 100 twoAnnouncementsInOneSlot
      violations ps `shouldBe` []
    it "does not let a vote supply the head for an unannounced EB" $ do
      -- eb2 was acquired but never announced, so it was never votable; the vote
      -- must not make itself legal by becoming the slot's head.
      ps <- collectWith 100 voteForUnannouncedEB
      violations ps `shouldBe` []
    it "raises no obligation for a head superseded before its vote window opens" $ do
      ps <- collectWith 100 supersededBeforeVotable
      violations ps `shouldBe` []

  describe "a gap in the slot ticks" $ do
    it "does not reject the jump" $ do
      ps <- collectWith 100 tickGap
      violations ps `shouldBe` []
    it "reports the gap rather than passing over it silently" $ do
      ps <- collectWith 100 tickGap
      [(f, t) | SlotGap f t <- ps] `shouldBe` [(3, 5)]
    it "restarts verification after the gap, carrying nothing across it" $ do
      -- Carrying the overlap would bring slots from before the gap into the new
      -- segment, which would still contain the gap and still be rejected.
      ps <- collectWith 100 tickGap
      segmentStarts ps `shouldBe` [0, 5]

  describe "Praos leadership without Leios running" $ do
    it "raises no EB obligation when the log shows no Leios activity" $ do
      -- The devnet shape that failed: leader at slot 4, a ranking block forged, and
      -- nothing Leios anywhere. NodeIsLeader alone is Praos leadership.
      ps <- collectWith 100 praosOnly
      violations ps `shouldBe` []
    it "reports the suppression rather than exempting the slot silently" $ do
      ps <- collectWith 100 praosOnly
      length [n | LeiosInactive n <- ps] `shouldNotBe` 0
    it "stays quiet when the mempool rule would have excused the slot anyway" $ do
      -- Same shape, mempool within the ranking block's capacity. The gate suppresses
      -- nothing the rule would have caught, so claiming a suppression would be noise
      -- — and on a 1 TX/s network it fires on every led slot.
      ps <- collectWith 100 praosOnlyMempoolFits
      length [n | LeiosInactive n <- ps] `shouldBe` 0
    it "still raises no violation when the gate stays quiet" $ do
      ps <- collectWith 100 praosOnlyMempoolFits
      violations ps `shouldBe` []
    it "still enforces the EB role once Leios has shown activity" $ do
      -- Same leader slot, but an EB was acquired earlier, so the gate is open and
      -- forging nothing at slot 4 is a violation.
      ps <- collectWith 100 leiosActiveThenSilentLeader
      violations ps `shouldNotBe` []

  describe "checkpoint throttling" $ do
    it "re-verifies periodically rather than at every slot" $ do
      -- 46 ticks inside one epoch, so only the periodic checkpoints fire. Slot 0
      -- takes the boundary path, which starts the segment without checking it.
      ps <- collectWith 100 (ticks 0 45)
      verifiedCount ps
        `shouldBe` length [s | s <- [1 .. 45 :: Integer], s `mod` checkpointEvery == 0]
    it "still checks the tail at end of input despite throttling" $ do
      ps <- collectWith 100 (ticks 0 45)
      streamEndedCount ps `shouldBe` 1

  describe "obligations that straddle an epoch boundary" $ do
    it "starts the second segment before the boundary" $ do
      -- The boundary is slot 10 and the carry is 8 wide, so verification of the
      -- second segment reaches back to slot 2. On these deliberately tiny ten-slot
      -- epochs that is most of the previous one; at production epoch lengths the
      -- overlap is negligible.
      ps <- collect straddlingVoted
      segmentStarts ps `shouldBe` [0, 2]
    it "accepts a straddling vote that was cast" $ do
      ps <- collect straddlingVoted
      violations ps `shouldBe` []
    it "rejects a straddling vote that was withheld" $ do
      -- The discriminating case: with a clean cut the second segment starts on empty
      -- state, the obligation is invisible, and the abstention passes vacuously.
      ps <- collect straddlingUnvoted
      violations ps `shouldNotBe` []
