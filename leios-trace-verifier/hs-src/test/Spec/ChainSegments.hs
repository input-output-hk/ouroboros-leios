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

-- | The timings the chain app uses, under which an announced EB has exactly one legal
--   vote slot at @ebSlot + 3@ and the carry width is 4.
timings :: Timings
timings = Timings{tLhdr = 1, tLvote = 4, tLdiff = 7, tValidityCheckTime = 3}

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

-- | An EB announced in slot 8 of a ten-slot epoch, so its vote falls due in slot 11 —
--   in the next epoch. The vote is present.
straddlingVoted :: [ChainEvent]
straddlingVoted =
  ticks 0 7
    <> [CSlot 8, CAnnouncementAccepted "eb" 8, CEBAcquired "eb" 8, CSlot 9, CSlot 10, CSlot 11, CVoted "eb" 8, CSlot 12]

-- | The same, with the vote withheld. The obligation is only visible to a segment
--   that carried the announcement across the boundary, so this is what distinguishes
--   an overlapping split from a clean cut.
straddlingUnvoted :: [ChainEvent]
straddlingUnvoted =
  ticks 0 7
    <> [CSlot 8, CAnnouncementAccepted "eb" 8, CEBAcquired "eb" 8, CSlot 9, CSlot 10, CSlot 11, CSlot 12]

-- | A Praos leader slot with no Leios activity anywhere: the node won the lottery
--   and forged a ranking block while the subsystem had not yet done anything.
praosOnly :: [ChainEvent]
praosOnly =
  ticks 0 3
    <> [CSlot 4, CNodeIsLeader 4, CRBForged "rb" 4]
    <> ticks 5 9

-- | The same leader slot, but preceded by a Leios acquisition, so the gate is open
--   and forging no EB at slot 4 is a genuine abstention from an available role.
leiosActiveThenSilentLeader :: [ChainEvent]
leiosActiveThenSilentLeader =
  ticks 0 1
    <> [CSlot 2, CAnnouncementAccepted "eb" 2, CEBAcquired "eb" 2, CSlot 3]
    <> [CSlot 4, CNodeIsLeader 4, CRBForged "rb" 4]
    <> ticks 5 9

chainSegments :: Spec
chainSegments = do
  describe "carry width" $
    it "spans the vote window plus the acquisition lead" $
      overlapSlots timings `shouldBe` 4

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

  describe "Praos leadership without Leios running" $ do
    it "raises no EB obligation when the log shows no Leios activity" $ do
      -- The devnet shape that failed: leader at slot 4, a ranking block forged, and
      -- nothing Leios anywhere. NodeIsLeader alone is Praos leadership.
      ps <- collectWith 100 praosOnly
      violations ps `shouldBe` []
    it "reports the suppression rather than exempting the slot silently" $ do
      ps <- collectWith 100 praosOnly
      length [n | LeiosInactive n <- ps] `shouldNotBe` 0
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
      ps <- collect straddlingVoted
      segmentStarts ps `shouldBe` [0, 6]
    it "accepts a straddling vote that was cast" $ do
      ps <- collect straddlingVoted
      violations ps `shouldBe` []
    it "rejects a straddling vote that was withheld" $ do
      -- The discriminating case: with a clean cut the second segment starts on empty
      -- state, the obligation is invisible, and the abstention passes vacuously.
      ps <- collect straddlingUnvoted
      violations ps `shouldNotBe` []
