{-# LANGUAGE OverloadedStrings #-}

-- | Behavioural tests for the chain verifier itself, as distinct from the node.log
--   parser covered by "Spec.ChainEvents". Each case is a hand-written event list run
--   through the whole pipeline — translation into spec actions, then the Agda
--   verifier — so what they pin down is the translator decisions that determine
--   whether an obligation is raised at all, and whether the spec then discharges it.
--
--   'verifyChainTraceFinalFromSlot' is used rather than the streaming entry point
--   because a fixed event list is a complete log: the trailing slot can be
--   adjudicated, so every slot in a fixture is checked.
module Spec.ChainVerifier (
  chainVerifier,
) where

import ChainEvents (ChainEvent (..))
import Data.Text (Text)
import LinearLeiosLib (verifyChainTraceFinalFromSlot)
import Test.Hspec (Spec, describe, it, shouldBe, shouldNotBe)

-- | Three equal-stake pools with the SUT last, mirroring the devnet the chain
--   verifier is exercised against. The figures have to be non-zero: vote
--   eligibility is the CIP-0164 committee, computed from the stake distribution
--   rather than a per-slot lottery.
stakeDist :: [(Text, Integer)]
stakeDist = [("node-0", 1000000000), ("node-1", 1000000000), ("node-2", 1000000000)]

-- | Verify a fixed event list starting at slot 0, returning just the status.
--
--   Timings are the ones the chain app hardcodes — Lhdr 1, Lvote 4, Ldiff 7,
--   validity check 3 — under which an announced EB is votable in exactly one slot,
--   @ebSlot + (3 * Lhdr `max` validityCheckTime) == ebSlot + 3@.
verify :: [Integer] -> Bool -> [ChainEvent] -> Text
verify slots authoritative evs =
  fst (snd (verifyChainTraceFinalFromSlot 3 2 stakeDist 1 4 7 slots authoritative evs 0))

-- | Eligibility taken from the log, as happens for any epoch the queried schedule
--   cannot cover.
fromLog :: [ChainEvent] -> Text
fromLog = verify [] False

-- | Verify from a given start slot, as a windowed verifier does for each window.
verifyFrom :: Integer -> [ChainEvent] -> Text
verifyFrom from evs =
  fst (snd (verifyChainTraceFinalFromSlot 3 2 stakeDist 1 4 7 [] False evs from))

-- | An EB announced and acquired in slot 1 and voted in slot 4.
announcedAndVoted :: [ChainEvent]
announcedAndVoted =
  [ CSlot 0
  , CSlot 1
  , CAnnouncementAccepted "eb" 1
  , CEBAcquired "eb" 1
  , CSlot 2
  , CSlot 3
  , CSlot 4
  , CVoted "eb" 1
  , CSlot 5
  -- extended past the CIP vote deadline (slot 8 = announce+3*Lhdr+Lvote) so a
  -- withheld vote is adjudicated at the deadline rather than escaping when the
  -- trace ends mid-window (deferral is legal inside the window).
  , CSlot 6
  , CSlot 7
  , CSlot 8
  , CSlot 9
  ]

-- | The same EB fetched but never announced on the chain, so nothing makes it
--   votable and abstaining is correct.
acquiredNotAnnounced :: [ChainEvent]
acquiredNotAnnounced =
  [ CSlot 0
  , CSlot 1
  , CEBAcquired "eb" 1
  , CSlot 2
  , CSlot 3
  , CSlot 4
  , CSlot 5
  ]

-- | The announcer's own adoption: 'CChainExtended' in the very slot the EB was
--   announced, which is the ordinary self-forge shape — the node reports adopting its
--   own ranking block right after announcing, and in Linear Leios that block shares
--   the EB's election slot. The tip has reached the announcer, not passed it, so the
--   window must stay open and the vote at slot 4 is still due.
adoptedAtAnnouncer :: [ChainEvent]
adoptedAtAnnouncer =
  [ CSlot 0
  , CSlot 1
  , CAnnouncementAccepted "eb" 1
  , CEBAcquired "eb" 1
  , CChainExtended 1
  , CSlot 2
  , CSlot 3
  , CSlot 4
  , CSlot 5
  , CSlot 6
  , CSlot 7
  , CSlot 8
  , CSlot 9
  ]

-- | The chain moves strictly past the announcer, so the EB can no longer be
--   certified and the window closes. Abstaining at slot 4 is then correct.
adoptedPastAnnouncer :: [ChainEvent]
adoptedPastAnnouncer =
  [ CSlot 0
  , CSlot 1
  , CAnnouncementAccepted "eb" 1
  , CEBAcquired "eb" 1
  , CSlot 2
  , CChainExtended 2
  , CSlot 3
  , CSlot 4
  , CSlot 5
  ]

-- | A repeat vote far from the original, and the bounded window a windowed verifier
--   would see when it reaches slot 20: overlap is 4, so the window starts at 16 and
--   contains neither the announcement nor the first vote.
votedTwiceFar :: [ChainEvent]
votedTwiceFar =
  [CSlot 0, CSlot 1, CAnnouncementAccepted "eb" 1, CEBAcquired "eb" 1]
    <> [CSlot s | s <- [2 .. 3]]
    <> [CSlot 4, CVoted "eb" 1]
    <> [CSlot s | s <- [5 .. 19]]
    <> [CSlot 20, CVoted "eb" 1]
    <> [CSlot 21]

windowOfVotedTwiceFar :: [ChainEvent]
windowOfVotedTwiceFar =
  [CSlot s | s <- [16 .. 19]]
    <> [CSlot 20, CVoted "eb" 1]
    <> [CSlot 21]

-- | The same EB voted twice: once in its one legal slot 4, then again in slot 5.
votedTwice :: [ChainEvent]
votedTwice =
  [ CSlot 0
  , CSlot 1
  , CAnnouncementAccepted "eb" 1
  , CEBAcquired "eb" 1
  , CSlot 2
  , CSlot 3
  , CSlot 4
  , CVoted "eb" 1
  , CSlot 5
  , CVoted "eb" 1
  , CSlot 6
  ]

-- | Two announced EBs, each voted in its own slot. Requires the EB payload to be
--   derived from the hash: a constant one collapses both to the same spec-level
--   hash, and the second vote is then rejected as already cast.
twoVotes :: [ChainEvent]
twoVotes =
  [ CSlot 0
  , CSlot 1
  , CAnnouncementAccepted "eb1" 1
  , CEBAcquired "eb1" 1
  , CSlot 2
  , CSlot 3
  , CSlot 4
  , CVoted "eb1" 1
  , CSlot 5
  , CAnnouncementAccepted "eb2" 5
  , CEBAcquired "eb2" 5
  , CSlot 6
  , CSlot 7
  , CSlot 8
  , CVoted "eb2" 5
  , CSlot 9
  ]

dropVotes :: [ChainEvent] -> [ChainEvent]
dropVotes = filter (not . isVote)
 where
  isVote (CVoted _ _) = True
  isVote _ = False

chainVerifier :: Spec
chainVerifier = do
  describe "slot ticks alone" $
    it "accepts a run in which the node does nothing" $
      fromLog [CSlot 0, CSlot 1, CSlot 2] `shouldBe` "ok"

  describe "EB production" $ do
    it "accepts an EB forged in a slot the log records as won" $
      fromLog [CSlot 0, CNodeIsLeader 0, CEBForged "eb" 0, CSlot 1] `shouldBe` "ok"
    it "rejects an EB forged with no leadership record" $
      fromLog [CSlot 0, CEBForged "eb" 0, CSlot 1] `shouldNotBe` "ok"
    it "accepts an EB forged in a slot an authoritative schedule says was won" $
      verify [0] True [CSlot 0, CEBForged "eb" 0, CSlot 1] `shouldBe` "ok"
    it "rejects abstention in a slot an authoritative schedule says was won" $
      verify [0] True [CSlot 0, CSlot 1] `shouldNotBe` "ok"

  describe "voting" $ do
    it "accepts a vote for an announced EB inside its voting window" $
      fromLog announcedAndVoted `shouldBe` "ok"
    it "rejects abstention when an announced EB was votable" $
      fromLog (dropVotes announcedAndVoted) `shouldNotBe` "ok"
    it "raises no obligation for an EB acquired but never announced" $
      fromLog acquiredNotAnnounced `shouldBe` "ok"
    it "accepts votes for two distinct EBs in one run" $
      fromLog twoVotes `shouldBe` "ok"
    -- What distinguishes these two is the obligation, not the vote: our head
    -- selection would let a vote through either way, so the cost of treating the
    -- announcer's own adoption as superseding is a withheld vote going unreported.
    it "keeps the window open when the tip only reaches the announcer" $
      fromLog adoptedAtAnnouncer `shouldNotBe` "ok"
    it "closes the window when the tip moves past the announcer" $
      fromLog adoptedPastAnnouncer `shouldBe` "ok"
    it "refuses a repeat vote in the slot after the legal one" $
      fromLog votedTwice `shouldNotBe` "ok"
    it "refuses a repeat vote long after the legal one" $
      fromLog votedTwiceFar `shouldNotBe` "ok"
    -- Characterises what bounding the verified prefix would cost, rather than
    -- asserting it is desirable. Verification from slot 16 sees neither the
    -- announcement nor the first vote, so 'wasAnnounced' is false, CVoted is
    -- dropped, no VT-Role is raised, and the stale vote passes unnoticed. Any
    -- windowing scheme has to carry the announcement history forward, or accept
    -- this blind spot: the overlap width is sized for legitimate obligations and
    -- says nothing about how far back a spurious event may reach.
    it "loses a stale vote when the prefix cannot see the announcement" $
      verifyFrom 16 windowOfVotedTwiceFar `shouldBe` "ok"
