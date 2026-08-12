{-# LANGUAGE OverloadedStrings #-}

-- | Parser tests for the node.log 'ChainEvents' extraction, covering both
--   node trace schemas: the pre-w31 combined @TraceLeiosKernel@ namespace and
--   the w31+ per-event namespaces with RB-keyed votes. w31+ votes are
--   resolved via two linkage facts: @AnnouncementAccepted@ (election slot →
--   ebHash) composed with ChainDB @AddedToCurrentChain@ (rbHash → slot).
--   Payload shapes mirror real node.log lines.
module Spec.ChainEvents (
  chainEvents,
) where

import ChainEvents (ChainEvent (..), parseNodeLog)
import qualified Data.ByteString.Lazy.Char8 as BSL8
import Test.Hspec (Spec, describe, it, shouldBe)

parse :: [BSL8.ByteString] -> [ChainEvent]
parse = parseNodeLog . BSL8.unlines

-- | A 64-hex-char RB hash (ChainDB's @newtip@ parser requires exactly 64).
rb64 :: BSL8.ByteString
rb64 = BSL8.concat (replicate 32 "ab")

chainEvents :: Spec
chainEvents = do
  describe "Forge.Loop events" $ do
    it "parses StartLeadershipCheck" $
      parse ["{\"ns\":\"Forge.Loop.StartLeadershipCheck\",\"data\":{\"kind\":\"TraceStartLeadershipCheck\",\"slot\":571219}}"]
        `shouldBe` [CSlot 571219]
    it "parses ForgedBlock" $
      parse ["{\"ns\":\"Forge.Loop.ForgedBlock\",\"data\":{\"kind\":\"TraceForgedBlock\",\"slot\":42,\"block\":\"aa11\",\"blockNo\":7}}"]
        `shouldBe` [CRBForged "aa11" 42]

  describe "pre-w31 combined namespace (TraceLeiosKernel + kind)" $ do
    it "parses LeiosBlockForged" $
      parse ["{\"ns\":\"Consensus.LeiosKernel.TraceLeiosKernel\",\"data\":{\"kind\":\"LeiosBlockForged\",\"hash\":\"eb01\",\"slot\":100}}"]
        `shouldBe` [CEBForged "eb01" 100]
    it "parses LeiosBlockAcquired" $
      parse ["{\"ns\":\"Consensus.LeiosKernel.TraceLeiosKernel\",\"data\":{\"kind\":\"LeiosBlockAcquired\",\"ebHash\":\"eb02\",\"ebSlot\":101}}"]
        `shouldBe` [CEBAcquired "eb02" 101]
    it "parses EB-keyed LeiosVoted / LeiosVoteAcquired" $
      parse
        [ "{\"ns\":\"Consensus.LeiosKernel.TraceLeiosKernel\",\"data\":{\"kind\":\"LeiosVoted\",\"vote\":{\"ebHash\":\"eb03\",\"slot\":102}}}"
        , "{\"ns\":\"Consensus.LeiosKernel.TraceLeiosKernel\",\"data\":{\"kind\":\"LeiosVoteAcquired\",\"vote\":{\"ebHash\":\"eb03\",\"slot\":102}}}"
        ]
        `shouldBe` [CVoted "eb03" 102, CVoteAcquired "eb03" 102]

  describe "w31+ per-event namespaces" $ do
    it "parses BlockForged" $
      parse ["{\"ns\":\"Consensus.LeiosKernel.BlockForged\",\"data\":{\"kind\":\"LeiosBlockForged\",\"hash\":\"eb04\",\"slot\":200,\"numTxs\":2011,\"ebSize\":78000}}"]
        `shouldBe` [CEBForged "eb04" 200]
    it "parses BlockAcquired (real node.log shape)" $
      parse ["{\"at\":\"2026-07-27T08:57:45.5Z\",\"ns\":\"Consensus.LeiosKernel.BlockAcquired\",\"data\":{\"ebHash\":\"a23c6d\",\"ebSlot\":571219,\"kind\":\"LeiosBlockAcquired\"},\"sev\":\"Info\",\"thread\":\"125\",\"host\":\"starbook\"}"]
        `shouldBe` [CEBAcquired "a23c6d" 571219]
    it "resolves RB-keyed votes via AnnouncementAccepted + AddedToCurrentChain" $
      parse
        [ "{\"ns\":\"Consensus.LeiosKernel.AnnouncementAccepted\",\"data\":{\"kind\":\"LeiosAnnouncementAccepted\",\"ebHash\":\"eb05\",\"electionSlot\":300,\"ebBodySize\":70347,\"equivocation\":false}}"
        , "{\"ns\":\"ChainDB.AddBlockEvent.AddedToCurrentChain\",\"data\":{\"kind\":\"AddedToCurrentChain\",\"newtip\":\"" <> rb64 <> "@300\"}}"
        , "{\"ns\":\"Consensus.LeiosKernel.Voted\",\"data\":{\"kind\":\"LeiosVoted\",\"vote\":{\"rbHash\":\"" <> rb64 <> "\",\"voterId\":20},\"weight\":1.22e-2}}"
        , "{\"ns\":\"Consensus.LeiosKernel.VoteAcquired\",\"data\":{\"kind\":\"LeiosVoteAcquired\",\"vote\":{\"rbHash\":\"" <> rb64 <> "\",\"voterId\":32}}}"
        ]
        `shouldBe` [CAnnouncementAccepted "eb05" 300, CVoted "eb05" 300, CVoteAcquired "eb05" 300]
    it "emits AnnouncementAccepted, which is what makes an EB votable" $
      parse ["{\"ns\":\"Consensus.LeiosKernel.AnnouncementAccepted\",\"data\":{\"kind\":\"LeiosAnnouncementAccepted\",\"ebHash\":\"eb06\",\"electionSlot\":301,\"ebBodySize\":1,\"equivocation\":false}}"]
        `shouldBe` [CAnnouncementAccepted "eb06" 301]
    it "parses NodeIsLeader" $
      parse ["{\"ns\":\"Forge.Loop.NodeIsLeader\",\"data\":{\"kind\":\"TraceNodeIsLeader\",\"slot\":7}}"]
        `shouldBe` [CNodeIsLeader 7]
    it "drops votes whose linkage is missing (truncated log prefix)" $
      parse ["{\"ns\":\"Consensus.LeiosKernel.VoteAcquired\",\"data\":{\"kind\":\"LeiosVoteAcquired\",\"vote\":{\"rbHash\":\"" <> rb64 <> "\",\"voterId\":1}}}"]
        `shouldBe` []

  describe "irrelevant input" $ do
    it "drops other Leios kinds, banners, and junk" $
      parse
        [ "==== run started at 2026-08-05T17:59:59Z (pid 177093) ===="
        , "{\"ns\":\"Consensus.LeiosKernel.Msg\",\"data\":{\"kind\":\"LeiosKernelMsg\",\"msg\":\"runLeiosVoting: disabled\"}}"
        , "{\"ns\":\"Consensus.LeiosKernel.BlockPointMissing\",\"data\":{\"kind\":\"LeiosBlockPointMissing\",\"ebHash\":\"x\",\"ebSlot\":1}}"
        , "{\"ns\":\"ChainDB.AddBlockEvent\",\"data\":{\"kind\":\"AddedBlockToQueue\"}}"
        ]
        `shouldBe` []
