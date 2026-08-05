{-# LANGUAGE OverloadedStrings #-}

-- | Parser tests for the node.log 'ChainEvents' extraction, covering both
--   node trace schemas: the pre-w31 combined @TraceLeiosKernel@ namespace and
--   the w31+ per-event namespaces with RB-keyed votes (resolved via
--   @BlockAnnounced@). Payload shapes mirror
--   @traceLeiosKernelToObject@ (ouroboros-consensus @LeiosDemoTypes@).
module Spec.ChainEvents (
  chainEvents,
) where

import ChainEvents (ChainEvent (..), parseNodeLog)
import qualified Data.ByteString.Lazy.Char8 as BSL8
import Test.Hspec (Spec, describe, it, shouldBe)

parse :: [BSL8.ByteString] -> [ChainEvent]
parse = parseNodeLog . BSL8.unlines

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
    it "resolves RB-keyed votes via BlockAnnounced" $
      parse
        [ "{\"ns\":\"Consensus.LeiosKernel.BlockAnnounced\",\"data\":{\"kind\":\"LeiosBlockAnnounced\",\"rbHash\":\"rb01\",\"ebHash\":\"eb05\",\"ebSlot\":300}}"
        , "{\"ns\":\"Consensus.LeiosKernel.Voted\",\"data\":{\"kind\":\"LeiosVoted\",\"vote\":{\"rbHash\":\"rb01\",\"voterId\":20},\"weight\":1.22e-2}}"
        , "{\"ns\":\"Consensus.LeiosKernel.VoteAcquired\",\"data\":{\"kind\":\"LeiosVoteAcquired\",\"vote\":{\"rbHash\":\"rb01\",\"voterId\":32}}}"
        ]
        `shouldBe` [CVoted "eb05" 300, CVoteAcquired "eb05" 300]
    it "keeps unresolved RB-keyed votes visible (RB hash, slot 0)" $
      parse ["{\"ns\":\"Consensus.LeiosKernel.VoteAcquired\",\"data\":{\"kind\":\"LeiosVoteAcquired\",\"vote\":{\"rbHash\":\"rb99\",\"voterId\":1}}}"]
        `shouldBe` [CVoteAcquired "rb99" 0]

  describe "irrelevant input" $ do
    it "drops other Leios kinds, banners, and junk" $
      parse
        [ "==== run started at 2026-08-05T17:59:59Z (pid 177093) ===="
        , "{\"ns\":\"Consensus.LeiosKernel.Msg\",\"data\":{\"kind\":\"LeiosKernelMsg\",\"msg\":\"runLeiosVoting: disabled\"}}"
        , "{\"ns\":\"Consensus.LeiosKernel.BlockPointMissing\",\"data\":{\"kind\":\"LeiosBlockPointMissing\",\"ebHash\":\"x\",\"ebSlot\":1}}"
        , "{\"ns\":\"ChainDB.AddBlockEvent\",\"data\":{\"kind\":\"AddedBlockToQueue\"}}"
        ]
        `shouldBe` []
