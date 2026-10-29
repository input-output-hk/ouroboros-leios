{-# LANGUAGE OverloadedStrings #-}

-- | Parser tests for the node.log 'ChainEvents' extraction, covering both
--   node trace schemas: the pre-w31 combined @TraceLeiosKernel@ namespace and
--   the w31+ per-event namespaces with RB-keyed votes. w31+ votes are
--   resolved via two linkage facts: @AnnouncementAccepted@ (election slot →
--   ebHash) composed with ChainDB's selection-change events,
--   @AddedToCurrentChain@ and @SwitchedToAFork@ (rbHash → slot).
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
        `shouldBe` [CAnnouncementAccepted "eb05" 300, CChainExtended 300, CVoted "eb05" 300, CVoteAcquired "eb05" 300]
    -- An RB can be adopted by switching to a fork rather than by extending the
    -- current chain. Both report the adopted tip in 'newtip', and the node votes
    -- on whatever it selected, so both must feed the linkage map. Listening only
    -- to AddedToCurrentChain silently drops the vote, which reads downstream as
    -- an unexplained abstention. Distinct from the CChainExtended cases below:
    -- this pins the vote *resolving* through a fork switch, not merely the tip
    -- advance being reported.
    it "resolves votes for an RB adopted by switching to a fork" $
      parse
        [ "{\"ns\":\"Consensus.LeiosKernel.AnnouncementAccepted\",\"data\":{\"kind\":\"LeiosAnnouncementAccepted\",\"ebHash\":\"eb07\",\"electionSlot\":699,\"ebBodySize\":70347,\"equivocation\":false}}"
        , "{\"ns\":\"ChainDB.AddBlockEvent.SwitchedToAFork\",\"data\":{\"kind\":\"TraceAddBlockEvent.SwitchedToAFork\",\"newSuffixSelectView\":{\"blockNo\":32,\"kind\":\"PraosTiebreakerView\",\"slotNo\":699},\"newtip\":\"" <> rb64 <> "@699\"}}"
        , "{\"ns\":\"Consensus.LeiosKernel.Voted\",\"data\":{\"kind\":\"LeiosVoted\",\"vote\":{\"rbHash\":\"" <> rb64 <> "\",\"voterId\":2},\"weight\":0.333333333333}}"
        ]
        `shouldBe` [CAnnouncementAccepted "eb07" 699, CChainExtended 699, CVoted "eb07" 699]
    it "emits AnnouncementAccepted, which is what makes an EB votable" $
      parse ["{\"ns\":\"Consensus.LeiosKernel.AnnouncementAccepted\",\"data\":{\"kind\":\"LeiosAnnouncementAccepted\",\"ebHash\":\"eb06\",\"electionSlot\":301,\"ebBodySize\":1,\"equivocation\":false}}"]
        `shouldBe` [CAnnouncementAccepted "eb06" 301]
    it "parses NodeIsLeader" $
      parse ["{\"ns\":\"Forge.Loop.NodeIsLeader\",\"data\":{\"kind\":\"TraceNodeIsLeader\",\"slot\":7}}"]
        `shouldBe` [CNodeIsLeader 7]
    it "emits CChainExtended when the tip advances (AddedToCurrentChain)" $
      parse ["{\"ns\":\"ChainDB.AddBlockEvent.AddedToCurrentChain\",\"data\":{\"kind\":\"AddedToCurrentChain\",\"newtip\":\"" <> rb64 <> "@432\"}}"]
        `shouldBe` [CChainExtended 432]
    it "emits CChainExtended on a fork switch too (SwitchedToAFork)" $
      parse ["{\"ns\":\"ChainDB.AddBlockEvent.SwitchedToAFork\",\"data\":{\"kind\":\"TraceAddBlockEvent.SwitchedToAFork\",\"newtip\":\"" <> rb64 <> "@433\"}}"]
        `shouldBe` [CChainExtended 433]
    it "maps NotVoted (a deliberate, protocol-legal abstention) with its reason" $
      parse ["{\"ns\":\"Consensus.LeiosKernel.NotVoted\",\"data\":{\"kind\":\"LeiosNotVoted\",\"ebHash\":\"eb07\",\"ebSlot\":540,\"reason\":\"chainTipDoesNotAnnounce\"}}"]
        `shouldBe` [CNotVoted "eb07" 540 "chainTipDoesNotAnnounce"]
    -- Mempool readings are far too voluminous to pass through one per event, so they
    -- are aggregated to one range per slot, emitted just ahead of the tick that
    -- closes that slot. The range also carries forward: the mempool as it stood when
    -- a slot began is one of that slot's readings, which is why slot 2's range starts
    -- at 300 rather than at its own first reading.
    it "aggregates mempool readings into one range per slot" $
      parse
        [ "{\"ns\":\"Forge.Loop.StartLeadershipCheck\",\"data\":{\"slot\":1}}"
        , "{\"ns\":\"Mempool.AddedTx\",\"data\":{\"kind\":\"TraceMempoolAddedTx\",\"mempoolSize\":{\"bytes\":100,\"numTxs\":1},\"tx\":{\"txid\":\"a\"}}}"
        , "{\"ns\":\"Mempool.AddedTx\",\"data\":{\"kind\":\"TraceMempoolAddedTx\",\"mempoolSize\":{\"bytes\":300,\"numTxs\":2},\"tx\":{\"txid\":\"b\"}}}"
        , "{\"ns\":\"Forge.Loop.StartLeadershipCheck\",\"data\":{\"slot\":2}}"
        , "{\"ns\":\"Mempool.RemoveTxs\",\"data\":{\"kind\":\"TraceMempoolRemoveTxs\",\"mempoolSize\":{\"bytes\":40,\"numTxs\":0},\"txs\":[]}}"
        , "{\"ns\":\"Forge.Loop.StartLeadershipCheck\",\"data\":{\"slot\":3}}"
        ]
        `shouldBe` [ CSlot 1
                   , CMempoolRange 100 300
                   , CSlot 2
                   , CMempoolRange 40 300
                   , CSlot 3
                   ]
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
