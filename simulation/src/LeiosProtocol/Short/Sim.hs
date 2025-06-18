{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module LeiosProtocol.Short.Sim where

import Chan
import Control.Exception (assert)
import Control.Monad (forever, guard)
import Control.Monad.Class.MonadFork (MonadFork (forkIO))
import Control.Monad.IOSim as IOSim (IOSim, runSimTrace)
import Control.Tracer as Tracer (
  Contravariant (contramap),
  Tracer,
  traceWith,
 )
import Data.Aeson
import Data.Aeson.Encoding (pair)
import Data.Coerce
import Data.Default (Default (..))
import Data.Foldable
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as T
import GHC.Records
import qualified LeiosEvents as Shared
import LeiosProtocol.Common hiding (Point)
import LeiosProtocol.Config
import LeiosProtocol.Relay
import LeiosProtocol.Short
import LeiosProtocol.Short.Node
import ModelTCP
import Network.TypedProtocol
import P2P
import PraosProtocol.BlockFetch (Message (..))
import qualified PraosProtocol.Common.Chain as Chain
import PraosProtocol.PraosNode (PraosMessage (..), praosMessageLabel)
import SimTCPLinks
import SimTypes
import System.Random (mkStdGen)
import Prelude hiding (id)

type LeiosTrace = [(Time, LeiosEvent)]

data LeiosEvent
  = -- | Declare the nodes and links
    LeiosEventSetup
      !World
      !(Map NodeId Point) -- nodes and locations
      !(Map NodeId StakeFraction)
      !(Set Link) -- links between nodes
  | -- | An event at a node
    LeiosEventNode (LabelNode LeiosNodeEvent)
  | -- | An event on a tcp link between two nodes
    LeiosEventTcp (LabelLink (TcpEvent LeiosMessage))
  deriving (Show)

logLeiosTraceEvent :: Map NodeId T.Text -> Int -> DiffTime -> LeiosEvent -> Maybe Encoding
logLeiosTraceEvent m loudness t e = do
  x <- logLeiosEvent m loudness e
  pure $ (pairs $ "time_s" .= t <> pair "event" x)

logLeiosEvent :: Map NodeId T.Text -> Int -> LeiosEvent -> Maybe Encoding
logLeiosEvent nodeNames loudness e = case e of
  LeiosEventSetup{} -> Nothing
  LeiosEventNode (LabelNode nid x) -> do
    pairs <$> logNode nid x
  LeiosEventTcp (LabelLink from to (TcpSendMsg msg forecast fcs)) -> do
    ps <- logMsg msg
    pure $
      pairs $
        "tag" .= asString "Sent"
          <> "sender" .= from
          <> "receipient" .= to
          <> mconcat
            [ "fragments" .= length fcs
              <> "forecast" .= forecast
            | emitDebug
            ]
          <> mconcat ["forecasts" .= fcs | emitControl]
          <> "msg_size_bytes" .= fromBytes (messageSizeBytes msg)
          <> "time_to_received_s" .= (coerce forecast.msgRecvTrailingEdge - coerce forecast.msgSendLeadingEdge :: DiffTime)
          <> "sending_s" .= (coerce forecast.msgSendTrailingEdge - coerce forecast.msgSendLeadingEdge :: DiffTime)
          <> ps
 where
  emitControl = loudness >= 3
  emitDebug = loudness >= 2
  node nid = "node" .= nid <> "node_name" .= nodeNames Map.! nid
  ibKind = "kind" .= asString "IB"
  ebKind = "kind" .= asString "EB"
  vtKind = "kind" .= asString "VT"
  rbKind = "kind" .= asString "RB"
  cpuTag = "tag" .= asString "Cpu"
  rbRef h = case h of
    GenesisHash -> "genesis"
    BlockHash x -> show (coerce x :: Int)
  logNode nid (PraosNodeEvent x) = logPraos nid x
  logNode nid (LeiosNodeEventLedgerState rbId) = do
    guard emitDebug
    Just $
      mconcat
        [ "tag" .= asString "ledgerstate"
        , node nid
        , "id" .= show (coerce rbId :: Int)
        ]
  logNode nid (LeiosNodeEventCPU CPUTask{..}) =
    Just $
      mconcat
        [ cpuTag
        , node nid
        , "duration_s" .= cpuTaskDuration
        , "task_label" .= cpuTaskLabel
        ]
  logNode nid (LeiosNodeEvent blkE blk)
    | Pruned <- blkE, not emitDebug = Nothing
    | otherwise = Just $ "tag" .= tag <> kindAndId <> extra <> node nid
   where
    extra
      | Generate <- blkE = case blk of
          EventIB ib ->
            mconcat
              [ "slot" .= ib.header.slot
              , "payload_bytes" .= fromBytes ib.body.size
              , "size_bytes" .= fromBytes (messageSizeBytes ib)
              , "rb_ref" .= rbRef (ib.header.rankingBlock)
              ]
          EventEB eb -> do
            let ebRefs = case eb.endorseBlocksEarlierPipeline of
                  [] -> mempty
                  ebrefs -> "endorse_blocks" .= map mkStringId ebrefs
            mconcat
              [ "slot" .= eb.slot
              , "input_blocks" .= map mkStringId eb.inputBlocks
              , ebRefs
              , "size_bytes" .= fromBytes (messageSizeBytes eb)
              ]
          EventVote vt ->
            mconcat
              [ "slot" .= vt.slot
              , "votes" .= vt.votes
              , "endorse_blocks" .= map mkStringId vt.endorseBlocks
              , "size_bytes" .= fromBytes (messageSizeBytes vt)
              ]
      | otherwise = mempty
    tag = asString $ case blkE of
      Generate -> "generated"
      Received -> "received"
      EnterState -> "enteredstate"
      Pruned -> "pruned"
    kindAndId = case blk of
      EventIB ib -> mconcat [ibKind, "id" .= ib.stringId]
      EventEB eb -> mconcat [ebKind, "id" .= eb.stringId]
      EventVote vt -> mconcat [vtKind, "id" .= vt.stringId]
  logNode _nid LeiosNodeEventConformance{} = Nothing
  logPraos nid (PraosNodeEventGenerate blk@(Block h b)) =
    Just $
      mconcat
        [ "tag" .= asString "generated"
        , rbKind
        , "id" .= show (coerce @_ @Int (blockHash blk))
        , "size_bytes" .= fromBytes (messageSizeBytes h + messageSizeBytes b)
        , node nid
        , "endorsed" .= map fst b.endorseBlocks
        , "parent" .= rbRef (blockPrevHash blk)
        ]
  logPraos nid (PraosNodeEventReceived blk) =
    Just $
      mconcat
        ["tag" .= asString "received", rbKind, "id" .= show (coerce @_ @Int (blockHash blk)), node nid]
  logPraos nid (PraosNodeEventEnterState blk) =
    Just $
      mconcat
        ["tag" .= asString "enteredstate", rbKind, "id" .= show (coerce @_ @Int (blockHash blk)), node nid]
  logPraos nid (PraosNodeEventCPU task) =
    assert False $
      Just $
        mconcat
          [cpuTag, node nid, "task" .= task]
  logPraos nid (PraosNodeEventNewTip chain) = do
    guard emitDebug
    Just $
      mconcat
        [ "tag" .= asString "chaintip"
        , "id" .= rbRef (Chain.headHash chain)
        , node nid
        ]
  logMsg :: LeiosMessage -> Maybe Series
  logMsg (RelayIB msg) = (ibKind <>) <$> logRelay (.id) msg
  logMsg (RelayEB msg) = (ebKind <>) <$> logRelay (.id) msg
  logMsg (RelayVote msg) = (vtKind <>) <$> logRelay (.id) msg
  logMsg (PraosMsg (PraosMessage (Right (ProtocolMessage (SomeMessage (MsgBlock hash _body)))))) =
    Just $ rbKind <> "id" .= show (coerce @_ @Int hash)
  logMsg (PraosMsg msg)
    | emitControl = Just $ mconcat [rbKind <> "id" .= asString "control", "msg_label" .= praosMessageLabel msg]
    | otherwise = Nothing
  logRelay :: (HasField "node" id NodeId, HasField "num" id Int) => (h -> id) -> RelayMessage id h b -> Maybe Series
  logRelay _getId (ProtocolMessage (SomeMessage msg@(MsgRespondBodies xs))) =
    Just $
      "ids" .= map (mkStringId . fst) xs
        <> "msg_label" .= relayMessageLabel msg
  logRelay _getId (ProtocolMessage (SomeMessage msg@(MsgRequestBodies xs)))
    | emitDebug =
        Just $
          "ids" .= map mkStringId xs
            <> "msg_label" .= relayMessageLabel msg
  logRelay getId (ProtocolMessage (SomeMessage msg@(MsgRespondHeaders xs)))
    | emitDebug =
        Just $
          "ids" .= map (mkStringId . getId) (toList xs)
            <> "msg_label" .= relayMessageLabel msg
  logRelay _getId (ProtocolMessage (SomeMessage msg@(MsgRequestHeaders _ ws we)))
    | emitDebug =
        Just $
          "shrink" .= ws.value
            <> "expand" .= we.value
            <> "msg_label" .= relayMessageLabel msg
  logRelay _ (ProtocolMessage (SomeMessage msg))
    | emitControl =
        Just $
          "id" .= asString "control"
            <> "msg_label" .= relayMessageLabel msg
    | otherwise = Nothing
  asString x = x :: String

messages :: [(a, LeiosEvent)] -> [(a, LabelLink LeiosMessage)]
messages trace = [(t, LabelLink x y msg) | (t, LeiosEventTcp (LabelLink x y (TcpSendMsg msg _ _))) <- trace]
sharedTraceEvent :: LeiosConfig -> Map NodeId T.Text -> DiffTime -> LeiosEvent -> Maybe Shared.TraceEvent
sharedTraceEvent leios m t e = Shared.TraceEvent (realToFrac t) <$> sharedEvent leios m e
sharedEvent :: LeiosConfig -> Map NodeId T.Text -> LeiosEvent -> Maybe Shared.Event
sharedEvent leios nodeNames e = case e of
  LeiosEventNode (LabelNode nid e') -> sharedNode (nodeName nid) e'
  LeiosEventTcp (LabelLink from to (TcpSendMsg msg forecast _)) ->
    sharedMsg (nodeName from) (nodeName to) (coerce forecast.msgSendTrailingEdge - coerce forecast.msgSendLeadingEdge :: DiffTime) (fromIntegral $ messageSizeBytes msg) msg
  _ -> Nothing
 where
  nodeName nid = fromMaybe undefined $ Map.lookup nid nodeNames
  blkId (EventIB ib) = mkStringId ib.id
  blkId (EventEB eb) = mkStringId eb.id
  blkId (EventVote vt) = mkStringId vt.id
  blkSlot (EventIB ib) = fromIntegral . fromEnum $ ib.header.slot
  blkSlot (EventEB eb) = fromIntegral . fromEnum $ eb.slot
  blkSlot (EventVote vt) = fromIntegral . fromEnum $ vt.slot
  splitTaskLabel lbl = case T.break (== ':') lbl of
    (tag, blkid) -> (tag, T.drop 2 blkid)
  sharedNode node (LeiosNodeEvent Generate blk) = Just $ sharedGenerated node (blkId blk) (blkSlot blk) blk
  sharedNode node (LeiosNodeEvent Received blk) = Just $ sharedReceived node (blkId blk) blk
  sharedNode node (LeiosNodeEvent EnterState blk) = Just $ sharedEnterState node (blkId blk) (blkSlot blk) blk
  sharedNode node (LeiosNodeEventCPU CPUTask{..}) =
    let (task_type, block_id) = splitTaskLabel cpuTaskLabel
     in Just
          Shared.Cpu
            { cpu_time_s = realToFrac cpuTaskDuration
            , task_type
            , block_id
            , ..
            }
  sharedNode node (PraosNodeEvent pe) =
    case pe of
      PraosNodeEventGenerate blk ->
        let
          (endorsement, endorsements) = headAndTail $ map (Shared.Endorsement . Shared.BlockRef . T.pack . mkStringId . fst) $ blk.blockBody.endorseBlocks
         in
          Just
            Shared.RBGenerated
              { producer = node
              , block_id = (rbId blk)
              , slot = fromIntegral . fromEnum $ blockSlot blk
              , size_bytes = fromIntegral $ messageSizeBytes blk
              , endorsement = Shared.Nullable endorsement
              , endorsements
              , payload_bytes = fromIntegral $ blk.blockBody.payload
              , parent = Shared.Nullable $ do
                  h@BlockHash{} <- pure $ blockPrevHash blk
                  Just $! Shared.BlockRef{id = rbRef h}
              , ..
              }
      PraosNodeEventReceived blk ->
        Just
          Shared.RBReceived
            { sender = Nothing
            , recipient = node
            , block_id = rbId blk
            , msg_size_bytes = Nothing
            , sending_s = Nothing
            , block_ids = Nothing
            , ..
            }
      PraosNodeEventEnterState blk ->
        Just
          Shared.RBEnteredState
            { id = rbId blk
            , slot = fromIntegral . fromEnum $ blockSlot blk
            , ..
            }
      PraosNodeEventCPU _ -> error "impossible"
      _ -> Nothing
   where
    rbId blk = T.pack $ show (coerce @_ @Int (blockHash blk))
  sharedNode node (LeiosNodeEventConformance ev) = Just $ case ev of
    Slot{..} -> Shared.Slot{slot = coerce slot, ..}
    NoIBGenerated{..} -> Shared.NoIBGenerated{slot = coerce slot, ..}
    NoEBGenerated{..} -> Shared.NoEBGenerated{slot = coerce slot, ..}
    NoVTGenerated{..} -> Shared.NoVTBundleGenerated{slot = coerce slot, ..}
  sharedNode _ _ = Nothing
  headAndTail xs = case xs of
    [] -> (Nothing, Nothing)
    (x : xs') -> (Just x, guard (not . null $ xs') >> Just xs')
  blockIds xs = headAndTail $ map (T.pack . mkStringId . fst) xs
  sharedMsg :: T.Text -> T.Text -> DiffTime -> Shared.Bytes -> LeiosMessage -> Maybe Shared.Event
  sharedMsg (Just -> sender) recipient (Just . realToFrac @_ @Shared.Time -> sending_s) (Just . fromIntegral @_ @Shared.Bytes -> msg_size_bytes) = \case
    RelayIB (ProtocolMessage (SomeMessage (MsgRespondBodies xs)))
      | (Just block_id, block_ids) <- blockIds xs -> Just $ Shared.IBSent{..}
    RelayEB (ProtocolMessage (SomeMessage (MsgRespondBodies xs)))
      | (Just block_id, block_ids) <- blockIds xs -> Just $ Shared.EBSent{..}
    RelayVote (ProtocolMessage (SomeMessage (MsgRespondBodies xs)))
      | (Just block_id, block_ids) <- blockIds xs -> Just $ Shared.VTBundleSent{..}
    (PraosMsg (PraosMessage (Right (ProtocolMessage (SomeMessage (MsgBlock hash _body)))))) ->
      Just $
        Shared.RBSent{block_id = T.pack $ show hash, block_ids = Just [], ..}
    _ -> Nothing

  rbRef h = T.pack $ case h of
    GenesisHash -> "genesis"
    BlockHash x -> show (coerce x :: Int)
  sharedGenerated :: T.Text -> String -> Word64 -> LeiosEventBlock -> Shared.Event
  sharedGenerated producer (T.pack -> id) slot blk =
    case blk of
      EventIB ib ->
        Shared.IBGenerated
          { size_bytes = fromIntegral $ messageSizeBytes ib
          , payload_bytes = fromIntegral $ ib.body.size
          , rb_ref =
              Just $ rbRef (ib.header.rankingBlock)
          , pipeline = coerce $ inputBlockPipeline leios ib
          , ..
          }
      EventEB eb ->
        Shared.EBGenerated
          { bytes = fromIntegral (messageSizeBytes eb)
          , input_blocks = map (Shared.BlockRef . T.pack . mkStringId) eb.inputBlocks
          , endorser_blocks = map (Shared.BlockRef . T.pack . mkStringId) eb.endorseBlocksEarlierPipeline
          , pipeline = coerce $ endorseBlockPipeline leios eb
          , ..
          }
      EventVote vt ->
        Shared.VTBundleGenerated
          { bytes = fromIntegral (messageSizeBytes vt)
          , votes = Map.fromList $ map ((,vt.votes) . T.pack . mkStringId) vt.endorseBlocks
          , pipeline = coerce $ voteMsgPipeline leios vt
          , ..
          }
  sharedEnterState :: T.Text -> String -> Word64 -> LeiosEventBlock -> Shared.Event
  sharedEnterState node (T.pack -> id) slot blk =
    case blk of
      EventIB _ -> Shared.IBEnteredState{..}
      EventEB _ -> Shared.EBEnteredState{..}
      EventVote _ -> Shared.VTBundleEnteredState{..}

  sharedReceived :: T.Text -> String -> LeiosEventBlock -> Shared.Event
  sharedReceived recipient (T.pack -> block_id) blk =
    case blk of
      EventIB _ -> Shared.IBReceived{..}
      EventEB _ -> Shared.EBReceived{..}
      EventVote _ -> Shared.VTBundleReceived{..}
   where
    sender = Nothing
    block_ids = Nothing
    msg_size_bytes = Nothing
    sending_s = Nothing

exampleTrace1 :: LeiosTrace
exampleTrace1 = traceRelayLink1 (0.1, Just 1000000)

traceRelayLink1 ::
  (DiffTime, Maybe Bytes) ->
  LeiosTrace
traceRelayLink1 connectionOptions =
  selectTimedEvents $
    runSimTrace $ do
      traceWith tracer $
        LeiosEventSetup
          World
            { worldDimensions = (500, 500)
            , worldShape = Rectangle
            }
          ( Map.fromList
              [ (nodeA, Point 50 100)
              , (nodeB, Point 450 100)
              ]
          )
          ( Map.fromList
              [ (nodeA, StakeFraction 0.5)
              , (nodeB, StakeFraction 0.5)
              ]
          )
          ( Set.fromList
              [(nodeA :<- nodeB), (nodeB :<- nodeA)]
          )
      slotConfig <- slotConfigFromNow
      let praosConfig@PraosConfig{configureConnection} = defaultPraosConfig
      let leiosConfig =
            LeiosConfig
              { praos = praosConfig
              , -- measured in slots, also stage length in Short leios.
                sliceLength = 5 -- matching the interval between RBs
                -- expected InputBlock generation rate per slot.
              , inputBlockFrequencyPerSlot = 5
              , -- expected EndorseBlock generation rate per stage, at most one per _node_ in each (pipeline, stage).
                endorseBlockFrequencyPerStage = 4
              , cleanupPolicies = def
              , variant = Short
              , headerDiffusionTime = 1
              , pipelinesToReferenceFromEB = 0
              , activeVotingStageLength = 1
              , pipeline = SingSingleVote
              , voteSendStage = Vote
              , votingFrequencyPerStage = 4
              , votesForCertificate = 1 -- just two nodes available to vote!
              , maxEndorseBlockAgeSlots = 50
              , maxEndorseBlockAgeForRelaySlots = 50
              , sizes -- TODO: realistic sizes
                =
                  SizesConfig
                    { inputBlockHeader = kilobytes 1
                    , inputBlockBodyAvgSize = kilobytes 95
                    , inputBlockBodyMaxSize = kilobytes 100
                    , endorseBlock = \eb -> coerce (length eb.inputBlocks) * 32 + 32 + 128
                    , voteMsg = \v -> fromIntegral v.votes * 32 + 32 + 128
                    , certificate = const (50 * 1024)
                    , rankingBlockLegacyPraosPayloadAvgSize = 0
                    }
              , delays =
                  LeiosDelays
                    { inputBlockHeaderValidation = const 0.005
                    , -- \^ vrf and signature
                      inputBlockValidation = const 0.1
                    , -- \^ hash matching and payload validation (incl. tx scripts)
                      endorseBlockValidation = const 0.005
                    , voteMsgValidation = const 0.005
                    , certificateGeneration = const 0.050
                    , inputBlockGeneration = const 0
                    , endorseBlockGeneration = const 0
                    , voteMsgGeneration = const (const 0)
                    , certificateValidation = const 0
                    }
              , ibDiffusion = RelayDiffusionConfig FreshestFirst 100 100 1
              , ebDiffusion = RelayDiffusionConfig PeerOrder 100 100 1
              , voteDiffusion = RelayDiffusionConfig PeerOrder 100 100 1
              , relayStrategy = RequestFromAll
              }
      let leiosNodeConfig nodeId@(NodeId i) =
            LeiosNodeConfig
              { leios = leiosConfig
              , slotConfig
              , stake = StakeFraction 0.5 -- just two nodes!
              , rng = mkStdGen i
              , -- \^ for block generation
                baseChain = Genesis
              , -- \^ overall size of txs to include in IBs
                processingQueueBound = 100
              , processingCores = Infinite
              , blockGeneration = Honest
              , conformanceEvents = False
              , ..
              }
      (pA, cB) <- newConnectionBundle (leiosTracer nodeA nodeB) (uncurry configureConnection connectionOptions)
      (cA, pB) <- newConnectionBundle (leiosTracer nodeA nodeB) (uncurry configureConnection connectionOptions)
      threads <-
        (++)
          <$> leiosNode (nodeTracer nodeA) (leiosNodeConfig nodeA) [pA] [cA]
          <*> leiosNode (nodeTracer nodeB) (leiosNodeConfig nodeB) [pB] [cB]
      mapM_ forkIO threads
      forever $ threadDelay 1000
 where
  (nodeA, nodeB) = (NodeId 0, NodeId 1)

  tracer :: Tracer (IOSim s) LeiosEvent
  tracer = simTracer

  nodeTracer :: NodeId -> Tracer (IOSim s) LeiosNodeEvent
  nodeTracer n =
    contramap (LeiosEventNode . LabelNode n) tracer

  leiosTracer ::
    NodeId ->
    NodeId ->
    Tracer (IOSim s) (LabelTcpDir (TcpEvent LeiosMessage))
  leiosTracer nfrom nto =
    contramap (LeiosEventTcp . labelDirToLabelLink nfrom nto) tracer
