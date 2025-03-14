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
import Control.Monad (forever)
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
import PraosProtocol.BlockFetch (Message (..))
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
      !(Set (NodeId, NodeId)) -- links between nodes
  | -- | An event at a node
    LeiosEventNode (LabelNode LeiosNodeEvent)
  | -- | An event on a tcp link between two nodes
    LeiosEventTcp (LabelLink (TcpEvent LeiosMessage))
  deriving (Show)

logLeiosTraceEvent :: Map NodeId T.Text -> Bool -> DiffTime -> LeiosEvent -> Maybe Encoding
logLeiosTraceEvent m emitControl t e = do
  x <- logLeiosEvent m emitControl e
  pure $ (pairs $ "time_s" .= t <> pair "event" x)

logLeiosEvent :: Map NodeId T.Text -> Bool -> LeiosEvent -> Maybe Encoding
logLeiosEvent nodeNames emitControl e = case e of
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
          <> "fragments" .= length fcs
          <> "forecast" .= forecast
          -- <> "forecasts" .= fcs
          <> "msg_size_bytes" .= fromBytes (messageSizeBytes msg)
          <> "time_to_received_s" .= (coerce forecast.msgRecvTrailingEdge - coerce forecast.msgSendLeadingEdge :: DiffTime)
          <> "sending_s" .= (coerce forecast.msgSendTrailingEdge - coerce forecast.msgSendLeadingEdge :: DiffTime)
          <> ps
 where
  node nid = "node" .= nid <> "node_name" .= nodeNames Map.! nid
  ibKind = "kind" .= asString "IB"
  ebKind = "kind" .= asString "EB"
  vtKind = "kind" .= asString "VT"
  rbKind = "kind" .= asString "RB"
  cpuTag = "tag" .= asString "Cpu"
  logNode nid (PraosNodeEvent x) = logPraos nid x
  logNode nid (LeiosNodeEventCPU CPUTask{..}) =
    Just $
      mconcat
        [ cpuTag
        , node nid
        , "duration_s" .= cpuTaskDuration
        , "task_label" .= cpuTaskLabel
        ]
  logNode nid (LeiosNodeEvent blkE blk) = Just $ "tag" .= tag <> kindAndId <> extra <> node nid
   where
    extra
      | Generate <- blkE = case blk of
          EventIB ib ->
            mconcat
              [ "slot" .= ib.header.slot
              , "payload_bytes" .= fromBytes ib.body.size
              , "size_bytes" .= fromBytes (messageSizeBytes ib)
              , "rb_ref" .= case (ib.header.rankingBlock) of
                  GenesisHash -> "genesis"
                  BlockHash x -> show (coerce x :: Int)
              ]
          EventEB eb ->
            mconcat
              [ "slot" .= eb.slot
              , "input_blocks" .= map mkStringId eb.inputBlocks
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
  logPraos nid (PraosNodeEventGenerate blk@(Block h b)) =
    Just $
      mconcat
        [ "tag" .= asString "generated"
        , rbKind
        , "id" .= show (coerce @_ @Int (blockHash blk))
        , "size_bytes" .= fromBytes (messageSizeBytes h + messageSizeBytes b)
        , node nid
        , "endorsed" .= map fst b.endorseBlocks
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
  logPraos _ (PraosNodeEventNewTip _chain) = Nothing
  logMsg :: LeiosMessage -> Maybe Series
  logMsg (RelayIB msg) = (ibKind <>) <$> logRelay (.id) msg
  logMsg (RelayEB msg) = (ebKind <>) <$> logRelay (.id) msg
  logMsg (RelayVote msg) = (vtKind <>) <$> logRelay (.id) msg
  logMsg (PraosMsg (PraosMessage (Right (ProtocolMessage (SomeMessage (MsgBlock hash _body)))))) =
    Just $ rbKind <> "id" .= show (coerce @_ @Int hash)
  logMsg (PraosMsg msg)
    | emitControl = Just $ mconcat ["id" .= asString "control", "label" .= praosMessageLabel msg]
    | otherwise = Nothing
  logRelay :: (HasField "node" id NodeId, HasField "num" id Int) => (h -> id) -> RelayMessage id h b -> Maybe Series
  logRelay _getId (ProtocolMessage (SomeMessage (MsgRespondBodies xs))) =
    Just $ "ids" .= map (mkStringId . fst) xs <> "msg_label" .= asString "respond-bodies"
  logRelay _getId (ProtocolMessage (SomeMessage (MsgRequestBodies xs))) =
    Just $
      "ids" .= map mkStringId xs
        <> "msg_label" .= asString "request-bodies"
  logRelay getId (ProtocolMessage (SomeMessage (MsgRespondHeaders xs))) =
    Just $
      "ids" .= map (mkStringId . getId) (toList xs)
        <> "msg_label" .= asString "respond-headers"
  logRelay _getId (ProtocolMessage (SomeMessage (MsgRequestHeaders _ ws we))) =
    Just $
      "shrink" .= ws.value
        <> "expand" .= we.value
        <> "msg_label" .= asString "request-headers"
  logRelay _ (ProtocolMessage (SomeMessage msg))
    | emitControl = Just $ "id" .= asString "control" <> "label" .= relayMessageLabel msg
    | otherwise = Nothing
  asString x = x :: String

messages :: [(a, LeiosEvent)] -> [(a, LabelLink LeiosMessage)]
messages trace = [(t, LabelLink x y msg) | (t, LeiosEventTcp (LabelLink x y (TcpSendMsg msg _ _))) <- trace]
sharedTraceEvent :: Map NodeId T.Text -> DiffTime -> LeiosEvent -> Maybe Shared.TraceEvent
sharedTraceEvent m t e = Shared.TraceEvent (realToFrac t) <$> sharedEvent m e
sharedEvent :: Map NodeId T.Text -> LeiosEvent -> Maybe Shared.Event
sharedEvent nodeNames e = case e of
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
  sharedNode node (LeiosNodeEvent Generate blk) = Just $ sharedGenerated node (blkId blk) (blkSlot blk) blk
  sharedNode node (LeiosNodeEvent Received blk) = Just $ sharedReceived node (blkId blk) blk
  sharedNode node (LeiosNodeEvent EnterState blk) = Just $ sharedEnterState node (blkId blk) (blkSlot blk) blk
  sharedNode node (LeiosNodeEventCPU CPUTask{..}) =
    Just
      Shared.Cpu
        { cpu_time_s = realToFrac cpuTaskDuration
        , task_label = cpuTaskLabel
        , ..
        }
  sharedNode node (PraosNodeEvent pe) =
    case pe of
      PraosNodeEventGenerate blk ->
        Just
          Shared.RBGenerated
            { producer = node
            , block_id = Just (rbId blk)
            , vrf = Nothing
            , slot = fromIntegral . fromEnum $ blockSlot blk
            , size_bytes = Nothing
            , endorsement = Nothing
            , endorsements = Just . map (Shared.Endorsement . Shared.BlockRef . T.pack . mkStringId . fst) $ blk.blockBody.endorseBlocks
            , payload_bytes = Just . fromIntegral $ blk.blockBody.payload
            , ..
            }
      PraosNodeEventReceived blk ->
        Just
          Shared.RBReceived
            { sender = Nothing
            , recipient = node
            , block_id = Just (rbId blk)
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
  sharedNode _ _ = Nothing
  blockIds xs = case map (T.pack . mkStringId . fst) xs of
    [] -> (Nothing, Nothing)
    (y : ys) -> (Just y, Just ys)
  sharedMsg :: T.Text -> T.Text -> DiffTime -> Shared.Bytes -> LeiosMessage -> Maybe Shared.Event
  sharedMsg (Just -> sender) recipient (Just . realToFrac @_ @Shared.Time -> sending_s) (Just . fromIntegral @_ @Shared.Bytes -> msg_size_bytes) = \case
    RelayIB (ProtocolMessage (SomeMessage (MsgRespondBodies xs)))
      | (block_id, block_ids) <- blockIds xs -> Just $ Shared.IBSent{..}
    RelayEB (ProtocolMessage (SomeMessage (MsgRespondBodies xs)))
      | (block_id, block_ids) <- blockIds xs -> Just $ Shared.EBSent{..}
    RelayVote (ProtocolMessage (SomeMessage (MsgRespondBodies xs)))
      | (block_id, block_ids) <- blockIds xs -> Just $ Shared.VTBundleSent{..}
    (PraosMsg (PraosMessage (Right (ProtocolMessage (SomeMessage (MsgBlock hash _body)))))) ->
      Just $
        Shared.RBSent{block_id = Just $ T.pack $ show hash, block_ids = Just [], ..}
    _ -> Nothing

  sharedGenerated :: T.Text -> String -> Word64 -> LeiosEventBlock -> Shared.Event
  sharedGenerated producer (T.pack -> id) slot blk =
    case blk of
      EventIB ib ->
        Shared.IBGenerated
          { size_bytes = Just (fromIntegral $ messageSizeBytes ib)
          , payload_bytes = Just (fromIntegral $ ib.body.size)
          , rb_ref =
              Just $
                T.pack
                  ( case (ib.header.rankingBlock) of
                      GenesisHash -> "genesis"
                      BlockHash x -> show (coerce x :: Int)
                  )
          , ..
          }
      EventEB eb -> Shared.EBGenerated{bytes = fromIntegral (messageSizeBytes eb), input_blocks = map (Shared.BlockRef . T.pack . mkStringId) eb.inputBlocks, ..}
      EventVote vt -> Shared.VTBundleGenerated{bytes = fromIntegral (messageSizeBytes vt), votes = Map.fromList $ map ((,vt.votes) . T.pack . mkStringId) vt.endorseBlocks, ..}
  sharedEnterState :: T.Text -> String -> Word64 -> LeiosEventBlock -> Shared.Event
  sharedEnterState node (T.pack -> id) slot blk =
    case blk of
      EventIB _ -> Shared.IBEnteredState{..}
      EventEB _ -> Shared.EBEnteredState{..}
      EventVote _ -> Shared.VTBundleEnteredState{..}

  sharedReceived :: T.Text -> String -> LeiosEventBlock -> Shared.Event
  sharedReceived recipient (Just . T.pack -> block_id) blk =
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
              [(nodeA, nodeB), (nodeB, nodeA)]
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
              , activeVotingStageLength = 1
              , pipeline = SingSingleVote
              , voteSendStage = Vote
              , votingFrequencyPerStage = 4
              , votesForCertificate = 1 -- just two nodes available to vote!
              , maxEndorseBlockAgeSlots = 50
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
