{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module LeiosProtocol.Short.Sim where

import Chan.Driver
import Chan.Mux
import Chan.TCP
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
import Data.Coerce
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as T
import GHC.Records
import LeiosProtocol.Common hiding (Point)
import LeiosProtocol.Relay (Message (..), RelayMessage, relayMessageLabel)
import LeiosProtocol.Short
import LeiosProtocol.Short.Node
import ModelTCP
import Network.TypedProtocol
import PraosProtocol.BlockFetch (Message (..))
import PraosProtocol.PraosNode (PraosMessage (..), praosMessageLabel)
import SimTCPLinks
import SimTypes
import System.Random (mkStdGen)

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

logLeiosEvent :: Map NodeId T.Text -> Bool -> LeiosEvent -> Maybe Encoding
logLeiosEvent nodeNames emitControl e = case e of
  LeiosEventSetup{} -> Nothing
  LeiosEventNode (LabelNode nid x) -> do
    pairs <$> logNode nid x
  LeiosEventTcp (LabelLink from to (TcpSendMsg msg forecast _)) -> do
    ps <- logMsg msg
    pure $
      pairs $
        "tag" .= asString "Sent"
          <> "sender" .= from
          <> "receipient" .= to
          <> "msg_size_bytes" .= fromBytes (messageSizeBytes msg)
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
  logMsg (RelayIB msg) = (ibKind <>) <$> logRelay msg
  logMsg (RelayEB msg) = (ebKind <>) <$> logRelay msg
  logMsg (RelayVote msg) = (vtKind <>) <$> logRelay msg
  logMsg (PraosMsg (PraosMessage (Right (ProtocolMessage (SomeMessage (MsgBlock hash _body)))))) =
    Just $ rbKind <> "id" .= show (coerce @_ @Int hash)
  logMsg (PraosMsg msg)
    | emitControl = Just $ mconcat ["id" .= asString "control", "label" .= praosMessageLabel msg]
    | otherwise = Nothing
  logRelay :: (HasField "node" id NodeId, HasField "num" id Int) => RelayMessage id h b -> Maybe Series
  logRelay (ProtocolMessage (SomeMessage (MsgRespondBodies xs))) =
    Just $ "ids" .= map (mkStringId . fst) xs
  logRelay (ProtocolMessage (SomeMessage msg))
    | emitControl = Just $ "id" .= asString "control" <> "label" .= relayMessageLabel msg
    | otherwise = Nothing
  asString x = x :: String

messages :: [(a, LeiosEvent)] -> [(a, LabelLink LeiosMessage)]
messages trace = [(t, LabelLink x y msg) | (t, LeiosEventTcp (LabelLink x y (TcpSendMsg msg _ _))) <- trace]

exampleTrace1 :: LeiosTrace
exampleTrace1 = traceRelayLink1 $ mkTcpConnProps 0.1 1000000

traceRelayLink1 ::
  TcpConnProps ->
  LeiosTrace
traceRelayLink1 tcpprops =
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
      let praosConfig = defaultPraosConfig
      let leiosConfig =
            LeiosConfig
              { praos = praosConfig
              , sliceLength = 5 -- matching the interval between RBs
              , -- \^ measured in slots, also stage length in Short leios.
                inputBlockFrequencyPerSlot = 5
              , -- \^ expected InputBlock generation rate per slot.
                endorseBlockFrequencyPerStage = 4
              , -- \^ expected EndorseBlock generation rate per stage, at most one per _node_ in each (pipeline, stage).
                activeVotingStageLength = 1
              , pipeline = SingSingleVote
              , voteSendStage = Vote
              , votingFrequencyPerStage = 4
              , votesForCertificate = 1 -- just two nodes available to vote!
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

      (pA, cB) <- newConnectionBundleTCP (leiosTracer nodeA nodeB) tcpprops
      (cA, pB) <- newConnectionBundleTCP (leiosTracer nodeA nodeB) tcpprops
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
