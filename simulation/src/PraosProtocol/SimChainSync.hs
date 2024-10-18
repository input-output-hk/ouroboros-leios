{-# LANGUAGE FlexibleInstances #-}

module PraosProtocol.SimChainSync where

import Chan
import ChanDriver
import ChanTCP
import PraosProtocol.ChainSync
import PraosProtocol.Types hiding (Point)

import Control.Concurrent.Class.MonadSTM (MonadSTM (atomically, newTVar))
import Control.Monad.Class.MonadAsync (
  Concurrently (Concurrently, runConcurrently),
  MonadAsync (concurrently_),
 )
import Control.Monad.Class.MonadTime.SI (
  DiffTime,
  MonadTime (..),
  NominalDiffTime,
  Time,
  UTCTime,
  addUTCTime,
  diffUTCTime,
 )
import Control.Monad.Class.MonadTimer (MonadDelay)
import Control.Monad.IOSim as IOSim (IOSim, runSimTrace)
import Control.Tracer as Tracer (
  Contravariant (contramap),
  Tracer,
  traceWith,
 )
import qualified Data.ByteString as BS
import Data.Foldable (traverse_)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Network.TypedProtocol
import Ouroboros.Network.Mock.ConcreteBlock (mkChainSimple)
import SimTCPLinks
import SimTypes
import System.Random (StdGen, uniform, uniformR)

instance MessageSize (Message ChainSyncState st st') where
  messageSizeBytes msg =
    1000
      * case msg of
        MsgRequestNext -> 1
        MsgAwaitReply -> 1
        MsgRollForward_StCanAwait hdr tip -> 2 * 256
        MsgRollBackward_StCanAwait pt tip -> 2 * 256
        MsgRollForward_StMustReply hdr tip -> 2 * 256
        MsgRollBackward_StMustReply pt tip -> 2 * 256
        MsgFindIntersect pts -> fromIntegral (Prelude.length pts) * 256
        MsgIntersectFound pt tip -> 2 * 256
        MsgIntersectNotFound tip -> 256
        MsgDone -> 1

type ChainSyncTrace = [(Time, ChainSyncEvent)]

data ChainSyncEvent
  = -- | Declare the nodes and links
    ChainSyncEventSetup
      !WorldShape
      !(Map NodeId Point) -- nodes and locations
      !(Set (NodeId, NodeId)) -- links between nodes
  | -- | An event at a node
    ChainSyncEventNode (LabelNode ChainSyncNodeEvent)
  | -- | An event on a tcp link between two nodes
    ChainSyncEventTcp (LabelLink (TcpEvent (ProtocolMessage ChainSyncState)))
  deriving (Show)
type ChainSyncMessage = ProtocolMessage ChainSyncState
data ChainSyncNodeEvent = ChainSyncNodeEvent
  -- = RelayNodeEventGenerate blk

  deriving
    ( -- | RelayNodeEventEnterQueue blk
      -- | RelayNodeEventEnterBuffer blk
      -- | RelayNodeEventRemove blk
      Show
    )

exampleTrace1 = traceRelayLink1 $ mkTcpConnProps 0.1 1000000

traceRelayLink1 ::
  TcpConnProps ->
  --- PacketGenerationPattern ->
  ChainSyncTrace
traceRelayLink1 tcpprops =
  selectTimedEvents $
    runSimTrace $ do
      traceWith tracer $
        ChainSyncEventSetup
          WorldShape
            { worldDimensions = (500, 500)
            , worldIsCylinder = False
            }
          ( Map.fromList
              [ (NodeId 0, Point 50 100)
              , (NodeId 1, Point 450 100)
              ]
          )
          ( Set.fromList
              [(NodeId 0, NodeId 1), (NodeId 1, NodeId 0)]
          )
      (inChan, outChan) <- newConnectionTCP (linkTracer na nb) tcpprops
      concurrently_
        (consumerNode inChan)
        (producerNode outChan)
      return ()
 where
  consumerNode chan = do
    hchainVar <- atomically $ newTVar Genesis
    runPeerWithDriver (chanDriver decideChainSyncState chan) (chainConsumer hchainVar)
  producerNode chan = do
    let chain = mkChainSimple $ replicate 10 (BlockBody $ BS.replicate 100 0)
    let (cps, fId) = initFollower GenesisPoint $ initChainProducerState chain
    cpsVar <- atomically $ newTVar cps
    runPeerWithDriver (chanDriver decideChainSyncState chan) (chainProducer fId cpsVar)
  [na, nb] = map NodeId [0, 1]
  -- configNode0 = RelayNodeConfig processingDelay generationPattern
  -- configNode1 = RelayNodeConfig processingDelay NoPacketGeneration
  processingDelay = const 0.1 -- 100 ms
  tracer :: Tracer (IOSim s) ChainSyncEvent
  tracer = simTracer

  nodeTracer :: NodeId -> Tracer (IOSim s) (ChainSyncNodeEvent)
  nodeTracer n =
    contramap (ChainSyncEventNode . LabelNode n) tracer

  linkTracer ::
    NodeId ->
    NodeId ->
    Tracer
      (IOSim s)
      (LabelTcpDir (TcpEvent (ProtocolMessage ChainSyncState)))
  linkTracer nfrom nto =
    contramap (ChainSyncEventTcp . labelDirToLabelLink nfrom nto) tracer
